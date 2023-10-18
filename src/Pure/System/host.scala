/*  Title:      Pure/System/host.scala
    Author:     Makarius

Information about compute hosts, including NUMA: Non-Uniform Memory Access of
separate CPU nodes.

See also https://www.open-mpi.org/projects/hwloc --- notably "lstopo" or
"hwloc-ls" (e.g. via Ubuntu package "hwloc").
*/

package isabelle


object Host {

  object Range {
    val Single = """^(\d+)$""".r
    val Multiple = """^(\d+)-(\d+)$""".r

    def apply(range: List[Int]): String =
      range match {
        case Nil => ""
        case x :: xs =>
          def elem(start: Int, stop: Int): String =
            if (start == stop) start.toString else start.toString + "-" + stop.toString

          val (elems, (r0, rn)) =
            xs.foldLeft((List.empty[String], (x, x))) {
              case ((rs, (r0, rn)), x) =>
                if (rn + 1 == x) (rs, (r0, x)) else (rs :+ elem(r0, rn), (x, x))
            }

          (elems :+ elem(r0, rn)).mkString(",")
      }

    def unapply(s: String): Option[List[Int]] =
      space_explode(',', s).foldRight(Option(List.empty[Int])) {
        case (Single(Value.Int(i)), Some(elems)) => Some(i :: elems)
        case (Multiple(Value.Int(i), Value.Int(j)), Some(elems)) => Some((i to j).toList ::: elems)
        case _ => None
      }

    def from(s: String) =
      s match {
        case Range(r) => r
        case _ => Nil
      }
  }


  /* process policy via numactl tool */

  def numactl(node: Int): String = "numactl -m" + node + " -N" + node
  def numactl_ok(node: Int): Boolean = Isabelle_System.bash(numactl(node) + " true").ok

  def process_policy_options(options: Options, numa_node: Option[Int]): Options =
    numa_node match {
      case None => options
      case Some(node) =>
        options.string("process_policy") = if (numactl_ok(node)) numactl(node) else ""
    }


  /* allocated resources */

  object Node_Info { def none: Node_Info = Node_Info("", None) }

  sealed case class Node_Info(hostname: String, numa_node: Option[Int]) {
    override def toString: String =
      hostname + if_proper(numa_node, "/" + numa_node.get.toString)
  }


  /* statically available resources */

  private val numa_info_linux: Path = Path.explode("/sys/devices/system/node/online")

  def parse_numa_info(numa_info: String): List[Int] =
    numa_info match {
      case Range(nodes) => nodes
      case s => error("Cannot parse CPU NUMA node specification: " + quote(s))
    }

  def numa_nodes(enabled: Boolean = true, ssh: SSH.System = SSH.Local): List[Int] = {
    val numa_info = if (ssh.isabelle_platform.is_linux) Some(numa_info_linux) else None
    for {
      path <- numa_info.toList
      if enabled && ssh.is_file(path)
      n <- parse_numa_info(ssh.read(path).trim)
    } yield n
  }

  def numa_node0(): Option[Int] =
    try {
      numa_nodes() match {
        case ns if ns.length >= 2 && numactl_ok(ns.head) => Some(ns.head)
        case _ => None
      }
    }
    catch { case ERROR(_) => None }

  def num_cpus(): Int = Runtime.getRuntime.availableProcessors

  object Info {
    def gather(hostname: String, ssh: SSH.System = SSH.Local): Info =
      Info(hostname, numa_nodes(ssh = ssh), num_cpus())
  }

  sealed case class Info(
    hostname: String,
    numa_nodes: List[Int],
    num_cpus: Int)


  /* shuffling of NUMA nodes */

  def numa_check(progress: Progress, enabled: Boolean): Boolean = {
    def warning =
      numa_nodes() match {
        case ns if ns.length < 2 => Some("no NUMA nodes available")
        case ns if !numactl_ok(ns.head) => Some("bad numactl tool")
        case _ => None
      }

    enabled &&
      (warning match {
        case Some(s) =>
          progress.echo_warning("Shuffling of NUMA CPU nodes is disabled: " + s)
          false
        case _ => true
      })
  }


  /* SQL data model */

  object private_data extends SQL.Data("isabelle_host") {
    val database: Path = Path.explode("$ISABELLE_HOME_USER/host.db")

    override lazy val tables = SQL.Tables(Node_Info.table, Info.table)

    object Node_Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_next = SQL.Column.int("numa_next")

      val table = make_table(List(hostname, numa_next), name = "node_info")
    }

    def read_numa_next(db: SQL.Database, hostname: String): Int =
      db.execute_query_statementO[Int](
        Node_Info.table.select(List(Node_Info.numa_next),
          sql = Node_Info.hostname.where_equal(hostname)),
        res => res.int(Node_Info.numa_next)
      ).getOrElse(0)

    def write_numa_next(db: SQL.Database, hostname: String, numa_next: Int): Unit = {
      db.execute_statement(Node_Info.table.delete(sql = Node_Info.hostname.where_equal(hostname)))
      db.execute_statement(Node_Info.table.insert(), body =
        { stmt =>
          stmt.string(1) = hostname
          stmt.int(2) = numa_next
        })
    }

    object Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_info = SQL.Column.string("numa_info")
      val num_cpus = SQL.Column.int("num_cpus")

      val table =
        make_table(List(hostname, numa_info, num_cpus), name = "info")
    }

    def write_info(db: SQL.Database, info: Info): Unit = {
      db.execute_statement(Info.table.delete(sql = Info.hostname.where_equal(info.hostname)))
      db.execute_statement(Info.table.insert(), body =
        { stmt =>
          stmt.string(1) = info.hostname
          stmt.string(2) = info.numa_nodes.mkString(",")
          stmt.int(3) = info.num_cpus
        })
    }

    def read_info(db: SQL.Database, hostname: String): Option[Host.Info] =
      db.execute_query_statementO[Host.Info](
        Info.table.select(Info.table.columns.tail, sql = Info.hostname.where_equal(hostname)),
        { res =>
          val numa_info = res.string(Info.numa_info)
          val num_cpus = res.int(Info.num_cpus)

          Host.Info(hostname, parse_numa_info(numa_info), num_cpus)
        })
  }

  def next_numa_node(
    db: SQL.Database,
    hostname: String,
    available_nodes: List[Int],
    used_nodes: => Set[Int]
  ): Option[Int] =
    if (available_nodes.isEmpty) None
    else {
      val available = available_nodes.zipWithIndex
      val used = used_nodes
      private_data.transaction_lock(db, create = true, label = "Host.next_numa_node") {
        val numa_next = private_data.read_numa_next(db, hostname)
        val numa_index = available.collectFirst({ case (n, i) if n == numa_next => i }).getOrElse(0)
        val candidates = available.drop(numa_index) ::: available.take(numa_index)
        val (n, i) =
          candidates.find({ case (n, i) => i == numa_index && !used(n) }) orElse
          candidates.find({ case (n, _) => !used(n) }) getOrElse candidates.head

        val numa_next1 = available_nodes((i + 1) % available_nodes.length)
        if (numa_next != numa_next1) private_data.write_numa_next(db, hostname, numa_next1)

        Some(n)
      }
    }

  def write_info(db: SQL.Database, info: Info): Unit =
    private_data.transaction_lock(db, create = true, label = "Host.write_info") {
      private_data.write_info(db, info)
    }
  def read_info(db: SQL.Database, hostname: String): Option[Host.Info] =
    private_data.transaction_lock(db, create = true, label = "Host.read_info") {
      private_data.read_info(db, hostname)
    }
}
