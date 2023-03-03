/*  Title:      Pure/System/host.scala
    Author:     Makarius

Information about compute hosts, including NUMA: Non-Uniform Memory Access of
separate CPU nodes.

See also https://www.open-mpi.org/projects/hwloc --- notably "lstopo" or
"hwloc-ls" (e.g. via Ubuntu package "hwloc").
*/

package isabelle


object Host {
  /* allocated resources */

  object Node_Info { def none: Node_Info = Node_Info("", None) }

  sealed case class Node_Info(hostname: String, numa_node: Option[Int])


  /* available NUMA nodes */

  private val numa_info_linux: Path = Path.explode("/sys/devices/system/node/online")

  def numa_nodes(enabled: Boolean = true, ssh: SSH.System = SSH.Local): List[Int] = {
    val Single = """^(\d+)$""".r
    val Multiple = """^(\d+)-(\d+)$""".r

    def parse(s: String): List[Int] =
      s match {
        case Single(Value.Int(i)) => List(i)
        case Multiple(Value.Int(i), Value.Int(j)) => (i to j).toList
        case _ => error("Cannot parse CPU NUMA node specification: " + quote(s))
      }

    val numa_info = if (ssh.isabelle_platform.is_linux) Some(numa_info_linux) else None
    for {
      path <- numa_info.toList
      if enabled && ssh.is_file(path)
      s <- space_explode(',', ssh.read(path).trim)
      n <- parse(s)
    } yield n
  }


  /* process policy via numactl tool */

  def numactl(node: Int): String = "numactl -m" + node + " -N" + node
  def numactl_ok(node: Int): Boolean = Isabelle_System.bash(numactl(node) + " true").ok

  def process_policy(node: Int): String = if (numactl_ok(node)) numactl(node) else ""

  def process_policy_options(options: Options, numa_node: Option[Int]): Options =
    numa_node match {
      case None => options
      case Some(n) => options.string("process_policy") = process_policy(n)
    }

  def perhaps_process_policy_options(options: Options): Options = {
    val numa_node =
      try {
        numa_nodes() match {
          case ns if ns.length >= 2 && numactl_ok(ns.head) => Some(ns.head)
          case _ => None
        }
      }
      catch { case ERROR(_) => None }
    process_policy_options(options, numa_node)
  }


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

  object Data {
    def make_table(name: String, columns: List[SQL.Column], body: String = ""): SQL.Table =
      SQL.Table("isabelle_host" + if_proper(name, "_" + name), columns, body = body)

    object Node_Info {
      val hostname = SQL.Column.string("hostname").make_primary_key
      val numa_index = SQL.Column.int("numa_index")

      val table = make_table("node_info", List(hostname, numa_index))
    }

    def read_numa_index(db: SQL.Database, hostname: String): Int =
      db.using_statement(
        Node_Info.table.select(List(Node_Info.numa_index),
          sql = Node_Info.hostname.where_equal(hostname))
      )(stmt => stmt.execute_query().iterator(_.int(Node_Info.numa_index)).nextOption.getOrElse(0))

    def update_numa_index(db: SQL.Database, hostname: String, numa_index: Int): Boolean =
      if (read_numa_index(db, hostname) != numa_index) {
        db.using_statement(
          Node_Info.table.delete(sql = Node_Info.hostname.where_equal(hostname))
        )(_.execute())
        db.using_statement(Node_Info.table.insert()) { stmt =>
          stmt.string(1) = hostname
          stmt.int(2) = numa_index
          stmt.execute()
        }
        true
      }
      else false
  }
}