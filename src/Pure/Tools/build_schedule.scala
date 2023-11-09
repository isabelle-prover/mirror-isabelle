/*  Title:      Pure/Tools/build_schedule.scala
    Author:     Fabian Huch, TU Muenchen

Build schedule generated by Heuristic methods, allowing for more efficient builds.
 */
package isabelle


import Host.Node_Info
import scala.annotation.tailrec


object Build_Schedule {
  val engine_name = "build_schedule"

  object Config {
    def from_job(job: Build_Process.Job): Config = Config(job.name, job.node_info)
  }

  case class Config(job_name: String, node_info: Node_Info) {
    def job_of(start_time: Time): Build_Process.Job =
      Build_Process.Job(job_name, "", "", node_info, Date(start_time), None)
  }

  /* organized historic timing information (extracted from build logs) */

  case class Timing_Entry(job_name: String, hostname: String, threads: Int, elapsed: Time)

  class Timing_Data private(data: List[Timing_Entry], val host_infos: Host_Infos) {
    require(data.nonEmpty)

    def is_empty = data.isEmpty
    def size = data.length

    private lazy val by_job =
      data.groupBy(_.job_name).view.mapValues(new Timing_Data(_, host_infos)).toMap
    private lazy val by_threads =
      data.groupBy(_.threads).view.mapValues(new Timing_Data(_, host_infos)).toMap
    private lazy val by_hostname =
      data.groupBy(_.hostname).view.mapValues(new Timing_Data(_, host_infos)).toMap

    def mean_time: Time = Timing_Data.mean_time(data.map(_.elapsed))

    private def best_entry: Timing_Entry = data.minBy(_.elapsed.ms)

    def best_threads(job_name: String): Option[Int] = by_job.get(job_name).map(_.best_entry.threads)

    def best_time(job_name: String): Time =
      by_job.get(job_name).map(_.best_entry.elapsed).getOrElse(
        estimate_config(Config(job_name, Node_Info(best_entry.hostname, None, Nil))))

    private def hostname_factor(from: String, to: String): Double =
      host_infos.host_factor(host_infos.the_host(from), host_infos.the_host(to))

    def approximate_threads(threads: Int): Option[Time] = {
      val approximations =
        by_job.values.filter(_.size > 1).map { data =>
          val (ref_hostname, x0) =
            data.by_hostname.toList.flatMap((hostname, data) =>
              data.by_threads.keys.map(hostname -> _)).minBy((_, n) => Math.abs(n - threads))

          def unify_hosts(data: Timing_Data): List[Time] =
            data.by_hostname.toList.map((hostname, data) =>
              data.mean_time.scale(hostname_factor(hostname, ref_hostname)))

          val entries =
            data.by_threads.toList.map((threads, data) =>
              threads -> Timing_Data.median_time(unify_hosts(data)))

          val y0 = data.by_hostname(ref_hostname).by_threads(x0).mean_time
          val (x1, y1_data) =
            data.by_hostname(ref_hostname).by_threads.toList.minBy((n, _) => Math.abs(n - threads))
          val y1 = y1_data.mean_time

          val a = (y1.ms - y0.ms).toDouble / (x1 - x0)
          val b = y0.ms - a * x0
          Time.ms((a * threads + b).toLong)
        }
      if (approximations.isEmpty) None else Some(Timing_Data.mean_time(approximations))
    }

    def threads_factor(divided: Int, divisor: Int): Double =
      (approximate_threads(divided), approximate_threads(divisor)) match {
        case (Some(dividend), Some(divisor)) => dividend.ms.toDouble / divisor.ms
        case _ => divided.toDouble / divisor
      }

    def estimate_config(config: Config): Time =
      by_job.get(config.job_name) match {
        case None => mean_time
        case Some(data) =>
          val hostname = config.node_info.hostname
          val threads = host_infos.num_threads(config.node_info)
          data.by_threads.get(threads) match {
            case None => // interpolate threads
              data.by_hostname.get(hostname).flatMap(
                _.approximate_threads(threads)).getOrElse {
                  // per machine, try to approximate config for threads
                  val approximated =
                    data.by_hostname.toList.flatMap((hostname1, data) =>
                      data.approximate_threads(threads).map(time =>
                        time.scale(hostname_factor(hostname1, hostname))))

                  if (approximated.nonEmpty) Timing_Data.mean_time(approximated)
                  else {
                    // no machine where config can be approximated
                    data.approximate_threads(threads).getOrElse {
                      // only single data point, use global curve to approximate
                      val global_factor = threads_factor(data.by_threads.keys.head, threads)
                      data.by_threads.values.head.mean_time.scale(global_factor)
                    }
                  }
                }

            case Some(data) => // time for job/thread exists, interpolate machine
              data.by_hostname.get(hostname).map(_.mean_time).getOrElse {
                Timing_Data.median_time(
                  data.by_hostname.toList.map((hostname1, data) =>
                    data.mean_time.scale(hostname_factor(hostname1, hostname))))
              }
          }
      }
  }

  object Timing_Data {
    def median_time(obs: List[Time]): Time = obs.sortBy(_.ms).drop(obs.length / 2).head
    def mean_time(obs: Iterable[Time]): Time = Time.ms(obs.map(_.ms).sum / obs.size)

    private val dummy_entries =
      List(
        Timing_Entry("dummy", "dummy", 1, Time.minutes(5)),
        Timing_Entry("dummy", "dummy", 8, Time.minutes(1)))

    def dummy: Timing_Data = new Timing_Data(dummy_entries, Host_Infos.dummy)

    def make(
      host_infos: Host_Infos,
      build_history: List[(Build_Log.Meta_Info, Build_Log.Build_Info)],
    ): Timing_Data = {
      val hosts = host_infos.hosts
      val measurements =
        for {
          (meta_info, build_info) <- build_history
          build_host <- meta_info.get(Build_Log.Prop.build_host).toList
          (job_name, session_info) <- build_info.sessions.toList
          hostname = session_info.hostname.getOrElse(build_host)
          host <- hosts.find(_.info.hostname == build_host).toList
          threads = session_info.threads.getOrElse(host.info.num_cpus)
        } yield (job_name, hostname, threads) -> session_info.timing.elapsed

      val entries =
        if (measurements.isEmpty) dummy_entries
        else
          measurements.groupMap(_._1)(_._2).toList.map {
            case ((job_name, hostname, threads), timings) =>
              Timing_Entry(job_name, hostname, threads, median_time(timings))
          }

      new Timing_Data(entries, host_infos)
    }
  }


  /* host information */

  case class Host(info: isabelle.Host.Info, build: Build_Cluster.Host)

  object Host_Infos {
    def dummy: Host_Infos =
      new Host_Infos(
        List(Host(isabelle.Host.Info("dummy", Nil, 8, Some(1.0)), Build_Cluster.Host("dummy"))))

    def apply(build_hosts: List[Build_Cluster.Host], db: SQL.Database): Host_Infos = {
      def get_host(build_host: Build_Cluster.Host): Host = {
        val info =
          isabelle.Host.read_info(db, build_host.name).getOrElse(
            error("No benchmark for " + quote(build_host.name)))
        Host(info, build_host)
      }

      new Host_Infos(build_hosts.map(get_host))
    }
  }

  class Host_Infos private(val hosts: List[Host]) {
    private val by_hostname = hosts.map(host => host.info.hostname -> host).toMap

    def host_factor(from: Host, to: Host): Double =
      from.info.benchmark_score.get / to.info.benchmark_score.get

    val host_speeds: Ordering[Host] =
      Ordering.fromLessThan((host1, host2) => host_factor(host1, host2) > 1)

    def the_host(hostname: String): Host =
      by_hostname.getOrElse(hostname, error("Unknown host " + quote(hostname)))
    def the_host(node_info: Node_Info): Host = the_host(node_info.hostname)

    def num_threads(node_info: Node_Info): Int =
      if (node_info.rel_cpus.nonEmpty) node_info.rel_cpus.length
      else the_host(node_info).info.num_cpus

    def available(state: Build_Process.State): Resources = {
      val allocated =
        state.running.values.map(_.node_info).groupMapReduce(the_host)(List(_))(_ ::: _)
      Resources(this, allocated)
    }
  }


  /* offline tracking of resource allocations */

  case class Resources(
    host_infos: Host_Infos,
    allocated_nodes: Map[Host, List[Node_Info]]
  ) {
    val unused_hosts: List[Host] = host_infos.hosts.filter(allocated(_).isEmpty)

    def allocated(host: Host): List[Node_Info] = allocated_nodes.getOrElse(host, Nil)

    def allocate(node: Node_Info): Resources = {
      val host = host_infos.the_host(node)
      copy(allocated_nodes = allocated_nodes + (host -> (node :: allocated(host))))
    }

    def try_allocate_tasks(
      hosts: List[Host],
      tasks: List[(Build_Process.Task, Int)]
    ): (List[Config], Resources) =
      tasks match {
        case Nil => (Nil, this)
        case (task, threads) :: tasks =>
          val (config, resources) =
            hosts.find(available(_, threads)) match {
              case Some(host) =>
                val node_info = next_node(host, threads)
                (Some(Config(task.name, node_info)), allocate(node_info))
              case None => (None, this)
            }
          val (configs, resources1) = resources.try_allocate_tasks(hosts, tasks)
          (configs ++ config, resources1)
      }

    def next_node(host: Host, threads: Int): Node_Info = {
      val numa_node_num_cpus = host.info.num_cpus / (host.info.numa_nodes.length max 1)
      def explicit_cpus(node_info: Node_Info): List[Int] =
        if (node_info.rel_cpus.nonEmpty) node_info.rel_cpus else (0 until numa_node_num_cpus).toList

      val used_nodes = allocated(host).groupMapReduce(_.numa_node)(explicit_cpus)(_ ::: _)

      val available_nodes = host.info.numa_nodes
      val numa_node =
        if (!host.build.numa) None
        else available_nodes.sortBy(n => used_nodes.getOrElse(Some(n), Nil).length).headOption

      val used_cpus = used_nodes.getOrElse(numa_node, Nil).toSet
      val available_cpus = (0 until numa_node_num_cpus).filterNot(used_cpus.contains).toList

      val rel_cpus = if (available_cpus.length >= threads) available_cpus.take(threads) else Nil

      Node_Info(host.info.hostname, numa_node, rel_cpus)
    }

    def available(host: Host, threads: Int): Boolean = {
      val used = allocated(host)

      if (used.length >= host.build.jobs) false
      else {
        if (host.info.numa_nodes.length <= 1)
          used.map(host_infos.num_threads).sum + threads <= host.info.num_cpus
        else {
          def node_threads(n: Int): Int =
            used.filter(_.numa_node.contains(n)).map(host_infos.num_threads).sum

          host.info.numa_nodes.exists(
            node_threads(_) + threads <= host.info.num_cpus / host.info.numa_nodes.length)
        }
      }
    }
  }


  /* schedule generation */

  case class State(build_state: Build_Process.State, current_time: Time) {
    def start(config: Config): State =
      copy(build_state =
        build_state.copy(running = build_state.running +
          (config.job_name -> config.job_of(current_time))))

    def step(timing_data: Timing_Data): State = {
      val remaining =
        build_state.running.values.toList.map { job =>
          val elapsed = current_time - job.start_date.time
          val predicted = timing_data.estimate_config(Config.from_job(job))
          val remaining = if (elapsed > predicted) Time.zero else predicted - elapsed
          job -> remaining
        }

      if (remaining.isEmpty) error("Schedule step without running sessions")
      else {
        val (job, elapsed) = remaining.minBy(_._2.ms)
        State(build_state.remove_running(job.name).remove_pending(job.name), current_time + elapsed)
      }
    }

    def finished: Boolean = build_state.pending.isEmpty && build_state.running.isEmpty
  }

  abstract class Scheduler {
    def ready_jobs(state: Build_Process.State): Build_Process.State.Pending =
      state.pending.filter(entry => entry.is_ready && !state.is_running(entry.name))

    def next(state: Build_Process.State): List[Config]

    def build_duration(build_state: Build_Process.State): Time
  }

  abstract class Heuristic(timing_data: Timing_Data) extends Scheduler {
    def build_duration(build_state: Build_Process.State): Time = {
      @tailrec
      def simulate(state: State): State =
        if (state.finished) state
        else {
          val state1 =
            next(state.build_state).foldLeft(state)(_.start(_)).step(timing_data)
          simulate(state1)
        }

      val start = Time.now()
      simulate(State(build_state, start)).current_time - start
    }
  }

  class Meta_Heuristic(heuristics: List[Heuristic]) extends Scheduler {
    require(heuristics.nonEmpty)

    def best_result(state: Build_Process.State): (Heuristic, Time) =
      heuristics.map(heuristic => heuristic -> heuristic.build_duration(state)).minBy(_._2.ms)

    def next(state: Build_Process.State): List[Config] = best_result(state)._1.next(state)

    def build_duration(state: Build_Process.State): Time = best_result(state)._2
  }


  /* heuristics */

  class Timing_Heuristic(
    threshold: Time,
    timing_data: Timing_Data,
    sessions_structure: Sessions.Structure
  ) extends Heuristic(timing_data) {
    /* pre-computed properties for efficient heuristic */

    type Node = String

    val build_graph = sessions_structure.build_graph
    val all_maximals = build_graph.maximals.toSet
    val maximals_preds =
      all_maximals.map(node => node -> build_graph.all_preds(List(node)).toSet).toMap

    val remaining_time = build_graph.node_height(timing_data.best_time(_).ms)

    def elapsed_times(node: Node): Map[Node, Long] =
      build_graph.reachable_length(timing_data.best_time(_).ms, build_graph.imm_succs, List(node))

    def path_times(node: Node): Map[Node, Long] = {
      val maximals = all_maximals.intersect(build_graph.all_succs(List(node)).toSet)
      val elapsed_time = elapsed_times(node)

      maximals
        .flatMap(node => maximals_preds(node).map(_ -> elapsed_time(node)))
        .groupMapReduce(_._1)(_._2)(_ max _)
    }

    def is_critical(ms: Long): Boolean = ms > threshold.ms

    val critical_path_nodes =
      build_graph.keys.map(node =>
        node -> path_times(node).filter((_, time) => is_critical(time)).keySet).toMap


    /* scheduling */

    val host_infos = timing_data.host_infos

    def next(state: Build_Process.State): List[Config] = {
      val resources = host_infos.available(state)

      def best_threads(task: Build_Process.Task): Int =
        timing_data.best_threads(task.name).getOrElse(
          host_infos.hosts.map(_.info.num_cpus).max min 8)

      val ready = ready_jobs(state)
      val free = resources.unused_hosts

      if (ready.length <= free.length)
        resources.try_allocate_tasks(free, ready.map(task => task -> best_threads(task)))._1
      else {
        val pending_tasks = state.pending.map(_.name).toSet

        val critical_nodes = ready.toSet.flatMap(task => critical_path_nodes(task.name))
        def is_critical(node: Node): Boolean = critical_nodes.contains(node)

        def parallel_paths(node: Node): Int =
          build_graph.imm_succs(node).filter(is_critical).map(parallel_paths(_) max 1).sum max 1

        val (critical, other) =
          ready.sortBy(task => remaining_time(task.name)).reverse.partition(task =>
            is_critical(task.name))

        val (critical_hosts, other_hosts) =
          host_infos.hosts.sorted(host_infos.host_speeds).reverse.splitAt(
            critical.map(_.name).map(parallel_paths).sum)

        val (configs1, resources1) =
          resources.try_allocate_tasks(critical_hosts,
            critical.map(task => task -> best_threads(task)))

        val (configs2, _) = resources1.try_allocate_tasks(other_hosts, other.map(_ -> 1))

        configs1 ::: configs2
      }
    }
  }


  /* process for scheduled build */

  abstract class Scheduled_Build_Process(
    build_context: Build.Context,
    build_progress: Progress,
    server: SSH.Server,
  ) extends Build_Process(build_context, build_progress, server) {
    protected val start_date = Date.now()

    def init_scheduler(timing_data: Timing_Data): Scheduler

    /* global resources with common close() operation */

    private final lazy val _log_store: Build_Log.Store = Build_Log.store(build_options)
    private final lazy val _log_database: SQL.Database =
      try {
        val db = _log_store.open_database(server = this.server)
        _log_store.init_database(db)
        db
      }
      catch { case exn: Throwable => close(); throw exn }

    override def close(): Unit = {
      super.close()
      Option(_log_database).foreach(_.close())
    }


    /* previous results via build log */

    override def open_build_cluster(): Build_Cluster = {
      val build_cluster = super.open_build_cluster()
      build_cluster.init()
      if (build_context.master && build_context.max_jobs > 0) {
        val benchmark_options = build_options.string("build_hostname") = hostname
        Benchmark.benchmark(benchmark_options, progress)
      }
      build_cluster.benchmark()
      build_cluster
    }

    private val timing_data: Timing_Data = {
      val cluster_hosts: List[Build_Cluster.Host] =
        if (build_context.max_jobs == 0) build_context.build_hosts
        else {
          val local_build_host =
            Build_Cluster.Host(
              hostname, jobs = build_context.max_jobs, numa = build_context.numa_shuffling)
          local_build_host :: build_context.build_hosts
        }

      val host_infos = Host_Infos(cluster_hosts, _host_database)

      val build_history =
        for {
          log_name <- _log_database.execute_query_statement(
            Build_Log.private_data.meta_info_table.select(List(Build_Log.private_data.log_name)),
            List.from[String], res => res.string(Build_Log.private_data.log_name))
          meta_info <- _log_store.read_meta_info(_log_database, log_name)
          build_info = _log_store.read_build_info(_log_database, log_name)
        } yield (meta_info, build_info)

      Timing_Data.make(host_infos, build_history)
    }
    private val scheduler = init_scheduler(timing_data)

    def write_build_log(results: Build.Results, state: Build_Process.State.Results): Unit = {
      val sessions =
        for {
          (session_name, result) <- state.toList
          if !result.current
        } yield {
          val info = build_context.sessions_structure(session_name)
          val entry =
            if (!results.cancelled(session_name)) {
              val status =
                if (result.ok) Build_Log.Session_Status.finished
                else Build_Log.Session_Status.failed

              Build_Log.Session_Entry(
                chapter = info.chapter,
                groups = info.groups,
                hostname = Some(result.node_info.hostname),
                threads = Some(timing_data.host_infos.num_threads(result.node_info)),
                timing = result.process_result.timing,
                sources = Some(result.output_shasum.digest.toString),
                status = Some(status))
            }
            else
              Build_Log.Session_Entry(
                chapter = info.chapter,
                groups = info.groups,
                status = Some(Build_Log.Session_Status.cancelled))
          session_name -> entry
        }

      val settings =
        Build_Log.Settings.all_settings.map(_.name).map(name =>
          name -> Isabelle_System.getenv(name))
      val props =
        List(
          Build_Log.Prop.build_id.name -> build_context.build_uuid,
          Build_Log.Prop.build_engine.name -> build_context.engine.name,
          Build_Log.Prop.build_host.name -> hostname,
          Build_Log.Prop.build_start.name -> Build_Log.print_date(start_date))

      val meta_info = Build_Log.Meta_Info(props, settings)
      val build_info = Build_Log.Build_Info(sessions.toMap)
      val log_name = Build_Log.log_filename(engine = engine_name, date = start_date)

      _log_store.update_sessions(_log_database, log_name.file_name, build_info)
      _log_store.update_meta_info(_log_database, log_name.file_name, meta_info)
    }


    /* build process */

    case class Cache(state: Build_Process.State, configs: List[Config], estimate: Date) {
      def is_current(state: Build_Process.State): Boolean = this.state == state
      def is_current_estimate(estimate: Date): Boolean =
        this.estimate.time - estimate.time >= Time.seconds(1)
    }

    private var cache = Cache(Build_Process.State(), Nil, Date.now())

    override def next_node_info(state: Build_Process.State, session_name: String): Node_Info = {
      val configs =
        if (cache.is_current(state)) cache.configs
        else scheduler.next(state)
      configs.find(_.job_name == session_name).get.node_info
    }

    override def next_jobs(state: Build_Process.State): List[String] =
      if (progress.stopped)
        state.pending.filter(entry => entry.is_ready && !state.is_running(entry.name)).map(_.name)
      else if (cache.is_current(state)) cache.configs.map(_.job_name)
      else {
        val start = Time.now()
        val next = scheduler.next(state)
        val estimate = Date(Time.now() + scheduler.build_duration(state))
        val elapsed = Time.now() - start

        val timing_msg = if (elapsed.is_relevant) " (in " + elapsed.message + ")" else ""
        progress.echo_if(build_context.master && !cache.is_current_estimate(estimate),
          "Estimated completion: " + estimate + timing_msg)

        val configs = next.filter(_.node_info.hostname == hostname)
        cache = Cache(state, configs, estimate)
        configs.map(_.job_name)
      }

    override def run(): Build.Results = {
      val results = super.run()
      if (build_context.master) write_build_log(results, snapshot().results)
      results
    }
  }

  class Engine extends Build.Engine(engine_name) {
    override def open_build_process(
      context: Build.Context,
      progress: Progress,
      server: SSH.Server
    ): Build_Process =
      new Scheduled_Build_Process(context, progress, server) {
        def init_scheduler(timing_data: Timing_Data): Scheduler = {
          val heuristics =
            List(5, 10, 20).map(minutes =>
              Timing_Heuristic(
                Time.minutes(minutes),
                timing_data,
                context.build_deps.sessions_structure))
          new Meta_Heuristic(heuristics)
        }
      }
  }
}
