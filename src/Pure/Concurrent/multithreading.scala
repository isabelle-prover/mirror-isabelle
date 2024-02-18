/*  Title:      Pure/Concurrent/multithreading.scala
    Author:     Makarius

Multithreading in Isabelle/Scala.
*/

package isabelle


object Multithreading {
  /* physical processors */

  // slightly different from Poly/ML (more accurate)
  def num_processors(ssh: SSH.System = SSH.Local): Int =
    if (ssh.isabelle_platform.is_macos) {
      val result = ssh.execute("sysctl -n hw.physicalcpu").check
      Library.trim_line(result.out) match {
        case Value.Int(n) => n max 1
        case _ => 1
      }
    }
    else {
      val Physical = """^\s*physical id\s*:\s*(\d+)\s*$""".r
      val Cores = """^\s*cpu cores\s*:\s*(\d+)\s*$""".r

      var physical: Option[Int] = None
      var physical_cores = Map.empty[Int, Int]

      val result = ssh.execute("cat /proc/cpuinfo").check
      for (line <- Library.trim_split_lines(result.out)) {
        line match {
          case Physical(Value.Int(i)) => physical = Some(i)
          case Cores(Value.Int(i))
            if physical.isDefined && !physical_cores.isDefinedAt(physical.get) =>
            physical_cores = physical_cores + (physical.get -> i)
          case _ =>
        }
      }
      physical_cores.valuesIterator.sum max 1
    }


  /* max_threads */

  def max_threads(
    value: Int = Value.Int.unapply(System.getProperty("isabelle.threads", "0")) getOrElse 0,
    default: => Int = num_processors()
  ): Int = {
    if (value > 0) value else (default max 1) min 8
  }
}