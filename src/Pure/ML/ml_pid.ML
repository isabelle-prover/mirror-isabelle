(*  Title:      Pure/ML/ml_pid.ML
    Author:     Makarius

Native PID for ML process.
*)

signature ML_PID =
sig
  val get: unit -> int
end;

structure ML_Pid: ML_PID =
struct

val get =
\<^if_windows>\<open>
  Foreign.buildCall0
    (Foreign.getSymbol (Foreign.loadLibrary "kernel32.dll") "GetCurrentProcessId", (), Foreign.cInt);
\<close>
\<^if_unix>\<open>SysWord.toLargeInt o Posix.Process.pidToWord o Posix.ProcEnv.getpid;\<close>

end;
