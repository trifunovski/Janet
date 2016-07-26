type drv

val completed : drv -> bool

val printDrv : drv -> unit

val proofAssistant : drv -> (int, Syntax.TermVar.t) Hashtbl.t -> unit

val main2 : unit -> unit
