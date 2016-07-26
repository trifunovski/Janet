open Syntax
open TmHshtbl

type context = Typ.t TmHshtbl.t

val typechecker :
  context -> Syntax.Term.t -> Syntax.Typ.t -> bool

val main : unit -> unit
