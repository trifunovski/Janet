open Tmhshtbl
open Syntax

type context = Typ.t TmHshtbl.t

type delta = (Term.t , (context * Typ.t)) Hashtbl.t

val typechecker :
  delta -> context -> Syntax.Term.t -> Syntax.Typ.t -> bool

val main : unit -> unit
