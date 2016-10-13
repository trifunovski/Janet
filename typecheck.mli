open Tmhshtbl
open Syntax

type context = Typ.t TmHshtbl.t

type delta = (Term.metaVar , (context * Typ.t)) Hashtbl.t

val typechecker :
  delta -> context -> Term.t -> Typ.t -> bool

val main : unit -> unit
