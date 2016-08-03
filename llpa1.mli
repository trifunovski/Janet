open Typecheck
open Syntax
open TmHshtbl
open Parser

type rule =
  Id | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli | Ltensor | Lwith1 | Lwith2 | Lplus | Lone

type delta = (Term.t , (context * Typ.t)) Hashtbl.t

type step = delta * context * Term.t * Typ.t

type drv = Axiom of step
         | Node1 of step * drv
         | Node2 of step * drv * drv
         | Unprocessed of step

type hole = Term.t

val printDrv : drv -> unit

val getContext : unit -> context

val getType : unit -> Typ.t

val startDrv : context -> Typ.t -> drv

val subIntoHole : hole -> Term.t -> Term.t

val refineHole : drv -> hole -> rule -> drv

val completed : drv -> bool
