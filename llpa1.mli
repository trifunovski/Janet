open Typecheck
open Syntax
open Tmhshtbl
open Parser

type rule =
  Id | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli
     | Llolli of TermVar.t | Ltensor of TermVar.t | Lwith1 of TermVar.t | Lwith2 of TermVar.t | Lplus of TermVar.t | Lone of TermVar.t

type delta = (Term.t , (context * Typ.t)) Hashtbl.t

type seq = context * Term.t * Typ.t

type drv = Node of seq * drv list

val printDrv : drv -> unit

val getContext : unit -> context

val getType : unit -> Typ.t

val startDrv : context -> Typ.t -> drv

val refineHole : drv -> Term.t -> rule -> drv

val completed : drv -> bool
