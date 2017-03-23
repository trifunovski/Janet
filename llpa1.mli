open Termvar
open Tmhshtbl
open Parser
open Syntax
open Typecheck

type rule =
     | Id of TermVar.t | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli
     | Llolli of TermVar.t | Ltensor of TermVar.t | Lwith1 of TermVar.t
     | Lwith2 of TermVar.t | Lplus of TermVar.t | Lone of TermVar.t

type seq = context * rest * Term.t * Typ.t

(*
val printDrv : drv -> unit

val getContext : unit -> context

val getType : unit -> Typ.t

val startDrv : context -> Typ.t -> (delta * drv)


val createTerm : rule -> Term.metaVar -> Typecheck.delta -> Term.t option

(* val refineHole : drv -> Term.metaVar -> rule -> delta -> (drv * ((Term.t -> Term.t) * delta) option) *)

val completed : drv -> bool

*)
