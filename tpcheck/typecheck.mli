open Termvar
open Tmhshtbl
open Plhshtbl
open Syntax
open Placevar
open Tmvarrest

type context = Typ.t TmHshtbl.t

type rest = PlaceVar.t

type alpha = (SetTmVar.t) PlHshtbl.t

type eqs = Union of (rest * (rest * rest))
         | Sub of (rest * (rest * (TermVar.t * rest * TermVar.t)))
         | Link of (rest * (rest * (SetTmVar.t * SetTmVar.t)))
         | Mv of (rest * (rest * (rest * Term.t Term.sub * TermVar.t)))

type delta = (Term.metaVar , (context * rest * Typ.t)) Hashtbl.t

val typechecker :
  delta -> context -> Term.t -> Typ.t -> bool

val main : unit -> unit
