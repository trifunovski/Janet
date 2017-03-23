open Termvar
open Tmhshtbl
open Syntax
open Placerest
open Tmvarrest

type context = Typ.t TmHshtbl.t

type rest = SetPlaceVar.t * SetTmVar.t

type form = Sin of rest | Sub of rest * (rest * TermVar.t)

type eqs = (form * form) list

type delta = (Term.metaVar , (context * rest * Typ.t)) Hashtbl.t

val typechecker :
  delta -> context -> Term.t -> Typ.t -> bool

val main : unit -> unit
