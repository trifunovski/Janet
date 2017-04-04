open Termvar
open Metavar
open Tmhshtbl

module Typ : sig
  type t =
         | Prop of string
         | Tensor of t * t
         | One
         | Lolli of t * t
         | With of t * t
         | Or of t * t

  val aequiv : t -> t -> bool

  val toString : t -> string
end

module Term : sig
  type termVar = TermVar.t
  type metaVar = MetaVar.t
  type 'a sub = 'a TmHshtbl.t
  type t

  type view =
            | Var of termVar
            | MV of metaVar * t sub
            | Lam of (termVar * Typ.t) * t
            | App of t * t
            | TenPair of t * t
            | WithPair of t * t
            | Letone of t * termVar * t
            | Letten of t * termVar * t
            | Letapp of t * (termVar * t) * t
            | Letfst of t * termVar * t
            | Letsnd of t * termVar * t
            | Inl of t
            | Inr of t
            | Case of termVar * (termVar * t) * (termVar * t)
            | Star (* One *)

  val into : view -> t
  val out : t -> view
  val aequiv : t -> t -> bool
  val toString : t -> string
  val applySub : (t sub) -> t -> t
end
