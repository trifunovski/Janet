module TermVar : sig
  type t

  val newT : string -> t

  (* Tests whether two temps are equal. *)
  val equal  : (t * t) -> bool

  (* Compares two temps. This is used to allow temps as keys into a table. *)
  val compare : (t * t) -> int

  (* Provides a string representation of the globally unique temp. *)
  val toString : t -> string

  (* Provides a hash representation of the temp. *)
  val hash : t -> int

  (* Provides the string used to create the temp. *)
  val toUserString : t -> string
end

module ABT : sig
  type 'oper t

  type 'oper view
    = Var of TermVar.t
    | Binding of TermVar.t * 'oper t
    | Oper of 'oper

  exception Malformed

  type 'a binding_modifier = TermVar.t -> int -> 'a -> 'a

  val bind : 'oper binding_modifier -> 'oper t binding_modifier
  val unbind : 'oper binding_modifier -> 'oper t binding_modifier
  val into : 'oper binding_modifier -> 'oper view -> 'oper t
  val out : 'oper binding_modifier -> 'oper t -> 'oper view

  val aequiv : ('oper * 'oper -> bool) -> 'oper t * 'oper t -> bool
end

module Typ : sig
  type t =
         | Prop of string
         | Tensor of t * t
         | One
         | Lolli of t * t
         | With of t * t
         | Top
         | Or of t * t

  val aequiv : t -> t -> bool

  val toString : t -> string
end

module Term : sig
  type termVar = TermVar.t
  type t

  type view =
            | Var of termVar
            | Lam of (termVar * Typ.t) * t
            | App of t * t
            | TenPair of t * t
            | WithPair of t * t
            | Let of t * t * t
            | Inl of (Typ.t * t)
            | Inr of (Typ.t * t)
            | Case of t * (termVar * t) * (termVar * t)
            | Unit (* Top *)
            | Star (* One *)

  val into : view -> t
  val out : t -> view
  val aequiv : t -> t -> bool
  val toString : t -> string

  val subst : t -> termVar -> t -> t
end
