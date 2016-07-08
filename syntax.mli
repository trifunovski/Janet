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
            | Let of t * termVar * t
            | Inl of (Typ.t * t)
            | Inr of (Typ.t * t)
            | Case of termVar * (termVar * t) * (termVar * t)
            | Unit (* Top *)
            | Star (* One *)

  val into : view -> t
  val out : t -> view
  val aequiv : t -> t -> bool
  val toString : t -> string

  val subst : t -> termVar -> t -> t
end
