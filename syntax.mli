module TermVar : sig
  type t

  val newT : string -> t

  (* Tests whether two temps are equal. *)
  val equal  : t -> t -> bool

  (* Compares two temps. This is used to allow temps as keys into a table. *)
  val compare : t -> t -> int

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
         | Or of t * t

  val aequiv : t -> t -> bool

  val toString : t -> string
end

module TmHshtbl :
sig
  type key = TermVar.t
  type 'a t = 'a Hashtbl.Make(TermVar).t
  val create : int -> 'a t
  val clear : 'a t -> unit
  val reset : 'a t -> unit
  val copy : 'a t -> 'a t
  val add : 'a t -> key -> 'a -> unit
  val remove : 'a t -> key -> unit
  val find : 'a t -> key -> 'a
  val find_all : 'a t -> key -> 'a list
  val replace : 'a t -> key -> 'a -> unit
  val mem : 'a t -> key -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val length : 'a t -> int
  val stats : 'a t -> Hashtbl.statistics
end

module Term : sig
  type termVar = TermVar.t
  type metaVar = TermVar.t
  type 'a sub = 'a TmHshtbl.t
  type t

  type view =
            | Var of termVar
            | MV of metaVar * t sub
            | Lam of (termVar * Typ.t) * t
            | App of t * t
            | TenPair of t * t
            | WithPair of t * t
            | Letten of t * termVar * t
            | Letapp of t * termVar * t
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
end
