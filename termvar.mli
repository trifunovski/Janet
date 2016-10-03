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
