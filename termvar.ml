module TermVar =
struct
  type t = string * int

  let counter = ref 0

  let hash (_ , id) = id

  let newT s = (s, (counter := !counter + 1; !counter))

  let equal (_, id1) (_, id2) = (id1 = id2)

  let compare (_, id1) (_, id2) = Pervasives.compare id1 id2

  let toString (s, id) = s ^ "@" ^ (string_of_int id)

  let toUserString (s, id) = s

end
