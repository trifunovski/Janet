module TermVar =
struct
  type t = string * int

  let counter = ref 0

  let hash (_ , id) = id

  let newT s = (s, (counter := !counter + 1; !counter))

  let equal ((_, id1) , (_, id2)) = (id1 = id2)

  let compare ((_, id1), (_, id2)) = Pervasives.compare id1 id2

  let toString (s, id) = s ^ "@" ^ (string_of_int id)

  let toUserString (s, id) = s

end

module Typ =
struct
  type t =
         | Prop of string
         | Tensor of t * t
         | One
         | Lolli of t * t
         | With of t * t
         | Top
         | Or of t * t

  let rec aequiv t1 t2 =
    match (t1 , t2) with
    | (Tensor (t1a , t1b) , Tensor (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (One , One) -> true
    | (Top , Top) -> true
    | (Prop a , Prop b) -> a = b
    | (Lolli (t1a , t1b) , Lolli (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (Or (t1a , t1b) , Or (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (With (t1a , t1b) , With (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | _ -> false

  let rec toString = function
    | Tensor (t1 , t2) -> "(" ^ toString t1 ^ " X " ^ toString t2 ^ ")"
    | One -> "1"
    | Top -> "T"
    | Prop a -> a
    | Lolli (t1 , t2) -> "(" ^ toString t1 ^ " --o " ^ toString t2 ^ ")"
    | Or (t1 , t2) -> "(" ^ toString t1 ^ " + " ^ toString t2 ^ ")"
    | With (t1 , t2) -> "(" ^ toString t1 ^ " & " ^ toString t2 ^ ")"

end

module Term =
struct
  type termVar = TermVar.t
  type t  = | T'Var of termVar
            | T'Lam of (termVar * Typ.t) * t
            | T'App of t * t
            | T'TenPair of t * t
            | T'WithPair of t * t
            | T'Let of t * termVar * t
            | T'Inl of (Typ.t * t)
            | T'Inr of (Typ.t * t)
            | T'Case of t * (termVar * t) * (termVar * t)
            | T'Unit (* Top *)
            | T'Star (* One *)

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


  let into (v : view) : t = failwith "unimplemented"
  let out (tm : t) : view = failwith "unimplemented"
  let aequiv (tm1 : t) (tm2 : t) : bool = failwith "unimplemented"
  let toString (tm : t) : string = failwith "unimplemented"

  let subst (tm1 : t) (v : termVar) (tm2 : t) : t = failwith "unimplemented"
end
