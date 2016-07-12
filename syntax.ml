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

module ABT =
struct
  type 'oper t
    = FV of TermVar.t
    | BV of int
    | ABS of string * 'oper t
    | OPER of 'oper

  type 'oper view
    = Var of TermVar.t
    | Binding of TermVar.t * 'oper t
    | Oper of 'oper

  type 'a binding_modifier = TermVar.t -> int -> 'a -> 'a

  exception Malformed

  let rec bind bind_oper x i t =
      match t with
      | FV y -> if TermVar.equal (x, y) then BV i else FV y
      | ABS (name, t) -> ABS (name, bind bind_oper x (i + 1) t)
      | BV n -> BV n
      | OPER f -> OPER (bind_oper x i f)

  let rec unbind unbind_oper x i t =
      match t with
      | BV j -> if i = j then FV x else BV j
      | ABS (name, t) -> ABS (name, unbind unbind_oper x (i + 1) t)
      | FV x -> FV x
      | OPER f -> OPER (unbind_oper x i f)

  let into bind_oper v =
      match v with
      | Var x -> FV x
      | Binding (x, t) -> ABS (TermVar.toUserString x, bind bind_oper x 0 t)
      | Oper f -> OPER f

  let out unbind_oper t =
      match t with
      | BV _ -> failwith "Internal Abbot Error"
      | FV x -> Var x
      | OPER f -> Oper f
      | ABS (name, t) ->
        let var = TermVar.newT name
        in Binding (var, unbind unbind_oper var 0 t)

  let rec aequiv oper_eq (t1, t2) =
      match (t1, t2) with
      | (BV i, BV j) -> i = j
      | (FV x, FV y) -> TermVar.equal (x, y)
      | (ABS (_, t1'), ABS (_, t2')) -> aequiv oper_eq (t1', t2')
      | (OPER f1, OPER f2) -> oper_eq (f1, f2)
      | _ -> false

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
            | T'Let of t * t * t
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
            | Let of t * t * t
            | Inl of (Typ.t * t)
            | Inr of (Typ.t * t)
            | Case of t * (termVar * t) * (termVar * t)
            | Unit (* Top *)
            | Star (* One *)


  let into (v : view) : t = failwith "unimplemented"
  let out (tm : t) : view = failwith "unimplemented"
  let aequiv (tm1 : t) (tm2 : t) : bool = failwith "unimplemented"

  let rec toString (tm : t) : string =
    match tm with
      | T'Var x -> TermVar.toUserString x
      | T'Lam ((x , t) , tm) -> "\\" ^ TermVar.toUserString x ^":"^ Typ.toString t ^ ".(" ^ toString tm ^ ")"
      | T'App (t1 , t2) -> "(" ^ toString t1 ^ ") (" ^ toString t2 ^ ")"
      | T'TenPair (t1 , t2) -> toString t1 ^ " X " ^ toString t2
      | T'WithPair (t1 , t2) -> "<" ^ toString t1 ^ " , " ^ toString t2 ^ ">"
      | T'Let (t1 , t3 , t2) -> "let " ^ toString t1 ^ " be " ^ toString t3 ^ " in " ^ toString t2
      | T'Inl (_ , t') -> "inl(" ^ toString t' ^ ")"
      | T'Inr (_ , t') -> "inr(" ^ toString t' ^ ")"
      | T'Case (z , (x , u) , (y , v)) -> "case " ^ toString z ^ " of inl(" ^ TermVar.toUserString x ^")" ^
          " => " ^ toString u ^ " , " ^ "inr(" ^ TermVar.toUserString y ^ ") => " ^ toString v
      | T'Unit -> "T"
      | T'Star -> "1"

  let rec subst (tm1 : t) (v : termVar) (tm2 : t) : t =
    match tm2 with
    | T'Var x -> if TermVar.equal (x , v) then tm1 else tm2
    | T'Lam ((x , a) , tm3) -> if TermVar.equal (x , v) then tm2 else T'Lam ((x , a) , subst tm3 v tm2)
    | T'App (t1 , t2) -> T'App (subst tm1 v t1 , subst tm1 v t2)
    | T'TenPair (t1 , t2) -> T'TenPair (subst tm1 v t1 , subst tm1 v t2)
    | T'WithPair (t1 , t2) -> T'WithPair (subst tm1 v t1 , subst tm1 v t2)
    | T'Let (t1 , t3 , t2) -> T'Let (subst tm1 v t1 , subst tm1 v t3 , subst tm1 v t2)
    | T'Inl (a , t') -> T'Inl (a , subst tm1 v t')
    | T'Inr (b , t') -> T'Inr (b , subst tm1 v t')
    | T'Case (t , (x , t1) , (y , t2)) -> T'Case (subst tm1 v t , (x , subst tm1 v t1) , (y , subst tm1 v t2))
    | _ -> tm2
end
