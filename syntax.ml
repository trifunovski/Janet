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

  type view =
            | Var of termVar
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
            | Unit (* Top *)
            | Star (* One *)
  and t = view

  type pr = | PVar of string
            | PLam of (string * Typ.t) * pr
            | PApp of pr * pr
            | PTenPair of pr * pr
            | PWithPair of pr * pr
            | PLetten of pr * string * pr
            | PLetapp of pr * string * pr
            | PLetfst of pr * string * pr
            | PLetsnd of pr * string * pr
            | PInl of pr
            | PInr of pr
            | PCase of string * (string * pr) * (string * pr)
            | PUnit (* Top *)
            | PStar (* One *)


  let into (v : view) : t = v

  let swapVar newV oldV curV =
    if TermVar.equal oldV curV then newV else oldV

  let rec swapInTerm newV oldV t =
  let st = swapInTerm newV oldV in
  let sv = swapVar newV oldV in
    match t with
    | Var z -> Var (sv z)
    | App (t1 , t2) -> App (st t1, st t2)
    | Lam ((x , tp) , tm) -> Lam (((sv x) , tp) , st tm)
    | TenPair (t1 , t2) -> TenPair (st t1 , st t2)
    | WithPair (t1 , t2) -> WithPair (st t1 , st t2)
    | Letten (t1 , v , t2) -> Letten (st t1 , sv v , st t2)
    | Letapp (t1 , v , t2) -> Letapp (st t1 , sv v , st t2)
    | Letfst (t1 , v , t2) -> Letfst (st t1 , sv v , st t2)
    | Letsnd (t1 , v , t2) -> Letsnd (st t1 , sv v , st t2)
    | Inl tm -> Inl (swapInTerm newV oldV tm)
    | Inr tm -> Inr (swapInTerm newV oldV tm)
    | Case (z , (x , t1) , (y , t2)) -> Case (sv z , (sv x , st t1) , (sv y , st t2))
    | _ -> t

  let out (tm : t) : view =
    match tm with
    | Lam ((x , tp) , tm) ->
        let newx = TermVar.newT (TermVar.toString x) in
          Lam ((newx,tp) , swapInTerm newx x tm)
    | Letten (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toString v) in
          Letten (t1 , newv , swapInTerm newv v t2)
    | Letapp (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toString v) in
          Letapp (t1 , newv , swapInTerm newv v t2)
    | Letfst (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toString v) in
          Letfst (t1 , newv , swapInTerm newv v t2)
    | Letsnd (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toString v) in
          Letsnd (t1 , newv , swapInTerm newv v t2)
    | Case (z , (x , t1) , (y , t2)) ->
        let newz = TermVar.newT (TermVar.toString z) in
        let newx = TermVar.newT (TermVar.toString x) in
        let newy = TermVar.newT (TermVar.toString y) in
          Case (newz , (newx , swapInTerm newx x t1) , (newy , swapInTerm newy y t2))
    | _ -> tm

  let rec toString (tm : t) : string =
    match tm with
      | Var x -> TermVar.toUserString x
      | Lam ((x , t) , tm) -> "λ" ^ TermVar.toUserString x ^" : "^ Typ.toString t ^ ".(" ^ toString tm ^ ")"
      | App (t1 , t2) -> "(" ^ toString t1 ^ ") (" ^ toString t2 ^ ")"
      | TenPair (t1 , t2) -> toString t1 ^ " X " ^ toString t2
      | WithPair (t1 , t2) -> "<" ^ toString t1 ^ " , " ^ toString t2 ^ ">"
      | Letten (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toString v ^ " in " ^ toString t2
      | Letapp (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toString v ^ " in " ^ toString t2
      | Letfst (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toString v ^ " in " ^ toString t2
      | Letsnd (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toString v ^ " in " ^ toString t2
      | Inl t' -> "inl(" ^ toString t' ^ ")"
      | Inr t' -> "inr(" ^ toString t' ^ ")"
      | Case (z , (x , u) , (y , v)) -> "case " ^ TermVar.toString z ^ " of inl(" ^ TermVar.toString x ^")" ^
          " => " ^ toString u ^ " , " ^ "inr(" ^ TermVar.toString y ^ ") => " ^ toString v
      | Unit -> "T"
      | Star -> "1"

  let rec aequiv (tm1 : t) (tm2 : t) : bool =
    match (tm1 , tm2) with
      | (Unit , Unit) -> true
      | (Star , Star) -> true
      | (Var x , Var y) -> TermVar.equal x y
      | (Inl t , Inl t') -> aequiv t t'
      | (Inr t , Inr t') -> aequiv t t'
      | (App (t1 , t2) , App (t1' , t2')) -> aequiv t1 t1' && aequiv t2 t2'
      | (TenPair (t1 , t2) , TenPair (t1' , t2') ) -> aequiv t1 t1' && aequiv t2 t2'
      | (WithPair (t1 , t2) , WithPair (t1' , t2') ) -> aequiv t1 t1' && aequiv t2 t2'
      | (Lam ((x , t) , tm) , Lam ((y , t') , tm')) -> aequiv tm (swapInTerm x y tm')
      | (Letten (t1 , v , t3) , Letten (t1' , v' , t3')) -> aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letapp (t1 , v , t3) , Letapp (t1' , v' , t3')) -> aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letfst (t1 , v , t3) , Letfst (t1' , v' , t3')) -> aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letsnd (t1 , v , t3) , Letsnd (t1' , v' , t3')) -> aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Case (z , (x , t1) , (y , t2)) , Case (z' , (x' , t1') , (y' , t2')) )
          -> aequiv t1 (swapInTerm x x' t1') && aequiv t2 (swapInTerm y y' t2')
      | _ -> false
end
