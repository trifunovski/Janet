open Termvar
open Tmhshtbl

module Typ =
struct
  type t =
         | Prop of string
         | Tensor of t * t
         | One
         | Lolli of t * t
         | With of t * t
         | Or of t * t

  let rec aequiv t1 t2 =
    match (t1 , t2) with
    | (Tensor (t1a , t1b) , Tensor (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (One , One) -> true
    | (Prop a , Prop b) -> a = b
    | (Lolli (t1a , t1b) , Lolli (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (Or (t1a , t1b) , Or (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | (With (t1a , t1b) , With (t2a , t2b)) -> aequiv t1a t2a && aequiv t1b t2b
    | _ -> false

  let rec toString = function
    | Tensor (t1 , t2) -> "(" ^ toString t1 ^ " ⊗ " ^ toString t2 ^ ")"
    | One -> "1"
    | Prop a -> a
    | Lolli (t1 , t2) -> "(" ^ toString t1 ^ " ⊸ " ^ toString t2 ^ ")"
    | Or (t1 , t2) -> "(" ^ toString t1 ^ " ⊕ " ^ toString t2 ^ ")"
    | With (t1 , t2) -> "(" ^ toString t1 ^ " & " ^ toString t2 ^ ")"

end

module Term =
struct
  type termVar = TermVar.t
  type metaVar = TermVar.t
  type 'a sub = 'a TmHshtbl.t

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
  and t = view

  let into (v : view) : t = v

  let rec swapInSub sub z x =
    TmHshtbl.iter
      (fun y t -> if TermVar.equal z y then () else
           TmHshtbl.replace sub y (swapInTerm z x t)) sub ; sub

  and swapVar newV oldV curV =
    if TermVar.equal oldV curV then newV else curV

  (* The newV is always a fresh variable when this function is called
   *)
  and swapInTerm newV oldV t =
  let st = swapInTerm newV oldV in
  let sv = swapVar newV oldV in
    match t with
    | Var z -> Var (sv z)
    | MV (u , sub) -> MV (u , swapInSub sub newV oldV)
    | App (t1 , t2) -> App (st t1, st t2)
    | Lam ((x , tp) , tm) when not (TermVar.equal oldV x) -> Lam ((x , tp) , st tm)
    | TenPair (t1 , t2) -> TenPair (st t1 , st t2)
    | WithPair (t1 , t2) -> WithPair (st t1 , st t2)
    | Letten (t1 , v , t2) when not (TermVar.equal oldV v) -> Letten (st t1 , v , st t2)
    | Letten (t1 , v , t2) -> Letten (st t1 , v , t2)
    | Letapp (t1 , v , t2) when not (TermVar.equal oldV v) -> Letapp (st t1 , v , st t2)
    | Letapp (t1 , v , t2) -> Letapp (st t1 , v , t2)
    | Letfst (t1 , v , t2) when not (TermVar.equal oldV v) -> Letfst (st t1 , v , st t2)
    | Letfst (t1 , v , t2) -> Letfst (st t1 , v , t2)
    | Letsnd (t1 , v , t2) when not (TermVar.equal oldV v) -> Letsnd (st t1 , v , st t2)
    | Letsnd (t1 , v , t2) -> Letsnd (st t1 , v , t2)
    | Inl tm -> Inl (swapInTerm newV oldV tm)
    | Inr tm -> Inr (swapInTerm newV oldV tm)
    | Case (z , (x , t1) , (y , t2)) ->
        let t1' = if not (TermVar.equal oldV x) then st t1 else t1 in
        let t2' = if not (TermVar.equal oldV y) then st t2 else t2 in
          Case (z , (x , t1') , (y , t2'))
    | _ -> t

  and out (tm : t) : view =
    match tm with
    | Lam ((x , tp) , tm) ->
        let newx = TermVar.newT (TermVar.toUserString x) in
          Lam ((newx,tp) , swapInTerm newx x tm)
    | Letten (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toUserString v) in
          Letten (t1 , newv , swapInTerm newv v t2)
    | Letapp (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toUserString v) in
          Letapp (t1 , newv , swapInTerm newv v t2)
    | Letfst (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toUserString v) in
          Letfst (t1 , newv , swapInTerm newv v t2)
    | Letsnd (t1 , v , t2) ->
        let newv = TermVar.newT (TermVar.toUserString v) in
          Letsnd (t1 , newv , swapInTerm newv v t2)
    | Case (z , (x , t1) , (y , t2)) ->
        let newz = TermVar.newT (TermVar.toUserString z) in
        let newx = TermVar.newT (TermVar.toUserString x) in
        let newy = TermVar.newT (TermVar.toUserString y) in
          Case (newz , (newx , swapInTerm newx x t1) , (newy , swapInTerm newy y t2))
    | _ -> tm

  let rec toString (tm : t) : string =
    match tm with
      | Var x -> TermVar.toUserString x
      | MV (x , _) -> "{ ?" ^ TermVar.toUserString x ^ " }"
      | Lam ((x , t) , tm) -> "λ" ^ TermVar.toUserString x ^" : "^ Typ.toString t ^ ".(" ^ toString tm ^ ")"
      | App (t1 , t2) -> "(" ^ toString t1 ^ ") (" ^ toString t2 ^ ")"
      | TenPair (t1 , t2) -> "(" ^ toString t1 ^ " × " ^ toString t2 ^ ")"
      | WithPair (t1 , t2) -> "<" ^ toString t1 ^ " , " ^ toString t2 ^ ">"
      | Letten (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toUserString v ^ " in " ^ toString t2
      | Letapp (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toUserString v ^ " in " ^ toString t2
      | Letfst (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toUserString v ^ " in " ^ toString t2
      | Letsnd (t1 , v , t2) -> "let " ^ toString t1 ^ " be " ^ TermVar.toUserString v ^ " in " ^ toString t2
      | Inl t' -> "inl(" ^ toString t' ^ ")"
      | Inr t' -> "inr(" ^ toString t' ^ ")"
      | Case (z , (x , u) , (y , v)) -> "case " ^ TermVar.toUserString z ^ " of inl(" ^ TermVar.toUserString x ^")" ^
          " => " ^ toString u ^ " , " ^ "inr(" ^ TermVar.toUserString y ^ ") => " ^ toString v
      | Star -> "*"

  let rec aequiv (tm1 : t) (tm2 : t) : bool =
    match (tm1 , tm2) with
      | (Star , Star) -> true
      | (Var x , Var y) -> TermVar.equal x y
      | (MV (x , _) , MV (y , _)) -> TermVar.equal x y
      | (Inl t , Inl t') -> aequiv t t'
      | (Inr t , Inr t') -> aequiv t t'
      | (App (t1 , t2) , App (t1' , t2')) -> aequiv t1 t1' && aequiv t2 t2'
      | (TenPair (t1 , t2) , TenPair (t1' , t2') ) -> aequiv t1 t1' && aequiv t2 t2'
      | (WithPair (t1 , t2) , WithPair (t1' , t2') ) -> aequiv t1 t1' && aequiv t2 t2'
      | (Lam ((x , t) , tm) , Lam ((y , t') , tm')) -> aequiv tm (swapInTerm x y tm')
      | (Letten (t1 , v , t3) , Letten (t1' , v' , t3')) ->
          aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letapp (t1 , v , t3) , Letapp (t1' , v' , t3')) ->
          aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letfst (t1 , v , t3) , Letfst (t1' , v' , t3')) ->
          aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Letsnd (t1 , v , t3) , Letsnd (t1' , v' , t3')) ->
          aequiv t1 t1' && aequiv t3 (swapInTerm v v' t3')
      | (Case (z , (x , t1) , (y , t2)) , Case (z' , (x' , t1') , (y' , t2')) )
          -> aequiv t1 (swapInTerm x x' t1') && aequiv t2 (swapInTerm y y' t2')
      | _ -> false


  let applySubToVar sub v =
    match TmHshtbl.mem sub v with
    | false -> into (Var v)
    | true -> TmHshtbl.find sub v

  let rec applySubToSub sub sub' =
      TmHshtbl.iter (fun y t ->
                      TmHshtbl.replace sub' y (applySub sub t)) sub'; sub'
  and applySub sub tm =
    match out tm with
        | MV (u , sub') -> into (MV (u , applySubToSub sub sub'))
        | Var z -> (applySubToVar sub z)
        | Case (z , (x , t1) , (y , t2)) ->
          let t1' = if TmHshtbl.mem sub x
                    then let sub1 = TmHshtbl.copy sub in
                         let () = TmHshtbl.remove sub1 x in
                            applySub sub1 t1
                    else applySub sub t1 in
          let t2' = if TmHshtbl.mem sub y
                    then let sub2 = TmHshtbl.copy sub in
                         let () = TmHshtbl.remove sub2 y in
                            applySub sub2 t2
                    else applySub sub t2 in
                    into (Case (z, (x , t1') , (y , t2')))
        | Lam ((x , tp) , tm) ->
          let tm' = if TmHshtbl.mem sub x
                    then let sub' = TmHshtbl.copy sub in
                         let () = TmHshtbl.remove sub' x in
                            applySub sub' tm
                    else applySub sub tm in
                    into (Lam ((x , tp) , tm'))
        | Letten (t1 , v , t2) ->
            let t1' = applySub sub t1 in
            let t2' = if TmHshtbl.mem sub v
                      then let sub' = TmHshtbl.copy sub in
                           let () = TmHshtbl.remove sub' v in
                              applySub sub' t2
                      else applySub sub t2 in
                      into (Letten (t1', v , t2'))

        | Letapp (t1 , v , t2) ->
            let t1' = applySub sub t1 in
            let t2' = if TmHshtbl.mem sub v
                      then let sub' = TmHshtbl.copy sub in
                           let () = TmHshtbl.remove sub' v in
                              applySub sub' t2
                      else applySub sub t2 in
                      into (Letapp (t1', v , t2'))

        | Letfst (t1 , v , t2) ->
            let t1' = applySub sub t1 in
            let t2' = if TmHshtbl.mem sub v
                      then let sub' = TmHshtbl.copy sub in
                           let () = TmHshtbl.remove sub' v in
                              applySub sub' t2
                      else applySub sub t2 in
                      into (Letfst (t1', v , t2'))

        | Letsnd (t1 , v , t2) ->
            let t1' = applySub sub t1 in
            let t2' = if TmHshtbl.mem sub v
                      then let sub' = TmHshtbl.copy sub in
                           let () = TmHshtbl.remove sub' v in
                              applySub sub' t2
                      else applySub sub t2 in
                      into (Letsnd (t1', v , t2'))

        | App (t1 , t2) -> into (App (applySub sub t1, applySub sub t2))
        | TenPair (t1 , t2) -> into (TenPair (applySub sub t1 , applySub sub t2))
        | WithPair (t1 , t2) -> into (WithPair (applySub sub t1 , applySub sub t2))
        | Inl tm -> into (Inl (applySub sub tm))
        | Inr tm -> into (Inr (applySub sub tm))
        | _ -> tm


end
