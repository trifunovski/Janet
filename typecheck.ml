open Syntax
open Parser

module TmHshtbl = Hashtbl.Make(Syntax.TermVar)

type context = Typ.t TmHshtbl.t

let lookup ctx v = try
  (Some (TmHshtbl.find ctx v))
  with | _ -> None

let add ctx v tp = TmHshtbl.add ctx v tp

let remove ctx v = TmHshtbl.remove ctx v

let find links s = try
  (Some (Hashtbl.find links s))
  with | _ -> None

let addHT links s tmvar = Hashtbl.add links s tmvar

let func ctx2 tm tp =
  match lookup ctx2 tm with
    | Some tp' when Typ.aequiv tp tp' -> ()
    | _ -> failwith "ctxs are not equivalent"

let ctxEquiv ctx1 ctx2 =
  if TmHshtbl.length ctx1 = TmHshtbl.length ctx2
  then try (TmHshtbl.iter (func ctx2) ctx1; true) with | _ -> false
  else false

let printCtxTerm tm tp = print_string ((TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp) ^ ", ")

let printCtx ctx = TmHshtbl.iter (printCtxTerm) ctx

let rec fixTerm links tm =
  match tm with
  | Term.PVar x -> (match find links x with
                | Some tmvar -> Term.into (Term.Var tmvar)
                | None ->
                  let tmvar = TermVar.newT x in
                    Term.into (Term.Var tmvar))
  | Term.PLam ((x , tp) , pr) ->
      (match find links x with
        | Some tmvar -> Term.into (Term.Lam ((tmvar, tp) , fixTerm links pr))
        | None ->
          let tmvar = TermVar.newT x in
          let () = addHT links x tmvar in
            Term.into (Term.Lam ((tmvar, tp) , fixTerm links pr)))
  | Term.PLetten (pr1 , x , pr2) ->
    (match find links x with
      | Some tmvar -> Term.into (Term.Letten (fixTerm links pr1 , tmvar , fixTerm links pr2))
      | None ->
        let tm1 = fixTerm links pr1 in
        let tmvar = TermVar.newT x in
        let () = addHT links x tmvar in
          Term.into (Term.Letten (tm1 , tmvar , fixTerm links pr2))
    )
  | Term.PLetapp (pr1 , x , pr2) ->
    (match find links x with
      | Some tmvar -> Term.into (Term.Letapp (fixTerm links pr1 , tmvar , fixTerm links pr2))
      | None ->
        let tm1 = fixTerm links pr1 in
        let tmvar = TermVar.newT x in
        let () = addHT links x tmvar in
          Term.into (Term.Letapp (tm1 , tmvar , fixTerm links pr2))
    )
  | Term.PLetfst (pr1 , x , pr2) ->
    (match find links x with
      | Some tmvar -> Term.into (Term.Letfst (fixTerm links pr1 , tmvar , fixTerm links pr2))
      | None ->
        let tm1 = fixTerm links pr1 in
        let tmvar = TermVar.newT x in
        let () = addHT links x tmvar in
          Term.into (Term.Letfst (tm1 , tmvar , fixTerm links pr2))
    )
  | Term.PLetsnd (pr1 , x , pr2) ->
    (match find links x with
      | Some tmvar -> Term.into (Term.Letsnd (fixTerm links pr1 , tmvar , fixTerm links pr2))
      | None ->
        let tm1 = fixTerm links pr1 in
        let tmvar = TermVar.newT x in
        let () = addHT links x tmvar in
          Term.into (Term.Letsnd (tm1 , tmvar , fixTerm links pr2))
    )
  | Term.PCase (z , (x , u) , (y , t)) ->
    (match find links z with
      | Some tmvarZ ->
        (match find links x with
          | Some tmvarX ->
              let tm1 = fixTerm links u in
              (match find links y with
                | Some tmvarY -> Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t)))
                | None ->
                  let tmvarY = TermVar.newT y in
                  let () = addHT links y tmvarY in
                    Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t) ))
                )
          | None ->
              let tmvarX = TermVar.newT x in
              let () = addHT links x tmvarX in
              let tm1 = fixTerm links u in
              let () = Hashtbl.remove links x in
              (match find links y with
                | Some tmvarY -> Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t)))
                | None ->
                  let tmvarY = TermVar.newT y in
                  let () = addHT links y tmvarY in
                    Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t) ))
                )
        )
      | None ->
        let tmvarZ = TermVar.newT z in
        let () = addHT links z tmvarZ in
        (match find links x with
          | Some tmvarX ->
              let tm1 = fixTerm links u in
              (match find links y with
                | Some tmvarY -> Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t)))
                | None ->
                  let tmvarY = TermVar.newT y in
                  let () = addHT links y tmvarY in
                    Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t) ))
                )
          | None ->
              let tmvarX = TermVar.newT x in
              let () = addHT links x tmvarX in
              let tm1 = fixTerm links u in
              let () = Hashtbl.remove links x in
              (match find links y with
                | Some tmvarY -> Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t)))
                | None ->
                  let tmvarY = TermVar.newT y in
                  let () = addHT links y tmvarY in
                    Term.into (Term.Case (tmvarZ , (tmvarX , tm1) , (tmvarY , fixTerm links t) ))
                )
        )
    )
  | Term.PApp (pr1 , pr2) -> Term.into (Term.App (fixTerm links pr1 , fixTerm links pr2))
  | Term.PTenPair (pr1 , pr2) -> Term.into (Term.TenPair (fixTerm links pr1 , fixTerm links pr2))
  | Term.PWithPair (pr1 , pr2) -> Term.into (Term.WithPair (fixTerm links pr1 , fixTerm links pr2))
  | Term.PInl (pr) -> Term.into (Term.Inl (fixTerm links pr))
  | Term.PInr (pr) -> Term.into (Term.Inr (fixTerm links pr))
  | Term.PUnit -> Term.into (Term.Unit)
  | Term.PStar -> Term.into (Term.Star)

let rec typecheck ctx tm tp =
  match (Term.out tm , tp) with
  (* Right Rules *)
  | (Term.Var x , tp) ->
      (match lookup ctx x with
        | Some tp' when Typ.aequiv tp tp' ->
            let () = remove ctx x in
              Some ctx
        | _ -> None)
  | (Term.Lam ((x , tp1) , tm1) , Typ.Lolli (a , b)) when Typ.aequiv tp1 a ->
    let () = add ctx x a in
      typecheck ctx tm1 b
  | (Term.TenPair (t , u) , Typ.Tensor (a , b)) ->
    (match typecheck ctx t a with
    | Some rest -> typecheck rest u b
    | None -> None)
  | (Term.Inl t , Typ.Or (a , b)) -> typecheck ctx t a
  | (Term.Inr t , Typ.Or (a , b)) -> typecheck ctx t b
  | (Term.WithPair (t , u) , Typ.With (a , b)) ->
    (match (typecheck ctx t a , typecheck ctx u b) with
    | (Some rest1 , Some rest2) when ctxEquiv rest1 rest2 -> Some rest1
    | _ -> None)
  | (Term.Star , Typ.One) -> Some ctx
  (* Left Rules *)
  | (Term.Letten (t1 , v , t2) , tp) ->
    (match (Term.out t1 , lookup ctx v) with
      | (Term.TenPair (xt , yt) , Some (Typ.Tensor (a , b))) ->
        (match (Term.out xt , Term.out yt) with
          | (Term.Var x , Term.Var y) ->
            let () = remove ctx v in
            let () = add ctx x a in
            let () = add ctx y b in
              typecheck ctx t2 tp
          | _ -> None)
      | _ -> None)
  | (Term.Letfst (t1 , v , t2) , tp) ->
    (match (Term.out t1 , lookup ctx v) with
      | (Term.WithPair (xt , _) , Some (Typ.With (a , b))) ->
        (match (Term.out xt) with
          | (Term.Var x) ->
            let () = remove ctx v in
            let () = add ctx x a in
              typecheck ctx t2 tp
          | _ -> None)
      | _ -> None)
  | (Term.Letsnd (t1 , v , t2) , tp) ->
    (match (Term.out t1 , lookup ctx v) with
      | (Term.WithPair (_ , yt) , Some (Typ.With (a , b))) ->
        (match (Term.out yt) with
          | (Term.Var y) ->
            let () = remove ctx v in
            let () = add ctx y b in
              typecheck ctx t2 tp
          | _ -> None)
      | _ -> None)
  | (Term.Case (z , (x , u) , (y , t)) , tp) ->
    (match lookup ctx z with
      | Some (Typ.Or (a , b)) ->
        let () = remove ctx z in
        let () = add ctx x a in
        let res1 = typecheck ctx u tp in
        let () = remove ctx x in
        let () = add ctx y b in
        (match (res1 , typecheck ctx t tp) with
          | (Some rest1 , Some rest2) when ctxEquiv rest1 rest2 -> Some rest1
          | _ -> None)
      | _ -> None)
  | (Term.Letapp (ft , x , u) , tp) ->
    (match Term.out ft with
      | Term.App (ftm , t) ->
        (match Term.out ftm with
          | Term.Var f ->
            (match lookup ctx f with
              | Some (Typ.Lolli (a , b)) ->
                let () = remove ctx f in
                (match typecheck ctx t a with
                  | Some rest ->
                    let () = add rest x b in
                      typecheck rest u tp
                  | _ -> None)
              | _ -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let typechecker ctx tm tp =
  match typecheck ctx tm tp with
    | Some rest_ctx -> if TmHshtbl.length rest_ctx = 0 then true else false
    | _ -> false

let rec map f = function
  | [] -> []
  | x :: xs -> (f x) :: (map f xs)

let rec get_context ctx links =
  let () = print_endline "Enter the context:" in
  let str = input_line stdin in
  let lexbuf = Lexing.from_string str in
  let ctxlist = Parser.ctxtmEXP Lexer.exp_token lexbuf in
  let _ = map (fun (s , x , a) -> TmHshtbl.add ctx x a; Hashtbl.add links s x; (s , x , a)) ctxlist  in
    (ctx , links)

let main (_ : unit) =
  let (ctx , links) = get_context (TmHshtbl.create 256) (Hashtbl.create 256) in
  let starting = TmHshtbl.copy ctx in
  let () = print_endline "Enter the intended type of the term:" in
  let strtp = input_line stdin in
  let tpbuf = Lexing.from_string strtp in
  let tp = Parser.typEXP Lexer.exp_token tpbuf in
  let () = print_endline "Enter the term you want typechecked: " in
  let str = input_line stdin in
  let lexbuf = Lexing.from_string str in
  let ptm = Parser.termEXP Lexer.exp_token lexbuf in
  let tm = fixTerm links ptm in
  if typechecker ctx tm tp
  then let () = printCtx starting in
  print_endline ("⊢ " ^ (Term.toString tm) ^ " : " ^ (Typ.toString tp))
  else let () = printCtx starting in
  print_endline ("⊬ " ^ (Term.toString tm) ^ " : " ^ (Typ.toString tp))
