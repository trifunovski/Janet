open Syntax
open Parser

exception TmTp of TermVar.t * Typ.t

module TmHshtbl = Hashtbl.Make(Syntax.TermVar)

type context = Typ.t TmHshtbl.t

let lookup ctx v = try
  (Some (TmHshtbl.find ctx v))
  with | _ -> None

let add ctx v tp = TmHshtbl.add ctx v tp

let remove ctx v = TmHshtbl.remove ctx v

let chooseFromCtx ctx1 =
  let ctx2 = TmHshtbl.create 256 in
  let () = print_endline "For each term type 1 if you want it to go to the left context, anything else for the right" in
  TmHshtbl.iter (
    fun tm tp ->
      let () = print_endline ((TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp)) in
      let str = input_line stdin in
      match str with
      | "1" -> ()
      | _ -> remove ctx1 tm; add ctx2 tm tp
    ) ctx1 ; (ctx1 , ctx2)

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

let printCtxTerm tm tp = print_string ((TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp) ^ " ")

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


let holeCtr = ref 0

type drv = Axiom of context * Term.t * Typ.t
         | Node1 of (context * Term.t * Typ.t) * drv
         | Node2 of (context * Term.t * Typ.t) * drv * drv
         | Unprocessed of context * TermVar.t * Typ.t

let rec completed = function
  | Axiom (_) -> true
  | Node1 ((_) , d) -> completed d
  | Node2 ((_) , d1 , d2) -> completed d1 && completed d2
  | _ -> false

let printUnprocessed ctx holTermVar tp =
  let () = printCtx ctx in print_endline ("⊢ " ^ TermVar.toUserString holTermVar ^ " : " ^ (Typ.toString tp))

let printStep ctx tm tp =
  let () = printCtx ctx in print_endline ("⊢ " ^ Term.toString tm ^ " : " ^ (Typ.toString tp))


let rec printDrv = function
  | Axiom (ctx , tm , tp) -> printStep ctx tm tp
  | Node1 ((ctx , tm , tp) , d) -> printStep ctx tm tp ; printDrv d
  | Node2 ((ctx , tm , tp) , d1 , d2) -> printStep ctx tm tp ; printDrv d1 ; printDrv d2
  | Unprocessed (ctx , tmvar , tp) -> printUnprocessed ctx tmvar tp

let rec getHoleComponents holTermVar = function
  | Unprocessed (ctx , h , tp) -> if TermVar.equal holTermVar h then Some (ctx , tp) else None
  | Node1 ((_) , d) -> getHoleComponents holTermVar d
  | Node2 ((_) , d1 , d2) ->
    (match getHoleComponents holTermVar d1 with
      | None -> getHoleComponents holTermVar d2
      | Some (ctx , tp) -> Some (ctx , tp))
  | _ -> None


let rec replaceInTerm oldTermVar newTerm tm =
  let reccall = replaceInTerm oldTermVar newTerm in
  match Term.out tm with
  | Term.Var x -> if TermVar.equal x oldTermVar then newTerm else tm
  | Term.Lam ((x , tp) , tm') -> Term.into ( Term.Lam ((x,tp) , reccall tm'))
  | Term.App (t1 , t2) -> Term.into (Term.App (reccall t1 , reccall t2))
  | Term.TenPair (t1 , t2) -> Term.into (Term.TenPair (reccall t1 , reccall t2))
  | Term.WithPair (t1 , t2) -> Term.into (Term.WithPair (reccall t1 , reccall t2))
  | Term.Letten (t1 , v , t2) -> Term.into (Term.Letten (reccall t1 , v , reccall t2))
  | Term.Letapp (t1 , v , t2) -> Term.into (Term.Letapp (reccall t1 , v , reccall t2))
  | Term.Letfst (t1 , v , t2) -> Term.into (Term.Letfst (reccall t1 , v , reccall t2))
  | Term.Letsnd (t1 , v , t2) -> Term.into (Term.Letsnd (reccall t1 , v , reccall t2))
  | Term.Inl t' -> Term.into (Term.Inl (reccall t'))
  | Term.Inr t' -> Term.into (Term.Inr (reccall t'))
  | Term.Case (z , (x , t1) , (y , t2)) -> Term.into (Term.Case (z , (x , reccall t1) , (y , reccall t2)))
  | Term.Unit -> tm
  | Term.Star -> tm

let rec replaceHole oldTermVar newTerm newDrv = function
  | Unprocessed (ctx , h , tp) ->
      if TermVar.equal h oldTermVar
      then newDrv
      else Unprocessed (ctx , h , tp)
  | Node1 ((ctx , tm , tp) , d) ->
      Node1 ((ctx , replaceInTerm oldTermVar newTerm tm, tp) ,
                  replaceHole oldTermVar newTerm newDrv d)
  | Node2 ((ctx , tm , tp) , d1 , d2) ->
      Node2 ((ctx , replaceInTerm oldTermVar newTerm tm , tp) ,
        replaceHole oldTermVar newTerm newDrv d1,
        replaceHole oldTermVar newTerm newDrv d2)
  | Axiom (ctx , tm , tp) -> Axiom (ctx , tm , tp)


let possibleRules ctx tp =
  let idtp = ref 0 in
  let () = TmHshtbl.iter (fun tm tp' -> if Typ.aequiv tp tp' then idtp := !idtp + 1 else ()) ctx in
  let l = if !idtp > 0 then ["I"] else [] in
  match tp with
    | Typ.Prop a ->
        (match TmHshtbl.fold (fun k v acc -> (k,v)::acc) ctx [] with
        | [(x,tp)] when Typ.aequiv (Typ.Prop a) tp -> ["I" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]
        | _ -> ["Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"])
    | Typ.Tensor (t1 , t2) -> l@["Xright" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]
    | Typ.One ->
        if (TmHshtbl.length ctx = 0) then
        ["1right"]
        else []
    | Typ.Lolli (_ , _) -> l@["-oright" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]
    | Typ.With (_ , _) -> l@["&right" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]
    | Typ.Top -> []
    | Typ.Or (_ , _) -> l@["+right1" ; "+right2" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]


let rec printList = function
    | [] -> print_endline ""
    | x :: xs -> print_string (x ^ " "); printList xs

(*
let split ctx a b =
  let () = printCtx ctx in
  let () = print_endline ("Choose a subset of the context that you would like to use to prove a term of type "^ Typ.toString (a)) in
  let
*)

let rec holes drv holeTerms =
  let () = print_string "Enter the hole you want to work on: " in
  let holnum = read_int () in
  match Hashtbl.mem holeTerms holnum with
  | false -> print_endline "You entered a non-existent hole number. Try again."; holes drv holeTerms
  | true ->
    let holTerm : TermVar.t = Hashtbl.find holeTerms holnum in
    let res = getHoleComponents holTerm drv in
    (match res with
      | None -> print_endline "You entered a non-existent hole number. Try again."; holes drv holeTerms
      | Some (ctx , tp) ->
    let () = printUnprocessed ctx holTerm tp in
    let () = print_endline "Possible rules to apply:" in
    let () = printList (possibleRules ctx tp) in
    let () = print_endline "Enter a name of a rule, or type back to go back:" in
    let str = input_line stdin in
      (match (str , tp) with
      | ("back" , _) -> holes drv holeTerms
      | ("I" , tp) ->
        (match TmHshtbl.fold (fun k v acc -> (k,v)::acc) ctx [] with
        | [(x,tp')] when Typ.aequiv tp tp' ->
            proofAssistant (replaceHole holTerm (Term.into (Term.Var x))
                (Axiom (ctx , (Term.into (Term.Var x)) , tp)) drv) holeTerms
        | _ -> print_endline "bad context"; holes drv holeTerms)
      | ("1right" , Typ.One) when TmHshtbl.length ctx = 0 ->
          proofAssistant (replaceHole holTerm (Term.into Term.Star) (Axiom (ctx ,Term.into Term.Star , tp )) drv) holeTerms
      | ("-oright" , Typ.Lolli (a , b)) ->
          let x = TermVar.newT "x" in
          let newCtx = TmHshtbl.copy ctx in
          let () = TmHshtbl.add newCtx x a in
          let newHoleNum = (holeCtr := !holeCtr + 1; !holeCtr) in
          let newHole = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum)  ^" }") in
          let () = Hashtbl.add holeTerms newHoleNum newHole in
          let newTerm = (Term.into (Term.Lam ((x , a) , (Term.into (Term.Var newHole))) )) in
            proofAssistant
                  (replaceHole
                      holTerm
                      newTerm
                      (Node1 ((ctx , newTerm , tp) ,
                      (Unprocessed (newCtx , newHole , b)) ))
                      drv)
                  holeTerms
      | ("&right" , Typ.With (a , b)) ->
          let newHoleNum1 = (holeCtr := !holeCtr + 1; !holeCtr) in
          let newHole1 = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum1)  ^" }") in
          let newHoleNum2 = (holeCtr := !holeCtr + 1; !holeCtr) in
          let newHole2 = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum2)  ^" }") in
          let () = Hashtbl.add holeTerms newHoleNum1 newHole1 in
          let () = Hashtbl.add holeTerms newHoleNum2 newHole2 in
          let newTerm = (Term.into (Term.WithPair (Term.into (Term.Var newHole1) ,
          Term.into (Term.Var newHole2) ))) in
            proofAssistant
              (replaceHole
                 holTerm
                 newTerm
                 (Node2 ((ctx , newTerm , tp),
                 Unprocessed (ctx , newHole1 , a),
                 Unprocessed (ctx , newHole2 , b)))
                 drv)
              holeTerms
      | ("+right1" , Typ.Or (a , b)) ->
            let newHoleNum = (holeCtr := !holeCtr + 1; !holeCtr) in
            let newHole = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum)  ^" }") in
            let () = Hashtbl.add holeTerms newHoleNum newHole in
            let newTerm = (Term.into (Term.Inl (Term.into (Term.Var newHole)))) in
            proofAssistant
                (replaceHole
                    holTerm
                    newTerm
                    (Node1 ((ctx , newTerm , tp) ,
                    Unprocessed (ctx , newHole , a)))
                    drv)
                holeTerms
      | ("+right2" , Typ.Or (a , b))->
            let newHoleNum = (holeCtr := !holeCtr + 1; !holeCtr) in
            let newHole = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum)  ^" }") in
            let () = Hashtbl.add holeTerms newHoleNum newHole in
            let newTerm = (Term.into (Term.Inr (Term.into (Term.Var newHole)))) in
            proofAssistant
                (replaceHole
                    holTerm
                    newTerm
                    (Node1 ((ctx , newTerm , tp) ,
                    Unprocessed (ctx , newHole , b)))
                    drv)
                holeTerms
      | ("Xright" , Typ.Tensor (a,b)) ->
                      let (ctx1 , ctx2) = chooseFromCtx ctx in
                      let newHoleNum1 = (holeCtr := !holeCtr + 1; !holeCtr) in
                      let newHole1 = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum1)  ^" }") in
                      let newHoleNum2 = (holeCtr := !holeCtr + 1; !holeCtr) in
                      let newHole2 = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum2)  ^" }") in
                      let () = Hashtbl.add holeTerms newHoleNum1 newHole1 in
                      let () = Hashtbl.add holeTerms newHoleNum2 newHole2 in
                      let newTerm = (Term.into (Term.TenPair (Term.into (Term.Var newHole1) , Term.into (Term.Var newHole2)))) in
                proofAssistant
                    (replaceHole
                        holTerm
                        newTerm
                        (Node2 ((ctx , newTerm , tp) ,
                        Unprocessed (ctx1 , newHole1 , a) ,
                        Unprocessed (ctx2 , newHole2 , b) ))
                        drv)
                    holeTerms
      | ("Xleft" , _) ->
          let res = (try (
            (TmHshtbl.iter (fun tm' tp' ->
                          match tp' with
                           | Typ.Tensor (a , b) ->
                              let () = print_endline ("Do you want to use this variable: " ^ (TermVar.toUserString tm') ^" : " ^ (Typ.toString tp')) in
                              let str = input_line stdin in
                              (match str with
                                | "yes" -> raise (TmTp (tm' , tp'))
                                | _ -> ()
                              )
                           | _ -> ()) ctx) ; None
            ) with
            | TmTp (tm' , tp') -> Some (tm' , tp')
            | _ -> None)
            in
          (match res with
            | Some (tm' , Typ.Tensor (a , b)) ->
                let oldctx = TmHshtbl.copy ctx in
                let () = remove ctx tm' in
                let x = TermVar.newT "x" in
                let y = TermVar.newT "y" in
                let () = add ctx x a in
                let () = add ctx y b in
                let newHoleNum = (holeCtr := !holeCtr + 1; !holeCtr) in
                let newHole = TermVar.newT ("{ ?" ^ (string_of_int newHoleNum)  ^" }") in
                let () = Hashtbl.add holeTerms newHoleNum newHole in
                let newTerm =
                Term.into (Term.Letten
                              (Term.into (Term.TenPair (Term.into (Term.Var x) ,Term.into (Term.Var y))),
                              tm' ,
                              Term.into (Term.Var newHole) )) in
                proofAssistant
                  (replaceHole
                      holTerm
                      newTerm
                      (Node1 ((oldctx , newTerm , tp) , Unprocessed (ctx , newHole , tp)))
                      drv)
                  holeTerms
            | _ -> print_endline "Invalid rule." ; holes drv holeTerms
            )
    (*
      | "-oleft" ->
      | "&left1" ->
      | "&left2" ->
      | "+left" ->
      | "1left" ->

      *)
      | _ -> print_endline "Invalid rule." ; holes drv holeTerms))
and proofAssistant drv holeTerms =
  let () = printDrv drv in
  match (completed drv) with
  | true -> holeCtr := 0 ; print_endline "The proof is complete."
  | false -> holes drv holeTerms

let main2 (_ : unit) =
  let (ctx , links) = get_context (TmHshtbl.create 256) (Hashtbl.create 256) in
  let () = print_endline "Enter the intended type of the term:" in
  let strtp = input_line stdin in
  let tpbuf = Lexing.from_string strtp in
  let tp = Parser.typEXP Lexer.exp_token tpbuf in
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1termvar = TermVar.newT ("{ ?" ^ (string_of_int hole1) ^" }") in
  let tree = Unprocessed (ctx , hole1termvar , tp) in
  let holeHT = Hashtbl.create 256 in
  let () = Hashtbl.add holeHT hole1 hole1termvar in
    proofAssistant tree holeHT
