open Termvar
open Tmhshtbl
open Syntax
open Parser
open Typecheck

exception TmTp of TermVar.t * Typ.t

type delta = (Term.t , (context * Typ.t)) Hashtbl.t

let holeCtr = ref 0

type drv = Axiom of delta * context * Term.t * Typ.t
         | Node1 of (delta * context * Term.t * Typ.t) * drv
         | Node2 of (delta * context * Term.t * Typ.t) * drv * drv
         | Unprocessed of delta * context * Term.t * Typ.t

let rec completed = function
  | Axiom (_) -> true
  | Node1 ((_) , d) -> completed d
  | Node2 ((_) , d1 , d2) -> completed d1 && completed d2
  | _ -> false

let ctxToString ctx =
  let str = TmHshtbl.fold (fun tm tp s -> (TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp) ^" , "^ s ) ctx "" in
    if String.length str > 0 then String.sub str 0 (String.length str - 2) else str

let thisStep = function
  | Unprocessed (_ , ctx , mv , tp) -> (ctxToString ctx) ^ "⊢ " ^ Term.toString mv ^ (Typ.toString tp)
  | Axiom (_ , ctx , tm , tp) -> (ctxToString ctx) ^ "⊢ " ^ Term.toString tm ^ " : " ^ (Typ.toString tp)
  | Node1 ((_ , ctx , tm , tp) , _) -> (ctxToString ctx) ^ "⊢ " ^ Term.toString tm ^ " : " ^ (Typ.toString tp)
  | Node2 ((_ , ctx , tm , tp) , _ , _) -> (ctxToString ctx) ^ "⊢ " ^ Term.toString tm ^ " : " ^ (Typ.toString tp)

let rec atLevel n drv =
  match (n , drv) with
  | (1 , drv) -> [thisStep drv]
  | (n , drv) when n < 1 -> []
  | (_ , Node1 ((_) , d)) -> atLevel (n - 1) d
  | (_ , Node2 ((_) , d1 , d2)) -> (atLevel (n-1) d1) @ (atLevel (n-1) d2)
  | _ -> []

let rec depth = function
  | Unprocessed _ -> 1
  | Axiom _ -> 1
  | Node1 ((_) , d) -> 1 + depth d
  | Node2 ((_) , d1 , d2) -> 1 + max (depth d1) (depth d2)

let rec repeat a s n =
  match n with
  | 0 -> s
  | _ -> a ^ (repeat a s (n-1))

let rec listToString l s s' =
  match l with
  | [] -> s' ^ "\n" ^ s
  | [x] -> listToString [] (s ^ x) (s' ^ (repeat "-" "" (String.length x)))
  | x :: xs -> listToString xs (s ^ x ^ "      ")  (s' ^ (repeat "-" "" (String.length x)) ^ "      ")

let rec printDrv drv =
  let dpth = depth drv in
  let rec helper n s =
    let s' = listToString (atLevel n drv) "" "" in
    match n with
    | 0 -> s
    | 1 -> s ^ "\n" ^ s'
    | _ ->  helper (n-1) (s ^ "\n" ^ s')
  in
    print_endline (helper dpth "")

let chooseFromCtx ctx1 =
  let ctx2 = TmHshtbl.create 256 in
  let () = print_endline "For each term type 1 if you want it to go to the left context, anything else for the right" in
      TmHshtbl.iter (
        fun tm tp ->
          let () = print_endline ((TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp)) in
          let str = input_line stdin in
          match str with
          | "1" -> ()
          | _ -> TmHshtbl.remove ctx1 tm; TmHshtbl.add ctx2 tm tp
        ) ctx1 ; (ctx1 , ctx2)

let rec getHoleComponents holTerm = function
  | Unprocessed (dt , ctx , h , tp) -> if Term.aequiv holTerm h then Some (dt , ctx , tp) else None
  | Node1 ((_) , d) -> getHoleComponents holTerm d
  | Node2 ((_) , d1 , d2) ->
    (match getHoleComponents holTerm d1 with
      | None -> getHoleComponents holTerm d2
      | Some (dt , ctx , tp) -> Some (dt , ctx , tp))
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
  | Term.Star -> tm

let rec replaceHole oldTermVar newTerm newDrv = function
  | Unprocessed (_ , ctx , h , tp) ->
      if TermVar.equal h oldTermVar
      then newDrv
      else Unprocessed (ctx , h , tp)
  | Node1 ((dt , ctx , tm , tp) , d) ->
      Node1 ((dt , ctx , replaceInTerm oldTermVar newTerm tm, tp) ,
                  replaceHole oldTermVar newTerm newDrv d)
  | Node2 ((dt , ctx , tm , tp) , d1 , d2) ->
      Node2 ((dt , ctx , replaceInTerm oldTermVar newTerm tm , tp) ,
        replaceHole oldTermVar newTerm newDrv d1,
        replaceHole oldTermVar newTerm newDrv d2)
  | Axiom (dt , ctx , tm , tp) -> Axiom (dt , ctx , tm , tp)


let getBottom = function
  | Unprocessed (_ , ctx , mv , tp) -> (ctx , mv , tp)
  | Axiom (_ , ctx , tm , tp) -> (ctx , tm , tp)
  | Node1 ((_ , ctx , tm , tp) , _ ) -> (ctx , tm , tp)
  | Node2 ((_ , ctx , tm , tp) , _ , _) -> (ctx , tm , tp)

let possibleRules ctx tp =
  let idtp = ref 0 in
  let () = TmHshtbl.iter (fun tm tp' -> if Typ.aequiv tp tp' then idtp := !idtp + 1 else ()) ctx in
  let l = if ((!idtp > 0) && (TmHshtbl.length ctx = 1)) then ["I"] else [] in
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
    | Typ.Or (_ , _) -> l@["+right1" ; "+right2" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]


let rec printList = function
    | [] -> print_endline ""
    | x :: xs -> print_string (x ^ " "); printList xs

let rec holes drv holeTerms =
  let () = print_string "Enter the hole you want to work on: " in
  let holnum = read_int () in
  match Hashtbl.mem holeTerms holnum with
  | false -> print_endline "You entered a non-existent hole number. Try again."; holes drv holeTerms
  | true ->
    let holTerm = Hashtbl.find holeTerms holnum in
    let res = getHoleComponents holTerm drv in
    (match res with
      | None -> print_endline "You entered a non-existent hole number. Try again."; holes drv holeTerms
      | Some (dt , ctx , tp) ->
    let () = print_endline (thisStep (Unprocessed (dt , ctx , holTerm , tp))) in
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
                      let origCtx = TmHshtbl.copy ctx in
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
                        (Node2 ((origCtx , newTerm , tp) ,
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
                let () = TmHshtbl.remove ctx tm' in
                let x = TermVar.newT "x" in
                let y = TermVar.newT "y" in
                let () = TmHshtbl.add ctx x a in
                let () = TmHshtbl.add ctx y b in
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
  let (ctx , tm , tp) = getBottom drv in
  match (completed drv , typechecker ctx tm tp) with
  | (true , true) -> print_endline "The proof is complete."
  | (true , false) -> failwith "Construction failure."
  | (false , _) -> holes drv holeTerms

let rec get_context ctx links =
  let () = print_endline "Enter the context:" in
  let str = input_line stdin in
  let lexbuf = Lexing.from_string str in
  let ctxlist = Parser.ctxtmEXP Lexer.exp_token lexbuf in
  let _ = List.map (fun (s , x , a) -> TmHshtbl.add ctx x a; Hashtbl.add links s x; (s , x , a)) ctxlist  in
      (ctx , links)

let makeIdSub ctx =
  let id = Hashtbl.make 256 in
    TmHshtbl.iter (fun k v -> Hashtbl.add id k (Term.into (Term.Var k))) ctx ; id

let main2 (_ : unit) =
  let () = holeCtr := 0 in
  let (ctx , links) = get_context (TmHshtbl.create 256) (Hashtbl.create 256) in
  let () = print_endline "Enter the intended type of the term:" in
  let strtp = input_line stdin in
  let tpbuf = Lexing.from_string strtp in
  let tp = Parser.typEXP Lexer.exp_token tpbuf in
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = TermVar.newT (string_of_int hole1) in
  let hole1ctx = makeIdSub ctx in
  let hole1TM = Term.into (MV (hole1MV , hole1sub)) in
  let dt = Hashtbl.create 256 in
  let () = Hashtbl.add dt hole1TM (hole1ctx , tp) in
  let tree = Unprocessed (dt , ctx , hole1TM , tp) in
  let holeHT = Hashtbl.create 256 in
  let () = Hashtbl.add holeHT hole1 hole1TM in
    proofAssistant tree holeHT
