open Typecheck
open Syntax
open Parser

type rule =
  Id | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli | Ltensor | Lwith1 | Lwith2 | Lplus | Lone

type delta = (Term.t , (context * Typ.t)) Hashtbl.t

type step = delta * context * Term.t * Typ.t

type drv = Axiom of step
         | Node1 of step * drv
         | Node2 of step * drv * drv
         | Unprocessed of step

type hole = Term.t

let holeCtr = ref 0

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

let getContext () =
  let ctx = TmHshtbl.create 256 in
  let () = print_endline "Enter the context:" in
  let str = input_line stdin in
  let lexbuf = Lexing.from_string str in
  let ctxlist = Parser.ctxtmEXP Lexer.exp_token lexbuf in
  let _ = List.iter (fun (s , x , a) -> TmHshtbl.add ctx x a) ctxlist in
    ctx

let getType () =
  let () = print_endline "Enter the intended type of the term:" in
  let strtp = input_line stdin in
  let tpbuf = Lexing.from_string strtp in
    Parser.typEXP Lexer.exp_token tpbuf

let applySubToVar sub v =
  match TmHshtbl.mem sub v with
  | false -> Term.into (Term.Var v)
  | true -> TmHshtbl.find sub v

let applySubToSub sub sub' =
  let newSub = TmHshtbl.create 256 in
    TmHshtbl.iter (fun k v ->
                        match Term.out v with
                          | Term.Var v' when TmHshtbl.mem sub v' -> TmHshtbl.add newSub k (TmHshtbl.find sub v')
                          | _ -> TmHshtbl.add newSub k v) sub'; newSub

let rec applySub sub tm =
  match Term.out tm with
  | Term.MV (u , sub') -> Term.into (Term.MV (u , applySubToSub sub sub'))
  | Term.Var z -> applySubToVar sub z
  | Term.Case (z , (x , t1) , (y , t2)) ->
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
              Term.into (Term.Case (z, (x , t1') , (y , t2')))
  | Term.Lam ((x , tp) , tm) ->
    let tm' = if TmHshtbl.mem sub x
              then let sub' = TmHshtbl.copy sub in
                   let () = TmHshtbl.remove sub' x in
                      applySub sub' tm
              else applySub sub tm in
              Term.into (Term.Lam ((x , tp) , tm'))
  | Term.Letten (t1 , v , t2) ->
      let t1' = applySub sub t1 in
      let t2' = if TmHshtbl.mem sub v
                then let sub' = TmHshtbl.copy sub in
                     let () = TmHshtbl.remove sub' v in
                        applySub sub' t2
                else applySub sub t2 in
                Term.into (Term.Letten (t1', v , t2'))

  | Term.Letapp (t1 , v , t2) ->
      let t1' = applySub sub t1 in
      let t2' = if TmHshtbl.mem sub v
                then let sub' = TmHshtbl.copy sub in
                     let () = TmHshtbl.remove sub' v in
                        applySub sub' t2
                else applySub sub t2 in
                Term.into (Term.Letapp (t1', v , t2'))

  | Term.Letfst (t1 , v , t2) ->
      let t1' = applySub sub t1 in
      let t2' = if TmHshtbl.mem sub v
                then let sub' = TmHshtbl.copy sub in
                     let () = TmHshtbl.remove sub' v in
                        applySub sub' t2
                else applySub sub t2 in
                Term.into (Term.Letfst (t1', v , t2'))

  | Term.Letsnd (t1 , v , t2) ->
      let t1' = applySub sub t1 in
      let t2' = if TmHshtbl.mem sub v
                then let sub' = TmHshtbl.copy sub in
                     let () = TmHshtbl.remove sub' v in
                        applySub sub' t2
                else applySub sub t2 in
                Term.into (Term.Letsnd (t1', v , t2'))

  | Term.App (t1 , t2) -> Term.into (Term.App (applySub sub t1, applySub sub t2))
  | Term.TenPair (t1 , t2) -> Term.into (Term.TenPair (applySub sub t1 , applySub sub t2))
  | Term.WithPair (t1 , t2) -> Term.into (Term.WithPair (applySub sub t1 , applySub sub t2))
  | Term.Inl tm -> Term.into (Term.Inl (applySub sub tm))
  | Term.Inr tm -> Term.into (Term.Inr (applySub sub tm))
  | _ -> tm

let subIntoHole holeTM newTM =
  match Term.out holeTM with
    | Term.MV (mv , sub) -> applySub sub newTM
    | _ -> failwith "not a valid hole"


let rec refineHole drv holeTM rul = failwith "unimplemented"

let makeIdSub ctx =
  let id = TmHshtbl.create 256 in
    TmHshtbl.iter (fun k v -> TmHshtbl.add id k (Term.into (Term.Var k))) ctx ; id

let startDrv ctx tp =
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = TermVar.newT (string_of_int hole1) in
  let hole1sub = makeIdSub ctx in
  let hole1TM = Term.into (Term.MV (hole1MV , hole1sub)) in
  let dt = Hashtbl.create 256 in
  let hole1ctx = TmHshtbl.copy ctx in
  let () = Hashtbl.add dt hole1TM (hole1ctx , tp) in
    Unprocessed (dt , ctx , hole1TM , tp)

let rec completed = function
  | Axiom (_) -> true
  | Node1 ((_) , d) -> completed d
  | Node2 ((_) , d1 , d2) -> completed d1 && completed d2
  | _ -> false
