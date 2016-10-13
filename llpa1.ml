open Termvar
open Metavar
open Tmhshtbl
open Syntax
open Parser
open Typecheck

type rule =
     | Id of TermVar.t | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli
     | Llolli of TermVar.t | Ltensor of TermVar.t | Lwith1 of TermVar.t
     | Lwith2 of TermVar.t | Lplus of TermVar.t | Lone of TermVar.t

type seq = context * Term.t * Typ.t

type drv = Node of seq * drv list

let rec applyToDrv f = function
  | Node ((ctx , tm , tp) , dl) -> Node ((f (ctx , tm , tp)) , List.map (applyToDrv f) dl)

type hole = Term.t

let holeCtr = ref 0

let makeIdSub ctx =
  let id = TmHshtbl.create 256 in
    TmHshtbl.iter (fun k v -> TmHshtbl.add id k (Term.into (Term.Var k))) ctx ; id

let ctxToString ctx =
  let str = TmHshtbl.fold (fun tm tp s -> (TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp) ^" , "^ s ) ctx "" in
    if String.length str > 0 then String.sub str 0 (String.length str - 2) else str

let thisStep = function
  | Node ((ctx , tm , tp) , _) -> (ctxToString ctx) ^ "⊢ " ^ Term.toString tm ^ " : " ^ (Typ.toString tp)

let rec atLevel n drv =
  match (n , drv) with
  | (1 , drv) -> [thisStep drv]
  | (n , drv) when n < 1 -> []
  | (_ , Node ((_) , dl)) -> List.fold_left (@) [] (List.map (atLevel (n - 1)) dl)

let rec depth = function
  | Node ((_) , []) -> 1
  | Node ((_) , d) -> 1 + List.fold_left (fun x y -> if x > y then x else y) 0 (List.map (depth) d)

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


let rec recurInTerm t mv newTerm =
  let ri = fun t' -> recurInTerm t' mv newTerm in
  match Term.out t with
  | Term.MV (u , sub) when MetaVar.equal u mv -> Term.applySub sub newTerm
  | Term.Lam ((x , tp) , t') -> Term.into (Term.Lam ((x , tp) , ri t'))
  | Term.App (t1 , t2) -> Term.into (Term.App (ri t1 , ri t2))
  | Term.TenPair (t1 , t2) -> Term.into (Term.TenPair (ri t1, ri t2))
  | Term.WithPair (t1 , t2) -> Term.into (Term.WithPair (ri t1, ri t2))
  | Term.Letten (t1 , v , t2) -> Term.into (Term.Letten (ri t1, v , ri t2))
  | Term.Letapp (t1 , v , t2) -> Term.into (Term.Letapp (ri t1, v , ri t2))
  | Term.Letfst (t1 , v , t2) -> Term.into (Term.Letfst (ri t1, v , ri t2))
  | Term.Letsnd (t1 , v , t2) -> Term.into (Term.Letsnd (ri t1, v , ri t2))
  | Term.Inl t' -> Term.into (Term.Inl (ri t'))
  | Term.Inr t' -> Term.into (Term.Inr (ri t'))
  | Term.Case (z , (x , t1 ) , (y , t2)) -> Term.into (Term.Case (z , (x , ri t1) , (y , ri t2)))
  | _ -> t

let rec refineHole (drv : drv) (mv : Term.metaVar) (rule : rule) (dlt : Typecheck.delta) :
      (drv * ((Term.t -> Term.t) * delta) option) =
  match drv with
  | Node ((ctx , tm , tp) , []) ->
      (match Term.out tm with
        | Term.MV (mv' , sub) when MetaVar.equal mv mv' ->
            let (mvCtx , mvTp) = Hashtbl.find dlt mv in
            (match (rule , mvTp) with
              | (Id (tvar) , mvTp) when Typ.aequiv mvTp (TmHshtbl.find mvCtx tvar) ->
                  let newTerm = (Term.into (Term.Var tvar)) in
                  (Node ((ctx , Term.applySub sub newTerm, tp) , []) , Some ((fun t -> recurInTerm t mv newTerm) , dlt))
              | (Rplus1 , Typ.Or (a , b)) ->
                  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
                  let newMV = MetaVar.newT (string_of_int hole1) in
                  let mvTerm = Term.into (Term.MV (newMV , makeIdSub mvCtx)) in
                  let newTerm = (Term.into (Term.Inl (applySub sub mvTerm))) in
                  let () = Hashtbl.add dlt newMV (mvCtx , a) in
                  (Node ((ctx , Term.applySub sub newTerm, Typ.Or (a , b)),
                      [Node ((ctx , mvTerm , a) , [])]) , Some ((fun t -> recurInTerm t mv newTerm) , dlt))
          (*
              | (Rtensor , Typ.Tensor (a , b)) ->

              | (Rplus2 , Typ.Or (a , b)) ->
              | (Rwith , Typ.With (a , b)) ->
              | (Rone , Typ.One) ->
              | (Rlolli , Typ.Lolli (a , b)) ->
              | (Llolli (tvar) , _) ->
              | (Ltensor (tvar) , _) ->
              | (Lwith1 (tvar) , _) ->
              | (Lwith2 (tvar) , _) ->
              | (Lplus (tvar) , _) ->
              | (Lone (tvar) , _) -> *)
              | _ -> failwith "Rule doesn't match the type of the hole."
              )
        | _ -> (Node ((ctx , tm , tp) , []), None))
  | Node ((ctx , tm , tp) , drvs) ->
      let pairs = List.map (fun d -> refineHole d mv rule dlt) drvs in
      let upd = List.fold_left (fun b (_ , res) -> (match (b , res) with
                                                      | (Some _ , _) -> b
                                                      | (None , _) -> res)) None pairs in
      let f = match upd with
              | None -> (fun x -> x)
              | Some (f' , _) -> f' in
            (Node ((ctx , f tm , tp) , List.map (fun (x , y) -> x) pairs) , upd)


(* let rec findBottom holeTM = function
  | Node ((ctx , tm , tp) , []) when Term.aequiv holeTM tm -> Some (ctx , tp)
  | Node ((_) , dl) -> List.fold_left
                          (function | (Some x , _) -> Some x | (_ , Some x) -> Some x | (_ , _) -> None)
                          (None) (List.map (findBottom holeTM) dl)
  | _ -> None


let rec applyToTerm holeTM f tm =
  match Term.out tm with
  | Term.MV (u , sub') when Term.aequiv holeTM tm -> f tm
  | Term.Case (z , (x , t1) , (y , t2)) ->
        Term.into (Term.Case (z, (x ,applyToHoleInTerm holeTM f t1) , (y ,applyToHoleInTerm holeTM f t2)))
  | Term.Lam ((x , tp) , tm') ->
              Term.into (Term.Lam ((x , tp) , applyToHoleInTerm holeTM f tm'))
  | Term.Letten (t1 , v , t2) ->
                Term.into (Term.Letten (applyToHoleInTerm holeTM f t1, v ,applyToHoleInTerm holeTM f t2))
  | Term.Letapp (t1 , v , t2) ->
                Term.into (Term.Letapp (applyToHoleInTerm holeTM f t1, v ,applyToHoleInTerm holeTM f t2))
  | Term.Letfst (t1 , v , t2) ->
                Term.into (Term.Letfst (applyToHoleInTerm holeTM f t1, v ,applyToHoleInTerm holeTM f t2))
  | Term.Letsnd (t1 , v , t2) -> Term.into (Term.Letsnd (applyToHoleInTerm holeTM f t1, v ,applyToHoleInTerm holeTM f t2))
  | Term.App (t1 , t2) -> Term.into (Term.App (applyToHoleInTerm holeTM f sub t1, applyToHoleInTerm holeTM f sub t2))
  | Term.TenPair (t1 , t2) -> Term.into (Term.TenPair (applyToHoleInTerm holeTM f sub t1 , applyToHoleInTerm holeTM f sub t2))
  | Term.WithPair (t1 , t2) -> Term.into (Term.WithPair (applyToHoleInTerm holeTM f t1 , applyToHoleInTerm holeTM f sub t2))
  | Term.Inl tm -> Term.into (Term.Inl (applyToHoleInTerm holeTM f tm))
  | Term.Inr tm -> Term.into (Term.Inr (applyToHoleInTerm holeTM f tm))
  | _ -> tm

*)

let startDrv ctx tp =
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = MetaVar.newT (string_of_int hole1) in
  let hole1sub = makeIdSub ctx in
  let hole1TM = Term.into (Term.MV (hole1MV , hole1sub)) in
  let dt = Hashtbl.create 256 in
  let hole1ctx = TmHshtbl.copy ctx in
  let () = Hashtbl.add dt hole1MV (hole1ctx , tp) in
    (dt , Node ((ctx , hole1TM , tp) , []))

let rec completed = function
  | Node ((_ , tm , _) , []) -> (match Term.out tm with
                                | Term.MV _ -> false
                                | _ -> true)
  | Node ((ctx , tm , tp) , dl) -> List.fold_left (&&) (true) (List.map (completed) dl)
