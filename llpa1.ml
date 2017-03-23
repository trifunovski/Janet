open Termvar
open Metavar
open Placevar
open Tmhshtbl
open Syntax
open Parser
open Typecheck
open Placerest
open Tmvarrest

exception Unimplemented

type rule =
     | Id of TermVar.t | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli
     | Llolli of TermVar.t | Ltensor of TermVar.t | Lwith1 of TermVar.t
     | Lwith2 of TermVar.t | Lplus of TermVar.t | Lone of TermVar.t

type seq = context * rest * Term.t * Typ.t

type hole = Term.t

let holeCtr = ref 0
let placeCtr = ref 0

let makeIdSub ctx =
  let id = TmHshtbl.create 256 in
    TmHshtbl.iter (fun k v -> TmHshtbl.add id k (Term.into (Term.Var k))) ctx ; id

let ctxToString ctx =
  let str = TmHshtbl.fold (fun tm tp s -> (TermVar.toUserString tm) ^ " : " ^ (Typ.toString tp) ^" , "^ s ) ctx "" in
    if String.length str > 0 then String.sub str 0 (String.length str - 2) else str

let getContext () =
  let ctx = TmHshtbl.create 256 in
  let () = print_endline "Enter the context:" in
  let str = input_line stdin in
  let lexbuf = Lexing.from_string str in
  let ctxlist = Parser.ctxtmEXP Lexer.exp_token lexbuf in
  let _ = List.iter (fun (s , x , a) -> TmHshtbl.add ctx x a) ctxlist in
    (ctx, ctxlist)

let getType () =
  let () = print_endline "Enter the intended type of the term:" in
  let strtp = input_line stdin in
  let tpbuf = Lexing.from_string strtp in
    Parser.typEXP Lexer.exp_token tpbuf


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


let rec listToString = function
    | [] -> ""
    | x :: [] -> x
    | x :: xs -> (x ^ ", ") ^ (listToString xs)

let rec wrap = function
    | Sin (places , vars) -> SetTmVar.fold (fun x xs -> x :: xs) vars []
    | Sub ((p1, v1),((p2, v2) , _)) -> (SetTmVar.fold (fun x xs -> x :: xs) v1 []) @ (SetTmVar.fold (fun x xs -> x :: xs) v2 [])

let rec isIn v = function
    | Sin (places , vars) -> SetPlaceVar.mem v places
    | Sub ((p1, _),((p2, _) , _)) -> SetPlaceVar.mem v p1 || SetPlaceVar.mem v p2

let rec collect v = function
  | [] -> []
  | (eq1 , eq2)::xs ->
      let l = if isIn v eq2 then wrap eq1 else []
      in l@(collect v xs)

let seqToString (ctx, rest, tm, tp) = (ctxToString ctx) ^ " ⊢ " ^ (Term.toString tm) ^ " : " ^ (Typ.toString tp)

let removeHole hlmv str delta hls =
  let () = Hashtbl.remove hls str in
  let () = Hashtbl.remove delta hlmv
  in (hls, delta)

let createHole delta hls tp hlctx rest =
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = MetaVar.newT (string_of_int hole1) in
  let hole1sub = makeIdSub hlctx in
  let hole1TM = Term.into (Term.MV (hole1MV , hole1sub)) in
  let () = Hashtbl.add hls (string_of_int hole1) hole1MV in
  let () = Hashtbl.add delta hole1MV (hlctx , rest , tp)
  in (hole1MV, hole1TM, hls, delta)

let createPlace () =
  let place = placeCtr := !placeCtr + 1; !placeCtr in
  let placePV = PlaceVar.newT (string_of_int place) in
    placePV

let rec createTerm rule hlmv str ctx (r1,r2) htp eqs delta hls =
  match (htp, rule) with
    (Typ.Tensor (t1 , t2), Rtensor) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let (p1 , p2) = (createPlace (), createPlace ()) in
      let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx (SetPlaceVar.add p1 (SetPlaceVar.empty) , SetTmVar.empty) in
      let (hole2MV, hole2TM, hls, delta) = createHole delta hls t2 ctx (SetPlaceVar.add p2 (SetPlaceVar.empty) , SetTmVar.empty) in
      let newTm = Term.into (Term.TenPair (hole1TM, hole2TM)) in
      let newEqs = (Sin (r1,r2) , Sin (SetPlaceVar.add p1 (SetPlaceVar.add p2 (SetPlaceVar.empty)) , SetTmVar.empty)) :: eqs
      in (newTm, newEqs, hls, delta)
  | _ -> raise Unimplemented


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

let rec analyzeHole hls delta (ctx,rest,tm,tp) eqs str =
  let hlmv = Hashtbl.find hls str in
  let (hctx, (r1, r2), htp) = Hashtbl.find delta hlmv in
  let () = print_endline ("You can use the following variables: " ^
          (SetTmVar.fold (fun k s -> s ^ (TermVar.toUserString k) ^ ", ") r2 "")) in
  let () = print_endline ("You can use the following rules: "^ listToString (possibleRules hctx htp)) in
  let () = print_endline ("Select a rule to be applied:") in
  let rule = input_line stdin in
  let (newTm, neweq, newhls, newdelta) = createTerm Rtensor hlmv str hctx (r1,r2) htp eqs delta hls in
    (newhls, newdelta, (ctx,rest,recurInTerm tm hlmv newTm ,tp), neweq)

let rec runStep hls delta drv eqs =
  let () = print_endline "Enter the desired hole #: " in
  let str = input_line stdin in
  match Hashtbl.mem hls str with
    true -> (print_endline("hole "^ str ^ " was selected."); analyzeHole hls delta drv eqs str)
  | false -> (print_endline ("You have entered a non-existing hole. Please try again."); (runStep hls delta drv eqs))


let startSeq ctx ctxlist tp =
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = MetaVar.newT (string_of_int hole1) in
  let hole1sub = makeIdSub ctx in
  let hole1TM = Term.into (Term.MV (hole1MV , hole1sub)) in
  let dt = Hashtbl.create 256 in
  let hls = Hashtbl.create 256 in
  let () = Hashtbl.add hls (string_of_int hole1) hole1MV in
  let hole1ctx = TmHshtbl.copy ctx in
  let () = Hashtbl.add dt hole1MV (hole1ctx , (SetPlaceVar.empty , SetTmVar.of_list (List.map (fun (_,x,_) -> x) ctxlist)) , tp) in
    (hls, dt , (ctx , (SetPlaceVar.empty, SetTmVar.of_list (List.map (fun (_,x,_) -> x) ctxlist)), hole1TM , tp))

let rec completed delta = Hashtbl.length delta = 0

let rec loop (hls,delta,seq,eqs) =
  let () = print_endline (seqToString seq) in
  if completed delta then (hls,delta,seq,eqs)
  else loop(runStep hls delta seq eqs)

let main () =
  let (ctx, ctxlist) = getContext () in
  let tp = getType () in
  let (hls, dlt, seq) = startSeq ctx ctxlist tp
in
  loop (hls, dlt, seq, [])




  (*
  let rec createTerm (r : rule) (mv : Term.metaVar) (dlt : Typecheck.delta) : Term.t option =
  let (mvCtx , mvTp) = Hashtbl.find dlt mv in
    match (r, mvTp) with
      | (Id (tvar) , mvTp) when Typ.aequiv mvTp (TmHshtbl.find mvCtx tvar) ->
          Some (Term.into (Term.Var tvar))
      | (Rtensor , Typ.Tensor (a , b)) ->
      | (Rplus1 , Typ.Or (a , b)) ->
          let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
          let newMV = MetaVar.newT (string_of_int hole1) in
          let mvTerm = Term.into (Term.MV (newMV , makeIdSub mvCtx)) in
          let newTerm = (Term.into (Term.Inl (applySub sub mvTerm))) in
          let () = Hashtbl.add dlt newMV (mvCtx , a) in
            Some newTerm
      | (Rplus2 , Typ.Or (a , b)) ->
          let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
          let newMV = MetaVar.newT (string_of_int hole1) in
          let mvTerm = Term.into (Term.MV (newMV , makeIdSub mvCtx)) in
          let newTerm = (Term.into (Term.Inr (applySub sub mvTerm))) in
          let () = Hashtbl.add dlt newMV (mvCtx , a) in
            Some newTerm
      | (Rwith , Typ.With (a , b)) ->
      | (Rone , Typ.One) -> Some (Term.into (Term.Star))
      | (Rlolli , Typ.Lolli (a , b)) ->
      | (Llolli (tvar) , _) ->
      | (Ltensor (tvar) , _) ->
      | (Lwith1 (tvar) , _) ->
      | (Lwith2 (tvar) , _) ->
      | (Lplus (tvar) , _) ->
      | (Lone (tvar) , _) ->
      | _ -> None
  *)
  (*
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
  *)

  (*

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
