open Termvar
open Metavar
open Placevar
open Tmhshtbl
open Plhshtbl
open Syntax
open Parser
open Typecheck
open Placerest
open Tmvarrest

exception Unimplemented
exception UnmatchedVariable
exception UnknownRule

type rule =
     | Id of TermVar.t | Rtensor | Rplus1 | Rplus2 | Rwith | Rone | Rlolli
     | Llolli of TermVar.t | Ltensor of TermVar.t | Lwith1 of TermVar.t
     | Lwith2 of TermVar.t | Lplus of TermVar.t | Lone of TermVar.t

type seq = context * rest * Term.t * Typ.t

type alpha = (TermVar.t list) PlHshtbl.t

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
        | [(x,tp)] when Typ.aequiv (Typ.Prop a) tp -> ["Id" ; "Xleft" ; "-oleft"; "&left1"; "&left2" ; "+left"; "1left"]
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

let rec createTerm alpha rule hlmv str ctx (r1,r2) htp eqs delta hls =
  match (htp, rule) with
    (Typ.Tensor (t1 , t2), Rtensor) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let (p1 , p2) = (createPlace (), createPlace ()) in
      let () = PlHshtbl.add alpha p1 (SetTmVar.fold (fun k s -> k :: s) r2 []) in
      let () = PlHshtbl.add alpha p2 (SetTmVar.fold (fun k s -> k :: s) r2 []) in
      let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx (SetPlaceVar.add p1 (SetPlaceVar.empty) , SetTmVar.empty) in
      let (hole2MV, hole2TM, hls, delta) = createHole delta hls t2 ctx (SetPlaceVar.add p2 (SetPlaceVar.empty) , SetTmVar.empty) in
      let newTm = Term.into (Term.TenPair (hole1TM, hole2TM)) in
      let newEqs = (Sin (r1,r2) , Sin (SetPlaceVar.add p1 (SetPlaceVar.add p2 (SetPlaceVar.empty)) , SetTmVar.empty)) :: eqs
      in (alpha, newTm, newEqs, hls, delta)
  | (htp , Id x) when (TmHshtbl.mem ctx x && Typ.aequiv htp (TmHshtbl.find ctx x) &&
                      ((not (SetPlaceVar.is_empty r1) && (SetTmVar.is_empty r2) && (SetPlaceVar.fold (fun x f -> PlHshtbl.mem alpha x || f) r1 false))
                      || (SetTmVar.mem x r2 && SetTmVar.cardinal r2 = 1))) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let newTm = Term.into (Term.Var (x)) in
      let () = if (SetTmVar.mem x r2) then SetPlaceVar.iter (fun a -> PlHshtbl.replace alpha a []) r1
               else (SetPlaceVar.iter (fun a -> (PlHshtbl.replace alpha a [x]);
               List.iter (fun (e1,e2) -> match e2 with
                                            Sin (e2p,e2v) -> if SetPlaceVar.mem a e2p then (SetPlaceVar.iter (fun a' -> if a = a' then () else PlHshtbl.replace a' ) e2p) else () 
                                          | _ -> raise Unimplemented)
               eqs) r1)
      in (alpha, newTm, eqs, hls, delta)
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

let rec occurs x = function
  | [] -> false
  | y :: ys -> TermVar.equal x y || occurs x ys

let rec removeDups = function
  | [] -> []
  | x :: xs -> if occurs x xs then removeDups xs else x :: (removeDups xs)

let pick_termvar vars =
  let () = print_endline ("Select the variable to which to apply the rule:") in
  let var = input_line stdin in
  let opt = List.fold_left (fun prev v -> if TermVar.toUserString v = var then Some v else None) None vars in
  match opt with
    Some v -> v
  | None -> raise UnmatchedVariable

let pick_rule vars =
  let () = print_endline ("Select a rule to be applied:") in
  let rule = input_line stdin in
  match rule with
    "Id" -> Id (pick_termvar (vars))
  | "Xleft" -> Ltensor (pick_termvar (vars))
  | "-oleft" -> Llolli (pick_termvar (vars))
  | "&left1" -> Lwith1 (pick_termvar (vars))
  | "&left2" -> Lwith2 (pick_termvar (vars))
  | "+left" -> Lplus (pick_termvar (vars))
  | "1left" -> Lone (pick_termvar (vars))
  | "Xright" -> Rtensor
  | "-oright" -> Rlolli
  | "&right" -> Rwith
  | "+right1" -> Rplus1
  | "+right2" -> Rplus2
  | "1right" -> Rone
  | _ -> raise UnknownRule

let rec analyzeHole alpha hls delta (ctx,rest,tm,tp) eqs str =
  let hlmv = Hashtbl.find hls str in
  let (hctx, (r1, r2), htp) = Hashtbl.find delta hlmv in
  let l = SetPlaceVar.fold (fun k s -> (Hashtbl.find alpha k)@s) r1 [] in
  let l2 = SetTmVar.fold (fun k s -> k :: s) r2 [] in
  let vars = (removeDups(l@l2)) in
  let () = print_endline ("You can use the following variables: " ^ (listToString (List.map (fun k -> TermVar.toUserString k) vars))) in
  let () = print_endline ("You can use the following rules: "^ listToString (possibleRules hctx htp)) in
  let rule = pick_rule vars in
  let (newAlpha, newTm, neweq, newhls, newdelta) = createTerm alpha rule hlmv str hctx (r1,r2) htp eqs delta hls in
    (newAlpha, newhls, newdelta, (ctx,rest,recurInTerm tm hlmv newTm ,tp), neweq)

let rec runStep alpha hls delta drv eqs =
  let () = print_endline "Enter the desired hole #: " in
  let str = input_line stdin in
  match Hashtbl.mem hls str with
    true -> (print_endline("hole "^ str ^ " was selected."); analyzeHole alpha hls delta drv eqs str)
  | false -> (print_endline ("You have entered a non-existing hole. Please try again."); (runStep alpha hls delta drv eqs))


let startSeq ctx ctxlist tp =
  let hole1 = holeCtr := !holeCtr + 1; !holeCtr in
  let hole1MV = MetaVar.newT (string_of_int hole1) in
  let hole1sub = makeIdSub ctx in
  let hole1TM = Term.into (Term.MV (hole1MV , hole1sub)) in
  let dt = Hashtbl.create 256 in
  let hls = Hashtbl.create 256 in
  let alpha = PlHshtbl.create 256 in
  let () = Hashtbl.add hls (string_of_int hole1) hole1MV in
  let hole1ctx = TmHshtbl.copy ctx in
  let () = Hashtbl.add dt hole1MV (hole1ctx , (SetPlaceVar.empty , SetTmVar.of_list (List.map (fun (_,x,_) -> x) ctxlist)) , tp) in
    (alpha, hls, dt , (ctx , (SetPlaceVar.empty, SetTmVar.of_list (List.map (fun (_,x,_) -> x) ctxlist)), hole1TM , tp))

let rec completed delta = Hashtbl.length delta = 0

let rec loop (alpha,hls,delta,seq,eqs) =
  let () = print_endline (seqToString seq) in
  if completed delta then let () = print_endline("We are done!") in (alpha,hls,delta,seq,eqs)
  else loop(runStep alpha hls delta seq eqs)

let main () =
  let (ctx, ctxlist) = getContext () in
  let tp = getType () in
  let (alpha, hls, dlt, seq) = startSeq ctx ctxlist tp
in
  loop (alpha, hls, dlt, seq, [])


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
