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
     | MV of MetaVar.t

type seq = context * rest * Term.t * Typ.t

type hole = Term.t

module SS = Set.Make(String)

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


let possibleRules ctx r tp =
  let s = SS.empty in
  let idtp = ref 0 in
  let s = SetTmVar.fold (fun tm s' ->
            let s'' = if Typ.aequiv tp (TmHshtbl.find ctx tm) then SS.add ("Id") s' else s' in
            match TmHshtbl.find ctx tm with
              | Typ.Tensor (t1 , t2) -> SS.add "Xleft" s''
              | Typ.One -> SS.add "1left" s''
              | Typ.Lolli (_ , _) -> SS.add "-oleft" s''
              | Typ.With (_ , _) -> SS.add "&left1" (SS.add "&left2" s'')
              | Typ.Or (_ , _) -> SS.add "+left" s''
              | _ -> s''
            ) r s in
  let s = match tp with
    | Typ.Tensor (t1 , t2) -> SS.add "Xright" s
    | Typ.One -> SS.add "1right" s
    | Typ.Lolli (_ , _) -> SS.add "-oright" s
    | Typ.With (_ , _) -> SS.add "&right" s
    | Typ.Or (_ , _) -> SS.add "+right1" (SS.add "+right2" s)
    | _ -> s in
    SS.fold (fun x l -> x :: l) s []


let rec listToString = function
    | [] -> ""
    | x :: [] -> x
    | x :: xs -> (x ^ ", ") ^ (listToString xs)

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

let createPlace alpha ctxSet =
  let place = placeCtr := !placeCtr + 1; !placeCtr in
  let plPV = PlaceVar.newT (string_of_int place) in
  let () = PlHshtbl.add alpha plPV ctxSet in
    (alpha, plPV)

let rec fixEqs2 tot alpha r set = function
  [] -> alpha
| eq :: eqs -> (match eq with
            | Union (a, (a1,a2)) when PlaceVar.equal a r ->
                    let () = PlHshtbl.replace alpha a1 (SetTmVar.diff (PlHshtbl.find alpha a1) set) in
                    let () = PlHshtbl.replace alpha a2 (SetTmVar.diff (PlHshtbl.find alpha a2) set) in
                    let alpha = fixEqs2 tot alpha a1 set tot
                    in fixEqs2 tot alpha a2 set tot
            | Sub (a, (a1, (f,a2,x))) when PlaceVar.equal a r ->
                    let () = PlHshtbl.replace alpha a1 (SetTmVar.diff (PlHshtbl.find alpha a1) set) in
                    let () = PlHshtbl.replace alpha a2 (SetTmVar.diff (PlHshtbl.find alpha a2) set) in
                    let alpha = fixEqs2 tot alpha a1 set tot
                    in fixEqs2 tot alpha a2 set tot
            | _ -> fixEqs2 tot alpha r set eqs)

let rec fixEqs tot alpha r set = function
  [] -> alpha
| eq :: eqs -> (match eq with
            | Union (a, (a1,a2)) when PlaceVar.equal a1 r ->
                    let () = PlHshtbl.replace alpha a2 (SetTmVar.diff (PlHshtbl.find alpha a2) set) in
          (*           let () = PlHshtbl.replace alpha a (SetTmVar.diff (PlHshtbl.find alpha a) set) in *)
                    let alpha = fixEqs2 tot alpha a2 set tot
                    in fixEqs tot alpha a set tot
            | Union (a, (a1,a2)) when PlaceVar.equal a2 r ->
                    let () = PlHshtbl.replace alpha a1 (SetTmVar.diff (PlHshtbl.find alpha a1) set) in
              (*      let () = PlHshtbl.replace alpha a (SetTmVar.diff (PlHshtbl.find alpha a) set) in *)
                    let alpha = fixEqs2 tot alpha a1 set tot
                    in fixEqs tot alpha a set tot
            | Sub (a, (a1, (f,a2,x))) when PlaceVar.equal a1 r ->
                    let set = (SetTmVar.diff set (SetTmVar.singleton x)) in
                    let () = PlHshtbl.replace alpha a2 (SetTmVar.diff (PlHshtbl.find alpha a2) set) in
              (*      let () = PlHshtbl.replace alpha a (SetTmVar.diff (PlHshtbl.find alpha a) set) in *)
                    let alpha = fixEqs2 tot alpha a2 set tot
                    in fixEqs tot alpha a set tot
            | Sub (a, (a1, (f,a2,x))) when PlaceVar.equal a2 r ->
                    let () = PlHshtbl.replace alpha a1 (SetTmVar.diff (PlHshtbl.find alpha a1) set) in
          (*          let () = PlHshtbl.replace alpha a (SetTmVar.diff (PlHshtbl.find alpha a) set) in *)
                    let alpha = fixEqs2 tot alpha a1 set tot
                    in fixEqs tot alpha a set tot
            | Link (a , (a' , (z , x))) when PlaceVar.equal a' r ->
                    let set = if SetTmVar.is_empty (SetTmVar.inter set x)
                              then set
                              else SetTmVar.union (SetTmVar.diff set x) z
                  (*  let () = PlHshtbl.replace alpha a (SetTmVar.diff (PlHshtbl.find alpha a) set) *)
                    in fixEqs tot alpha a set tot
            | _ -> fixEqs tot alpha r set eqs)

let rec createTerm alpha rule hlmv str ctx r htp eqs delta hls =
  match (htp, rule) with
    (htp, MV u) ->
      let a = r in
      let (hls , delta) = removeHole hlmv str delta hls in
      let (gamma0 , alpha0 , atp) = Hashtbl.find delta u in
      let restCtx = PlHshtbl.find alpha a in
      let z = TermVar.newT "z" in
      let restCtx = SetTmVar.add z restCtx in
      let (alpha , a') = createPlace alpha restCtx in
      let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp ctx a' in
      let (hole0MV, hole0TM, hls, delta) = createHole delta hls atp gamma0 a in
      let newTm = Term.into (Term.Letmv (z , hole0TM , hole1TM)) in
      let newEqs = Mv (a , (a' , (alpha0 , makeIdSub gamma0 , z))) :: eqs in
      let alpha = alpha (* fixEqs newEqs alpha r (SetTmVar.singleton x) newEqs *)
      in (alpha, newTm, newEqs, hls, delta)
  | (Typ.Tensor (t1 , t2), Rtensor) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let restCtx = PlHshtbl.find alpha r in
      let (alpha , p1) = createPlace alpha restCtx in
      let (alpha , p2) = createPlace alpha restCtx in
      let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx p1 in
      let (hole2MV, hole2TM, hls, delta) = createHole delta hls t2 ctx p2 in
      let newTm = Term.into (Term.TenPair (hole1TM, hole2TM)) in
      let newEqs = (Union (r , (p1 , p2))) :: eqs
      in (alpha, newTm, newEqs, hls, delta)
  | (htp, Ltensor x) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let (Typ.Tensor(t1,t2)) = TmHshtbl.find ctx x in
      let restCtx = PlHshtbl.find alpha r in
    (*  let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton x)) in *)
      let x1 = TermVar.newT "x1" in
      let x2 = TermVar.newT "x2" in
      let restCtx = SetTmVar.add (x1) (SetTmVar.add (x2) (SetTmVar.remove x restCtx)) in
      let (alpha , p1) = createPlace alpha restCtx in
      let holectx = TmHshtbl.copy ctx in
      let () = TmHshtbl.add holectx x1 t1 in
      let () = TmHshtbl.add holectx x2 t2 in
      let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp holectx p1 in
      let newTm = Term.into (Term.Letten (Term.into(Term.TenPair(Term.into(Term.Var x1),Term.into(Term.Var x2))), Term.into(Term.Var x), hole1TM)) in
      let newEqs = Link (r , (p1 , (SetTmVar.singleton (x) , SetTmVar.add x1 (SetTmVar.singleton x2)))) :: eqs in
      let alpha = fixEqs newEqs alpha r (SetTmVar.singleton x) newEqs
      in (alpha, newTm, newEqs, hls, delta)
  | (htp , Id x) when SetTmVar.mem x (PlHshtbl.find alpha r) && Typ.aequiv htp (TmHshtbl.find ctx x) ->
      let (hls , delta) = removeHole hlmv str delta hls in
      let newTm = Term.into (Term.Var (x)) in
      let () = PlHshtbl.replace alpha r (SetTmVar.singleton x) in
  (*    let () = PlHshtbl.replace alpha r (SetTmVar.diff (PlHshtbl.find alpha r) (SetTmVar.singleton x)) in *)
      let alpha = fixEqs eqs alpha r (SetTmVar.singleton x) eqs
      in (alpha, newTm, eqs, hls, delta)
  | (Typ.One , Rone) ->
        let (hls , delta) = removeHole hlmv str delta hls in
        let () = PlHshtbl.replace alpha r (SetTmVar.empty) in
        let newTm = Term.into (Term.Star)
        in (alpha, newTm, eqs, hls, delta)
  | (htp , Lone z) ->
        let (hls , delta) = removeHole hlmv str delta hls in
        let (Typ.One) = TmHshtbl.find ctx z in
        let restCtx = PlHshtbl.find alpha r in
    (*    let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton z)) in *)
        let restCtx = SetTmVar.remove z restCtx in
        let (alpha , p1) = createPlace alpha restCtx in
        let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp ctx p1 in
        let newTm = Term.into (Term.Letone (Term.into(Term.Star), Term.into (Term.Var z), hole1TM)) in
        let newEqs = Link (r , (p1, (SetTmVar.singleton z , SetTmVar.empty))) :: eqs in
        let alpha = fixEqs newEqs alpha r (SetTmVar.singleton z) newEqs
        in (alpha, newTm, newEqs, hls, delta)
  | (Typ.Lolli (t1 , t2), Rlolli) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let restCtx = PlHshtbl.find alpha r in
    let x = TermVar.newT "x" in
    let (alpha , p1) = createPlace alpha (SetTmVar.add x restCtx) in
    let holectx = TmHshtbl.copy ctx in
    let () = TmHshtbl.add holectx x t1 in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls t2 holectx p1 in
    let newTm = Term.into (Term.Lam((x,t1),hole1TM)) in
    let newEqs = Link (r , (p1 , (SetTmVar.empty , SetTmVar.singleton x))) :: eqs
    in (alpha, newTm, newEqs, hls, delta)
  | (htp, Llolli f) ->
  (* REMOVE THE f FROM OTHER PLACES RIGHT NOW!!! fixEqs with singleton f *)
    let (hls , delta) = removeHole hlmv str delta hls in
    let (Typ.Lolli(t1,t2)) = TmHshtbl.find ctx f in
    let restCtx = PlHshtbl.find alpha r in
  (*  let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton f)) in *)
    let x = TermVar.newT "x" in
    let restCtx1 = SetTmVar.remove f restCtx in
    let restCtx2 = SetTmVar.add x restCtx1 in
    let (alpha , p1) = createPlace alpha restCtx1 in
    let (alpha , p2) = createPlace alpha restCtx2 in
    let holectx2 = TmHshtbl.copy ctx in
    let () = TmHshtbl.add holectx2 x t2 in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx p1 in
    let (hole2MV, hole2TM, hls, delta) = createHole delta hls htp holectx2 p2 in
    let newTm = Term.into (Term.Letapp (x, Term.into (Term.App (Term.into (Term.Var f) , hole1TM)) , hole2TM)) in
    let newEqs = Sub (r , (p2 , (f , p1 , x))) :: eqs in
    let alpha = fixEqs newEqs alpha r (SetTmVar.singleton f) newEqs
    in (alpha, newTm, newEqs, hls, delta)
  | (Typ.Or(t1,t2), Rplus1) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let restCtx = PlHshtbl.find alpha r in
    let (alpha , p1) = createPlace alpha restCtx in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx p1 in
    let newTm = Term.into (Term.Inl (hole1TM)) in
    let newEqs = Link(r,(p1 , (SetTmVar.empty , SetTmVar.empty))) :: eqs
    in (alpha, newTm, newEqs, hls, delta)
  | (Typ.Or(t1,t2), Rplus2) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let restCtx = PlHshtbl.find alpha r in
    let (alpha , p1) = createPlace alpha restCtx in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx p1 in
    let newTm = Term.into (Term.Inr (hole1TM)) in
    let newEqs = Link(r,(p1 , (SetTmVar.empty , SetTmVar.empty))) :: eqs
    in (alpha, newTm, newEqs, hls, delta)
  | (htp, Lplus z) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let (Typ.Or(t1,t2)) = TmHshtbl.find ctx z in
    let restCtx = PlHshtbl.find alpha r in
  (*  let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton z)) in *)
    let x = TermVar.newT "x" in
    let y = TermVar.newT "y" in
    let restCtx1 = SetTmVar.add x (SetTmVar.remove z restCtx) in
    let restCtx2 = SetTmVar.add y (SetTmVar.remove z restCtx) in
    let (alpha , p1) = createPlace alpha restCtx1 in
    let (alpha , p2) = createPlace alpha restCtx2 in
    let holectx1 = TmHshtbl.copy ctx in
    let holectx2 = TmHshtbl.copy ctx in
    let () = TmHshtbl.add holectx1 x t1 in
    let () = TmHshtbl.add holectx2 y t2 in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp holectx1 p1 in
    let (hole2MV, hole2TM, hls, delta) = createHole delta hls htp holectx2 p2 in
    let newTm = Term.into (Term.Case (z , (x, hole1TM), (y, hole2TM))) in
    let newEqs = Link (r , (p1,(SetTmVar.singleton z,SetTmVar.singleton x))) :: Link (r , (p2 , (SetTmVar.singleton z,SetTmVar.singleton y))) :: eqs in
    let alpha = fixEqs newEqs alpha r (SetTmVar.singleton z) newEqs
    in (alpha, newTm, newEqs, hls, delta)
  | (Typ.With(t1,t2), Rwith) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let restCtx = PlHshtbl.find alpha r in
    let (alpha , p1) = createPlace alpha restCtx in
    let (alpha , p2) = createPlace alpha restCtx in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls t1 ctx p1 in
    let (hole2MV, hole2TM, hls, delta) = createHole delta hls t2 ctx p2 in
    let newTm = Term.into (Term.WithPair (hole1TM, hole2TM)) in
    let newEqs = Link (r , (p1 , (SetTmVar.empty , SetTmVar.empty))) :: Link (r , (p2 , (SetTmVar.empty, SetTmVar.empty))) ::eqs
    in (alpha, newTm, newEqs, hls, delta)
  | (htp , Lwith1 z) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let (Typ.With(t1,t2)) = TmHshtbl.find ctx z in
    let restCtx = PlHshtbl.find alpha r in
  (*  let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton z)) in *)
    let x = TermVar.newT "x" in
    let dummy = TermVar.newT "_" in
    let restCtx = SetTmVar.add (x) (SetTmVar.remove z restCtx) in
    let (alpha , p1) = createPlace alpha restCtx in
    let holectx = TmHshtbl.copy ctx in
    let () = TmHshtbl.add holectx x t1 in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp holectx p1 in
    let newTm = Term.into (Term.Letfst (Term.into(Term.WithPair(Term.into(Term.Var x),Term.into(Term.Var dummy))), Term.into (Term.Var z), hole1TM)) in
    let newEqs = Link (r , (p1 , (SetTmVar.singleton z , SetTmVar.singleton x))) :: eqs in
    let alpha = fixEqs newEqs alpha r (SetTmVar.singleton z) newEqs
    in (alpha, newTm, newEqs, hls, delta)
  | (htp , Lwith2 z) ->
    let (hls , delta) = removeHole hlmv str delta hls in
    let (Typ.With(t1,t2)) = TmHshtbl.find ctx z in
    let restCtx = PlHshtbl.find alpha r in
  (*  let () = PlHshtbl.replace alpha r (SetTmVar.diff restCtx (SetTmVar.singleton z)) in *)
    let x = TermVar.newT "x" in
    let dummy = TermVar.newT "_" in
    let restCtx = SetTmVar.add (x) (SetTmVar.remove z restCtx) in
    let (alpha , p1) = createPlace alpha restCtx in
    let holectx = TmHshtbl.copy ctx in
    let () = TmHshtbl.add holectx x t2 in
    let (hole1MV, hole1TM, hls, delta) = createHole delta hls htp holectx p1 in
    let newTm = Term.into (Term.Letsnd (Term.into(Term.WithPair(Term.into(Term.Var dummy),Term.into(Term.Var x))), Term.into (Term.Var z), hole1TM)) in
    let newEqs = Link (r , (p1 , (SetTmVar.singleton z , SetTmVar.singleton x))) :: eqs in
    let alpha = fixEqs newEqs alpha r (SetTmVar.singleton z) newEqs
    in (alpha, newTm, newEqs, hls, delta)
  | _ -> raise Unimplemented


let rec recurInTerm t mv newTerm =
  let ri = fun t' -> recurInTerm t' mv newTerm in
  match Term.out t with
  | Term.MV (u , sub) when MetaVar.equal u mv -> Term.applySub sub newTerm
  | Term.Lam ((x , tp) , t') -> Term.into (Term.Lam ((x , tp) , ri t'))
  | Term.App (t1 , t2) -> Term.into (Term.App (ri t1 , ri t2))
  | Term.TenPair (t1 , t2) -> Term.into (Term.TenPair (ri t1, ri t2))
  | Term.WithPair (t1 , t2) -> Term.into (Term.WithPair (ri t1, ri t2))
  | Term.Letone (t1 , t2 , t3) -> Term.into (Term.Letone (t1, t2 , ri t3))
  | Term.Letten (t1 , t2 , t3) -> Term.into (Term.Letten (t1, t2 , ri t3))
  | Term.Letapp (f , t2 , t3) -> Term.into (Term.Letapp (f, ri t2 , ri t3))
  | Term.Letfst (t1 , t2 , t3) -> Term.into (Term.Letfst (t1, t2 , ri t3))
  | Term.Letsnd (t1 , t2 , t3) -> Term.into (Term.Letsnd (t1, t2 , ri t3))
  | Term.Letmv (z , t2 , t3) -> Term.into (Term.Letmv (z, ri t2, ri t3))
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
(*  let () = print_endline ("Printing current vars: " ^ listToString (List.map (fun k -> TermVar.toString k) vars)) in *)
  let opt = List.fold_left (fun prev v -> if TermVar.toString v = var then Some v else prev) None vars in
  match opt with
    Some v -> v
  | None -> raise UnmatchedVariable

let pick_metavar mvs =
  let () = print_endline ("Select the meta-variable to which to apply the rule:") in
  let var = input_line stdin in
  let opt = List.fold_left (fun prev v -> if MetaVar.toString v = var then Some v else prev) None mvs in
  match opt with
    Some v -> v
  | None -> raise UnmatchedVariable

let pick_rule vars mvs =
  let () = print_endline ("Select a rule to be applied:") in
  let rule = input_line stdin in
  match rule with
    "Id" -> Id (pick_termvar (vars))
  | "MV" -> MV (pick_metavar (mvs))
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
  let (hctx, r, htp) = Hashtbl.find delta hlmv in
  let mvs = Hashtbl.fold (fun k v l -> k::l) delta [] in
  let l = SetTmVar.fold (fun k s -> k::s) (PlHshtbl.find alpha r) [] in
  let () = print_endline ("You can use the following variables: " ^ (listToString (List.map (fun k -> (TermVar.toString k) ^ " : " ^ (Typ.toString(TmHshtbl.find hctx k))) l))) in
  let () = print_endline ("You can use the following meta-variables: " ^ (listToString (List.map (fun k -> (MetaVar.toString k)) mvs))) in
  let () = print_endline ("You can use the following rules: "^ (listToString ("MV"::(possibleRules hctx (PlHshtbl.find alpha r) htp)))) in
  let rule = pick_rule l mvs in
  let (newAlpha, newTm, neweq, newhls, newdelta) = createTerm alpha rule hlmv str hctx r htp eqs delta hls in
    (newAlpha, newhls, newdelta, (ctx,rest,recurInTerm tm hlmv newTm ,tp), neweq)

let rec runStep alpha hls delta drv eqs =
  let () = print_endline "Enter the desired hole #: " in
  let str = input_line stdin in
  match Hashtbl.mem hls str with
    true ->
        let hlmv = Hashtbl.find hls str in
        let (hctx, r, htp) = Hashtbl.find delta hlmv in
        (print_endline("Hole "^ str ^ " was selected, with type "^ Typ.toString htp ); analyzeHole alpha hls delta drv eqs str)
  | false -> (print_endline ("You have entered a non-existing hole. Please try again."); (runStep alpha hls delta drv eqs))

let startSeq ctx ctxlist tp =
  let dt = Hashtbl.create 256 in
  let hls = Hashtbl.create 256 in
  let alpha = PlHshtbl.create 256 in
  let (alpha, plPV) = createPlace alpha (SetTmVar.of_list (List.map (fun (_,x,_) -> x)ctxlist)) in
  let (hole1MV, hole1TM, hls, delta) = createHole dt hls tp ctx plPV in
    (alpha, hls, delta , (ctx , plPV, hole1TM , tp))

let rec completed delta = Hashtbl.length delta = 0

let rec checkEqs alpha = function
  | [] -> true
  | Union (a , (a1, a2)) :: eqs -> SetTmVar.is_empty(SetTmVar.inter (PlHshtbl.find alpha a1) (PlHshtbl.find alpha a2))
                                && SetTmVar.cardinal(SetTmVar.inter (PlHshtbl.find alpha a) (SetTmVar.union (PlHshtbl.find alpha a1) (PlHshtbl.find alpha a2)))
                                = SetTmVar.cardinal (PlHshtbl.find alpha a) && checkEqs alpha eqs
  | Sub (a , (a2 , (f , a1 , z))) :: eqs -> SetTmVar.is_empty(SetTmVar.inter (PlHshtbl.find alpha a1) (PlHshtbl.find alpha a2))
                                && SetTmVar.cardinal (SetTmVar.inter (SetTmVar.union (SetTmVar.diff (PlHshtbl.find alpha a2) (SetTmVar.singleton z))
                                      (SetTmVar.union (SetTmVar.singleton f) (PlHshtbl.find alpha a1))) (PlHshtbl.find alpha a))
                                      = SetTmVar.cardinal (PlHshtbl.find alpha a) && checkEqs alpha eqs
  | Link (a , (a' , (x , z))) :: eqs -> SetTmVar.cardinal (SetTmVar.inter (PlHshtbl.find alpha a) (SetTmVar.union (SetTmVar.diff
                                              (PlHshtbl.find alpha a') z) x)) = SetTmVar.cardinal (PlHshtbl.find alpha a)
                                    && checkEqs alpha eqs
  | Mv (a , (a' , (a0 , gam , x))) :: eqs -> checkEqs alpha eqs

let rec loop ((alpha,hls,delta,(ctx,rest,tm,tp),eqs), startRes) =
  let _ = Sys.command "clear" in
  let () = print_endline (seqToString (ctx,rest,tm,tp)) in
  if completed delta
  then
      let () = (* if (PlHshtbl.fold (fun k v r -> SetTmVar.cardinal v + r) alpha 0) = 0 *)
               if checkEqs alpha eqs && SetTmVar.cardinal (SetTmVar.inter (PlHshtbl.find alpha rest) (startRes)) = SetTmVar.cardinal startRes
               then print_endline("We are done!")
               else print_endline("We didn't use up all resources...") (* ^ (PlHshtbl.fold (fun k v r ->
                  (SetTmVar.fold (fun tm s -> (TermVar.toString tm) ^ ", " ^ s) v ("..from "^ PlaceVar.toString k ^"\n")) alpha "") )) *)
      in ((alpha,hls,delta,(ctx,rest,tm,tp),eqs),startRes)
  else loop(runStep alpha hls delta (ctx,rest,tm,tp) eqs, startRes)

let main () =
  let (ctx, ctxlist) = getContext () in
  let tp = getType () in
  let (alpha, hls, dlt, (ctx , plPV, hole1TM , tp)) = startSeq ctx ctxlist tp in
  let startRes = PlHshtbl.find alpha plPV
in
  loop ((alpha, hls, dlt, (ctx , plPV, hole1TM , tp), []) , startRes)

let run () =
  let _ = Sys.command "clear" in
  let res = main () in ()
