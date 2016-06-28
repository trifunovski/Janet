type ('a , 'b) either = Inl of 'a | Inr of 'b

let (>>) f g x = f(g x)

type variance = Pos | Neg

type var = string

type obj = Object

type arr = Arrow

type cat = Category of obj * arr

type term = var * variance * cat

let flipVar (v : variance) = if v = Pos then Neg else Pos

type context = Emp | Sin of term | Com of context * context

let rec flipContext (psi : context) =
  match psi with
  | Emp -> Emp
  | Sin (x , v , c) -> Sin (x , flipVar v , c)
  | Com (psi1 , psi2) -> Com (flipContext psi1 , flipContext psi2)

let rec no_dups ((x , v , c) : term) (psi : context) =
  match psi with
  | Emp -> true
  | Sin (x' , v' , c') -> if x = x' then c = c' && (v <> v') else true
  | Com (psi1 , psi2) -> no_dups (x , v, c) psi1 && no_dups (x , v , c) psi2

let rec valid (psi1 : context) (psi2 : context) =
  match psi1 with
  | Emp -> true
  | Sin (x , v , c) -> no_dups (x , v , c) psi2
  | Com (psi1a, psi1b) -> valid psi1a psi2 && valid psi1b psi2

let rec validSingleCtx (psi : context) =
  match psi with
  | Emp -> true
  | Sin t -> true
  | Com (psi1 , psi2) -> validSingleCtx psi1 && validSingleCtx psi2 && valid psi1 psi2

let rec deltaHelper (psi : context) (help : context) =
  match psi with
  | Emp -> true
  | Sin (x , v , c) -> not (no_dups (x , flipVar v , c) help)
  | Com (psi1 , psi2) -> deltaHelper psi1 help && deltaHelper psi2 help

let isDelta (psi : context) : bool = deltaHelper psi psi

let isPhi (psi : context) : bool = validSingleCtx psi && isDelta (Com (psi , flipContext psi))

(* CONTEXT WELL-FORMEDNESS *)

type ctx = Context of context

type equiv = Equiv of context * context

let rec flipJudge ((Context (psi)) : ctx) = Context (flipContext psi)

let emptyJudge = function
  | Emp -> Context (Emp)
  | _ -> failwith "Bad context given for empty"

let singleJudge = function
  | Sin t -> Context (Sin t)
  | _ -> failwith "Bad context given for single"

let commaJudge ((Context (psi1)) : ctx) ((Context (psi2)) : ctx) =
  match valid psi1 psi2 with
  | true -> Context (Com (psi1 , psi2))
  | _ -> failwith "contexts are not compatible"

let rec toContext (Context psi) = psi

let comm = function
  | (Com(psi1 , psi2)) -> Equiv (Com (psi1 , psi2) , Com (psi2 , psi1))
  | _ -> failwith "COMMUTATIVITY"

let assoc = function
  | (Com(Com(psi1 , psi2), psi3)) -> Equiv ((Com ((Com (psi1 , psi2)) , psi3)) ,
      (Com (psi1 , (Com (psi2 , psi3)))))
  | _ -> failwith "ASSOCIATIVITY"

let unitL = function
  | Com (Emp , psi) -> Equiv (Com (Emp , psi) , psi)
  | _ -> failwith "UNITLEFT"

let unitR = function
  | Com (psi , Emp) -> Equiv (Com (psi , Emp) , psi)
  | _ -> failwith "UNITRIGHT"

let wellFormedEquiv (Context (psi)) = function
  | Equiv (psi1 , psi2) when psi = psi1 -> Context psi2
  | Equiv (psi1 , psi2) when psi = psi2 -> Context psi1
  | _ -> failwith "WellFormednessEquiv"

(* RENAMINGS *)

type rnm = EmptyRenaming
         | SingleRenaming of var * var * variance
         | CommaRenaming of rnm * rnm
         | IdRenaming of context
         | CompositionRenaming of rnm * rnm
         | InverseRenaming of rnm
         | FlipRenaming of rnm

type renaming_judgment = Renaming of context * rnm * context
type equivren = EquivRen of rnm * rnm

let rec applyToSubs (f : (var * var * variance) -> (var * var * variance)) r =
  match r with
  | EmptyRenaming -> EmptyRenaming
  | SingleRenaming (x , y , v) -> (match f (x , y , v) with
                                  | (x',y',v') -> SingleRenaming (x',y',v'))
  | CommaRenaming (r1 , r2) -> CommaRenaming (applyToSubs f r1, applyToSubs f r2)
  | IdRenaming (psi) -> IdRenaming (psi)
  | CompositionRenaming (r1 , r2) ->
      CompositionRenaming (applyToSubs f r1 , applyToSubs f r2)
  | InverseRenaming r1 -> InverseRenaming (applyToSubs f r1)
  | FlipRenaming r1 -> FlipRenaming (applyToSubs f r1)

let emptyRenaming (_ : unit) = Renaming (Emp, EmptyRenaming, Emp)

let varRenaming (x , y , v , c) =
  Renaming (Sin (x,v,c) , SingleRenaming (x,y,v), Sin (y,v,c))

let commaRenaming (Renaming (psi1 , r1 , psi1')) (Renaming (psi2 , r2 , psi2')) =
  Renaming (Com (psi1 , psi2) , CommaRenaming (r1 , r2) , Com (psi1' , psi2'))

let idRenaming (psi : context) = Renaming (psi , IdRenaming (psi) , psi)

let compositionRenaming r1 r2 =
  match (r1 , r2) with
  | (Renaming (psi1 , rnm1 , psi2) , Renaming (psi2' , rnm2 , psi3)) when psi2 = psi2' ->
    Renaming (psi1 , CompositionRenaming (rnm1 , rnm2) , psi3)
  | _ -> failwith "Bad composition of renamings"
let inverseRenaming (Renaming (psi1 , r , psi2)) = Renaming (psi2, applyToSubs (fun (x , y , v) -> (y , x , v)) r, psi1)

let flipRenaming (Renaming (psi1 , r , psi2)) =
      Renaming (flipContext psi1, applyToSubs (fun (x , y , v) -> (x , y, flipVar v)) r,
       flipContext psi2)

let commRenaming = function
| CommaRenaming (r1 , r2) -> EquivRen (CommaRenaming (r1 , r2) , CommaRenaming (r2 , r1))
| _ -> failwith "commutative renaming fail"

let assocRenaming = function
| CommaRenaming (CommaRenaming (r1,r2), r3) ->
  EquivRen (CommaRenaming (CommaRenaming (r1,r2), r3) , CommaRenaming (r1 , CommaRenaming (r2,r3)))
| _ -> failwith "associtative renaming fail"

let unitLrenaming = function
| CommaRenaming (EmptyRenaming , r) -> EquivRen (CommaRenaming (EmptyRenaming , r) , r)
| _ -> failwith "unitL renaming fail"

let unitRrenaming = function
| CommaRenaming (r , EmptyRenaming) -> EquivRen (CommaRenaming (r , EmptyRenaming) , r)
| _ -> failwith "unitR renaming fail"

let idEquivRenaming = function
| IdRenaming (Emp) -> EquivRen (IdRenaming (Emp) , EmptyRenaming)
| IdRenaming (Sin (x , v , c)) -> EquivRen (IdRenaming (Sin (x , v , c)) , SingleRenaming (x , x , v))
| IdRenaming (Com (psi1 , psi2)) -> EquivRen (IdRenaming (Com (psi1 , psi2)) ,
      CommaRenaming (IdRenaming psi1 , IdRenaming psi2))
| _ -> failwith "Id equiv renaming"

let inverseEquivRenaming = function
| InverseRenaming (EmptyRenaming) -> EquivRen (InverseRenaming (EmptyRenaming) , EmptyRenaming)
| InverseRenaming (SingleRenaming (x , y , v)) -> EquivRen (SingleRenaming (x , y , v) , SingleRenaming (y , x , v))
| InverseRenaming (CommaRenaming (r1 , r2)) ->
  EquivRen (InverseRenaming (CommaRenaming (r1 , r2)) , CommaRenaming (InverseRenaming r1, InverseRenaming r2))
| _ -> failwith "inverse equiv renaming"

let flipEquivRenaming = function
| FlipRenaming (EmptyRenaming) -> EquivRen (FlipRenaming (EmptyRenaming) , EmptyRenaming)
| FlipRenaming (SingleRenaming (x , y , v)) ->
    EquivRen (FlipRenaming (SingleRenaming (x , y , v)) , SingleRenaming (x , y , flipVar v))
| FlipRenaming (CommaRenaming (r1 , r2)) ->
  EquivRen (FlipRenaming (CommaRenaming (r1 , r2)) , CommaRenaming (FlipRenaming r1 , FlipRenaming r2))
| FlipRenaming (FlipRenaming r) -> EquivRen (FlipRenaming (FlipRenaming r) , r)
| _ -> failwith "flip equiv renaming"

let composeEquivRenaming = function
| CompositionRenaming (EmptyRenaming , r) -> EquivRen (CompositionRenaming (EmptyRenaming , r) , EmptyRenaming)
| CompositionRenaming (SingleRenaming (x , y , v) , SingleRenaming (z , x' , v')) when x = x' && v = v' ->
  EquivRen (CompositionRenaming (SingleRenaming (x , y , v) , SingleRenaming (z , x , v)) ,
            SingleRenaming (z , y , v))

| CompositionRenaming (IdRenaming psi , r) -> EquivRen (CompositionRenaming (IdRenaming psi , r), r)
| CompositionRenaming (r , IdRenaming psi) -> EquivRen (CompositionRenaming (r , IdRenaming psi), r)
| CompositionRenaming (CompositionRenaming (r1 , r2) , r3) ->
  EquivRen (CompositionRenaming (CompositionRenaming (r1 , r2) , r3) , CompositionRenaming (r1 , CompositionRenaming (r2,r3)))
(*  | CompositionRenaming (InverseRenaming r , r') when r = r' -> EquivRen ( , ) *)
| _ -> failwith "composition equiv renaming"

(* UNIFICATION *)

type unification = Uni of context * context * context * context * rnm * context * rnm

let uniZero = function
  | (delta1 , delta2) when isDelta delta1 && isDelta delta2
    -> Uni (delta1 , Emp , delta2 , Emp , EmptyRenaming , Com (delta1 , delta2) , IdRenaming (Com (delta1 , delta2)))
  | _ -> failwith "uniZero bad input"

let uniOne = function
  | (Uni (psi1 , psi1' , psi2 , psi2' , r , delta0 , r0) , (x , y , v , a)) when isDelta delta0
    -> Uni (Com (psi1 , Sin (x , flipVar v , a)) , Com (psi1' , Sin (x , v , a)) ,
       Com (psi2 , Sin (y , v , a) ) , Com (psi2' , Sin (y , flipVar v , a)) ,
       CommaRenaming (r , SingleRenaming (y , x , v)) , Com (delta0 , Com (Sin (x , Pos , a) , Sin (x , Neg , a))) ,
       CommaRenaming (r0 , CommaRenaming (SingleRenaming (x , x , flipVar v) , SingleRenaming (x , y , v))))
  | _ -> failwith "uniOne bad input"

(* SUBSTITUTIONS *)

type sub = EmptySub | VarSub of var * var * variance | CommaSub of sub * sub |
  IdSub of context | CompSub of sub * sub | FlipSub of sub
type sub_judgment = Sub of context * sub * context

let emptySub (_ : unit) = Sub (Emp , EmptySub , Emp)

let varSub (s : sub_judgment) = ()

let commaSub (Sub (psi1 , sub1 , psi1') : sub_judgment) (Sub (psi2 , sub2 , psi2') : sub_judgment) =
  Sub (Com (psi1 , psi2) , CommaSub (sub1 , sub2) , Com (psi1' , psi2'))

let idSub (psi : context) = Sub (psi , IdSub psi , psi)

let compSub s1 s2 =
  match (s1 , s2) with
  | (Sub (psi , s' , psi') , Sub(c , s , psi'')) when psi' = c -> Sub (psi , CompSub (s , s') , psi'')
  | _ -> failwith "comp sub fail"

let flipSub (Sub (psi , s , psi')) = Sub (flipContext psi , FlipSub s , flipContext psi')

(* CALCULUS *)

type hom = Hom of term * term | Tensor of hom * hom | Limply of hom * hom | End of term * hom | Coend of term * hom
type tp = Type of hom
type tpctx = Dot | Cons of tpctx * hom
type judgment = J of context * tp
type tc_judgment = TCJ of context * tpctx * hom

let hom_intro = function
  | Com (Sin (x , v , c), Sin (y , v' , c')) when c = c' && v <> v'
      -> J (Com (Sin (x , v , c), Sin (y , v' , c')) , Type (Hom ((x,v,c) , (y,v',c'))))
  | _ -> failwith "hom_intro bad input"

let tensor_intro = function
  | (J (psi1 , Type m1) , J (psi2 , Type m2)) -> J (Com (psi1 , psi2) , Type (Tensor (m1 , m2)))

let coend_intro = function
  | J (Com (psi , Com (Sin (x , v , c) , Sin (x' , v' , c'))) , Type m)
      when x = x' && v <> v' && c = c' -> J (psi , Type (Coend ((x , v , c) , m)))
  | _ -> failwith "coend_intro bad input"

let end_intro = function
  | J (Com (psi , Com (Sin (x , v , c) , Sin (x' , v' , c'))) , Type m)
        when x = x' && v <> v' && c = c' -> J (psi , Type (End ((x , v , c) , m)))
  | _ -> failwith "coend_intro bad input"

let limply_intro = function
  | (J (psi1' , Type m1), J (psi2 , Type m2)) -> J (Com (flipContext psi1' , psi2) , Type (Limply (m1 , m2)))

let hom_intro2 = function
  | (Com (Sin (z , v , c) , Sin (z' , v' , c'))) when z = z' && v <> v' && c = c'
      -> TCJ (Com (Sin (z , v , c) , Sin (z' , v' , c')) , Dot , Hom ((z,v,c),(z',v',c')))
  | _ -> failwith "hom_intro2 bad input"

let tensor_intro2 = function
  | TCJ (delta , Cons (Cons (gamma , m1) , m2) , n) when isDelta delta -> TCJ (delta , Cons (gamma , Tensor (m1,m2)) , n)
  | _ -> failwith "tensor_intro2 bad input"

let coend_intro2 = function
  | TCJ (Com (delta , (Com (Sin (x,v,c) , Sin (x',v',c')))) , Cons (gamma , m) , n) when isDelta delta && x = x' && v <> v' && c = c'
      -> TCJ (delta , Cons (gamma , Coend ((x,v,c),m)), n)
  | _ -> failwith "coend_intro2 bad input"

let end_intro2 = function
  | TCJ (Com (delta , (Com (Sin (x,v,c) , Sin (x',v',c')))) , gamma , m) when isDelta delta && x = x' && v <> v' && c = c'
      -> TCJ (delta , gamma , End ((x , v , c) , m))
  | _ -> failwith "end_intro2 bad input"

let limply_intro2 = function
  | TCJ (delta , Cons (gamma , m) , n) when isDelta delta -> TCJ (delta , gamma , Limply (m , n))
  | _ -> failwith "limply_intro2 bad input"

let tensor_intro3 = function
  | (J (phi1 , Type m1) , J (phi2 , Type m2)) when isPhi phi1 && isPhi phi2 ->
    TCJ (Com (Com (phi1 , flipContext phi1) , Com (phi2 , flipContext phi2) ), Cons (Cons (Dot ,m1) , m2) , Tensor (m1,m2))
  | _ -> failwith "tensor_intro3 bad input"

let coend_intro3 = function
  | J (Com (phi , Com (Sin (x , v , c), Sin (x',v',c'))) , Type m) when x = x' && v <> v' && c = c' && isPhi phi
    -> TCJ (Com (Com (phi , flipContext phi) , Com (Sin (x , v , c), Sin (x',v',c'))) , Cons (Dot , m) , Coend ((x,v,c) , m))
  | _ -> failwith "coend_intro3 bad input"

let end_intro3 = function
  | J (Com (phi , Com (Sin (x , v , c), Sin (x',v',c'))) , Type m) when x = x' && v <> v' && c = c' && isPhi phi
    -> TCJ (Com (Com (phi , flipContext phi) , Com (Sin (x , v , c), Sin (x',v',c'))) , Cons (Dot , End ((x , v, c) , m)) , m)
  | _ -> failwith "end_intro3 bad input"

let limply_intro3 = function
  | (J (phi1 , Type m1) , J (phi2 , Type m2)) when isPhi phi1 && isPhi phi2
    -> TCJ (Com (Com (phi1 , flipContext phi1) , Com (phi2 , flipContext phi2)) , Cons (Cons (Dot , m1) , Limply (m1 , m2) ) , m2)
  | _ -> failwith "limply_intro3 bad input"
