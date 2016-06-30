type variance = Pos | Neg

type var = string

type obj = Object

type arr = Arrow

type cat = Category of obj * arr

type term = var * variance * cat

let flipVar (v : variance) = if v = Pos then Neg else Pos

type context = Emp
             | Sin of term
             | Com of context * context

type rnm = EmptyRenaming
         | SingleRenaming of var * var * variance
         | CommaRenaming of rnm * rnm
         | IdRenaming of context
         | CompositionRenaming of rnm * context * rnm
         | InverseRenaming of rnm
         | FlipRenaming of rnm

type unification = Uni of context * context * context * context * rnm * context * rnm

type sub = EmptySub
         | VarSub of var * var * variance
         | CommaSub of sub * sub
         | IdSub of context
         | CompositionSub of sub * context * sub
         | FlipSub of sub

type cat_term = N of var * cat
              | R of var * (rnm * context) * cat
              | S of var * (sub * context) * cat

type tp = Hom of cat * var * var
        | Tensor of tp * tp
        | Limpl of tp * tp
        | End of (var * cat) * tp
        | Coend of (var * cat) * tp

type ctx = Dot
         | Cons of ctx * tp

type seq = Seq of ctx * tp

let bothVars x c = Com (Sin (x , Pos , c) , Sin (x , Neg , c))

let rec flipContext (psi : context) =
  match psi with
  | Emp -> Emp
  | Sin (x , v , c) -> Sin (x , flipVar v , c)
  | Com (psi1 , psi2) -> Com (flipContext psi1 , flipContext psi2)

let rec set_variance (psi : context) (v : variance) =
  match psi with
  | Emp -> Emp
  | Sin (x , _ , c) -> Sin (x , v , c)
  | Com (psi1 , psi2) -> Com (set_variance psi1 v , set_variance psi2 v)

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

let rec context_equiv c1 c2 =
  match (c1 , c2) with
  | (Com (psi1 , psi2) , Com (psi2' , psi1')) when context_equiv psi1 psi1' && context_equiv psi2 psi2' -> true
  | (Com (Com (psi1 , psi2) , psi3), Com (psi1' , Com(psi2' , psi3')))
    when context_equiv psi1 psi1' && context_equiv psi2 psi2' && context_equiv psi3 psi3' -> true
  | (Com (Emp , psi) , psi') when context_equiv psi psi' -> true
  | (Com (psi , Emp) , psi') when context_equiv psi psi' -> true
  | _ -> false

let rec renaming_equiv rn1 rn2 =
  match (rn1 , rn2) with
  | (CommaRenaming (r1 , r2) , CommaRenaming (r2' , r1'))
    when renaming_equiv r1 r1' && renaming_equiv r2 r2' -> true
  | (CommaRenaming (CommaRenaming (r1 , r2) , r3) , CommaRenaming (r1' , CommaRenaming (r2' , r3')))
    when renaming_equiv r1 r1' && renaming_equiv r2 r2' && renaming_equiv r3 r3' -> true
  | (CommaRenaming (EmptyRenaming , r) , r') when renaming_equiv r r' -> true
  | (CommaRenaming (r , EmptyRenaming) , r') when renaming_equiv r r' -> true
  | (IdRenaming Emp , EmptyRenaming) -> true
  | (IdRenaming (Sin (x , v , a)) , SingleRenaming (x' , x'' , v'))
    when x = x' && x' = x'' && v = v' -> true
  | (IdRenaming (Com (psi1 , psi2)), CommaRenaming (IdRenaming psi1' , IdRenaming psi2'))
    when context_equiv psi1 psi1' && context_equiv psi2 psi2' -> true
  | (InverseRenaming EmptyRenaming , EmptyRenaming) -> true
  | (InverseRenaming (SingleRenaming (x , y , v)) , SingleRenaming (y' , x' , v'))
    when x = x' && y = y' && v = v' -> true
  | (InverseRenaming (CommaRenaming (r1 , r2)) , CommaRenaming (InverseRenaming r1' , InverseRenaming r2'))
    when renaming_equiv r1 r1' && renaming_equiv r2 r2' -> true
  | (FlipRenaming EmptyRenaming , EmptyRenaming) -> true
  | (FlipRenaming (SingleRenaming (x , y , v)) , SingleRenaming (x' , y' , vS))
    when x = x' && y = y' && v = flipVar vS -> true
  | (FlipRenaming (CommaRenaming (r1 , r2)) , CommaRenaming (FlipRenaming r1' , FlipRenaming r2'))
    when renaming_equiv r1 r1' && renaming_equiv r2 r2' -> true
  | (CompositionRenaming (EmptyRenaming , _ , r) , EmptyRenaming) -> true
  | (CompositionRenaming (SingleRenaming (x , y , v) , _ , r) , SingleRenaming (z , y' , v'))
    when y = y' && v = v' && renaming_equiv r (SingleRenaming (z , x , v)) -> true
  | (CompositionRenaming (CommaRenaming (r1 , r2) , _ , r') ,
    CommaRenaming (CompositionRenaming (r1' , _  , r1''), CompositionRenaming (r2' , _ , r2'')))
    when renaming_equiv r1 r1' && renaming_equiv r2 r2' && renaming_equiv r' (CommaRenaming (r1'' , r2''))
    -> true
  | (CompositionRenaming (IdRenaming _ , _ , r) , r') when renaming_equiv r r' -> true
  | (CompositionRenaming (r , _ , IdRenaming _) , r') when renaming_equiv r r' -> true
  | (CompositionRenaming (CompositionRenaming (r1 , _ , r2 ) , _ , r3) ,
     CompositionRenaming (r1' , _ , CompositionRenaming (r2' , _ , r3')))
     when renaming_equiv r1 r1' && renaming_equiv r2 r2' && renaming_equiv r3 r3' -> true
  | (CompositionRenaming (r , _ , InverseRenaming r') , IdRenaming _) when renaming_equiv r r' -> true
  | (CompositionRenaming (InverseRenaming r , _ , r') , IdRenaming _) when renaming_equiv r r' -> true
  | (FlipRenaming (FlipRenaming r) , r') when renaming_equiv r r' -> true
  | _ -> false

let rec sub_equiv subst1 subst2 =
  match (subst1 , subst2) with
  | (CommaSub (r1 , r2) , CommaSub (r2' , r1'))
    when sub_equiv r1 r1' && sub_equiv r2 r2' -> true
  | (CommaSub (CommaSub (r1 , r2) , r3) , CommaSub (r1' , CommaSub (r2' , r3')))
    when sub_equiv r1 r1' && sub_equiv r2 r2' && sub_equiv r3 r3' -> true
  | (CommaSub (EmptySub , r) , r') when sub_equiv r r' -> true
  | (CommaSub (r , EmptySub) , r') when sub_equiv r r' -> true
  | (IdSub Emp , EmptySub) -> true
  | (IdSub (Sin (x , v , a)) , VarSub (x' , x'' , v'))
    when x = x' && x' = x'' && v = v' -> true
  | (IdSub (Com (psi1 , psi2)), CommaSub (IdSub psi1' , IdSub psi2'))
    when context_equiv psi1 psi1' && context_equiv psi2 psi2' -> true
  | (FlipSub EmptySub , EmptySub) -> true
  | (FlipSub (VarSub (x , y , v)) , VarSub (x' , y' , vS))
    when x = x' && y = y' && v = flipVar vS -> true
  | (FlipSub (CommaSub (r1 , r2)) , CommaSub (FlipSub r1' , FlipSub r2'))
    when sub_equiv r1 r1' && sub_equiv r2 r2' -> true
  | (CompositionSub (EmptySub , _ , r) , EmptySub) -> true
  | (CompositionSub (VarSub (x , y , v) , _ , r) , VarSub (z , y' , v'))
    when y = y' && v = v' && sub_equiv r (VarSub (z , x , v)) -> true
  | (CompositionSub (CommaSub (r1 , r2) , _ , r') ,
    CommaSub (CompositionSub (r1' , _  , r1''), CompositionSub (r2' , _ , r2'')))
    when sub_equiv r1 r1' && sub_equiv r2 r2' && sub_equiv r' (CommaSub (r1'' , r2''))
    -> true
  | (CompositionSub (IdSub _ , _ , r) , r') when sub_equiv r r' -> true
  | (CompositionSub (r , _ , IdSub _) , r') when sub_equiv r r' -> true
  | (CompositionSub (CompositionSub (r1 , _ , r2 ) , _ , r3) ,
     CompositionSub (r1' , _ , CompositionSub (r2' , _ , r3')))
     when sub_equiv r1 r1' && sub_equiv r2 r2' && sub_equiv r3 r3' -> true
  | (FlipSub (FlipSub r) , r') when sub_equiv r r' -> true
  | _ -> false

let rec cat_term_equiv tm1 tm2 =
  match (tm1 , tm2) with
  | (R (x , (r , _) , a) , N (y , a')) when a = a' && renaming_equiv r (SingleRenaming (y , x , Pos)) -> true
  | (S (x , (s , _) , a) , N (y , a')) when a = a' && sub_equiv s (VarSub (y , x , Pos)) -> true
  | _ -> false

let rec context_type_checker = function
  | Emp -> ()
  | Sin t -> ()
  | Com (psi1 , psi2) when valid psi1 psi2 -> context_type_checker psi1; context_type_checker psi2
  | _ -> failwith "context_type_checker failed"

let rec renaming_type_checker c1 rn c2 =
  match (c1 , rn , c2) with
  | (Emp , EmptyRenaming , Emp) -> ()
  | (Sin (x , v , a) , SingleRenaming (x' , y' , v') , Sin (y , v'' , a')) when
    x = x' && v = v' && v' = v'' && y = y' && a = a' -> ()
  | (Com (psi1 , psi2) , CommaRenaming (r1 , r2)  , Com(psi1' , psi2'))
    -> renaming_type_checker psi1 r1 psi1'; renaming_type_checker psi2 r2 psi2'
  | (psi , IdRenaming psi'' , psi') when context_equiv psi psi' && context_equiv psi psi'' -> ()
  | (psi' , InverseRenaming r , psi) -> renaming_type_checker psi r psi'
  | (psi , FlipRenaming r , psi') -> renaming_type_checker (flipContext psi) r (flipContext psi')
  | (psi , CompositionRenaming (r , psi' , r') , psi'')
    -> renaming_type_checker psi r psi'; renaming_type_checker psi' r' psi''
  | _ -> failwith "renaming_type_checker failed"

let rec unification_type_checker = function
  | Uni (delta1 , Emp , delta2 , Emp , EmptyRenaming , Com (delta1' , delta2') ,
  IdRenaming (Com (delta1'' , delta2''))) when context_equiv delta1 delta1' && context_equiv delta1' delta1''
  && context_equiv delta2 delta2' && context_equiv delta2' delta2'' && isDelta delta1 && isDelta delta2 -> ()
  | Uni (Com (psi1 , Sin (x , vS , a)), Com (psi1' , Sin (x' , v , a')) ,
    Com (psi2 , Sin (y , v' , b)), Com (psi2' , Sin (y' , v'S , b')) ,
    CommaRenaming (r , SingleRenaming (y'' , x'' , vr)) , Com (delta0, Com (Sin (xr , pos , c) , Sin (xr' , neg, c'))),
    CommaRenaming (r0 , CommaRenaming (SingleRenaming (xl , xl' , vlS) , SingleRenaming (xl'' , yl , vl))))
    when x = x' && x' = x'' && x'' = xr && xr = xr' && xr' = xl && xl = xl' && xl' = xl'' &&
    vS = flipVar v && v = v' && v' = flipVar v'S && v' = vr && v'S = vlS && v' = vl &&
    y = y' && y' = y'' && y'' = yl && a = a' && a' = b && b = b' && b' = c && c = c' &&
    isDelta delta0
    -> unification_type_checker (Uni (psi1 , psi1' , psi2 , psi2' , r , delta0 ,r0))
  | _ -> failwith "unification_type_checker failed"

let rec substitution_type_checker c1 subst c2 =
  match (c1 , subst , c2) with
  | (Emp , EmptySub , Emp) -> ()
  | (psi , VarSub (y , x , v) , Sin (x' , v' , a)) when x = x' && v = v'
    -> cat_term_type_checker (set_variance psi v) (N (y , a))
  | (Com (psi1 , psi2) , CommaSub (s1 , s2) , Com (psi1' , psi2'))
    -> substitution_type_checker psi1 s1 psi1'; substitution_type_checker psi2 s2 psi2'
  | (psi , IdSub psi'' , psi') when context_equiv psi psi'' && context_equiv psi'' psi' -> ()
  | (psi , CompositionSub (s , psi' , s') , psi'')
    -> substitution_type_checker psi s psi'; substitution_type_checker psi' s' psi''
  | (psi , FlipSub s , psi') -> substitution_type_checker (flipContext psi) s (flipContext psi')
  | _ -> failwith "substitution_type_checker failed"
and cat_term_type_checker psi t =
  match (psi , t) with
  | (Sin (x , Pos , a) , N (x' , a')) when x = x' && a = a' -> ()
  | (psi , R (x , (r , psi') , a)) -> cat_term_type_checker psi' (N (x , a));
      renaming_type_checker psi r psi'
  | (psi , S (x , (s , psi') , a)) -> cat_term_type_checker psi' (N (x , a));
      substitution_type_checker psi s psi'
  | _ -> failwith "cat_term_type_checker failed"

let rec tp_type_checker psi m =
  match (psi , m) with
  | (Com (Sin (x , Neg , a) , Sin (y , Pos , a')) , Hom (a'' , x' , y'))
    when x = x' && y = y' && a = a' && a' = a'' -> ()
  | (Com (psi1 , psi2) , Tensor (m1 , m2)) -> tp_type_checker psi1 m1; tp_type_checker psi2 m2
  | (Com (psi1 , psi2) , Limpl (m1 , m2)) -> tp_type_checker (flipContext psi1) m1; tp_type_checker psi2 m2
  | (psi , Coend ((x , a) , m)) -> tp_type_checker (Com (psi , bothVars x a)) m
  | (psi , End ((x , a) , m)) -> tp_type_checker (Com (psi , bothVars x a)) m
  | _ -> failwith "tp_type_checker failed"

let rec ctx_type_checker cats tps =
  match (cats , tps) with
  | (Emp , Dot) -> ()
  | (Com (psi1 , psi2) , Cons (gamma , m)) -> ctx_type_checker psi1 gamma; tp_type_checker psi2 m
  | _ -> failwith "ctx_type_checker failed"

let rec seq_type_checker cats sq =
  match (cats , sq) with
  | (Com (psi1 , psi2) , Seq (gamma , m)) -> ctx_type_checker (flipContext psi1) gamma;
    tp_type_checker psi2 m
  | _ -> failwith "seq_type_checker failed"

let rec two_ctx_type_checker delta tps tp =
  match (delta , tps , tp) with
  | (_ , Cons (gamma , Tensor (m1 , m2)) , n) when isDelta delta -> two_ctx_type_checker delta (Cons (Cons (gamma , m1) , m2)) n
  | (_ , _ , Limpl (m , n)) when isDelta delta -> two_ctx_type_checker delta (Cons (tps , m)) n
  | (_ , Cons (gamma , Coend ((x , a) , m)) , n) when isDelta delta ->
    two_ctx_type_checker (Com (delta , bothVars x a)) (Cons (gamma , m)) n
  | (_ , _ , End ((x , a) , m)) when isDelta delta -> two_ctx_type_checker (Com (delta , bothVars x a)) tps m
  | _ -> failwith "two_ctx_type_checker failed"
