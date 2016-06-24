type ('a , 'b) either = Inl of 'a | Inr of 'b

type variance = Pos | Neg

type var = string

module Object =
  struct
    type obj
  end
module Arrow =
  struct
    type arr
  end

type obj = Object.obj

type arr = Arrow.arr

module Category =
  struct
    type cat = Category of obj * arr
 (* let empty (_ : unit) =
    let discrete (ob : obj) =
    val id : obj -> arr
    val comp : arr -> arr -> arr *)
  end

type cat = Category.cat

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

(*
let rec belongs (x, v, c) = function
  | Sin (x , v', c') -> v = v' && c = c'
  | Com (psi1 , psi2) -> belongs (x, v, c) psi1 || belongs (x, v, c) psi2
  | _ -> false

module type MEMBERSHIP =
sig
    type member
    val singleMember : term -> member
    val mult1 : member -> context -> member
    val mult2 : context -> member -> member
end;;
module Membership : MEMBERSHIP =
  struct
    type member = Solo of term * context | Mult of term * context * context
    let singleMember (t : term) = Solo (t , Sin t)
    let mult1 (m : member) (psi2 : context) =
      match m with
      | Solo (t , psi1) -> Mult (t , psi1 , psi2)
      | Mult (t , psi1a , psi1b) -> Mult (t , (Com (psi1a , psi1b)) , psi2)
    let mult2 (psi1 : context) (m : member) =
      match m with
      | Solo (t , psi2) -> Mult (t , psi1 , psi2)
      | Mult (t , psi2a , psi2b) -> Mult (t , psi1 , Com (psi2a , psi2b))
  end

*)

module type CONTEXT_JUDGEMENT =
sig
    type ctx
    type equiv
    val emptyJudge : context -> ctx
    val singleJudge : context -> ctx
    val commaJudge : ctx -> ctx -> ctx
    val flipJudge : ctx -> ctx
    val comm : context -> equiv
    val assoc : context -> equiv
    val unitL : context -> equiv
    val unitR : context -> equiv
end;;
module Ctx : CONTEXT_JUDGEMENT =
  struct
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
  end;;

type ctx = Ctx.ctx


module type RENAMING =
sig
    type renaming
    type equivren
    val emptyRenaming : unit -> renaming
    val varRenaming : var * var * variance * cat -> renaming
    val commaRenaming : renaming -> renaming -> renaming
    val idRenaming : context -> renaming
    val compositionRenaming : renaming -> renaming -> renaming
    val inverseRenaming : renaming -> renaming
    val flipRenaming : renaming -> renaming
end
module Renaming : RENAMING =
  struct
    type rnm = EmptyRenaming
             | SingleRenaming of var * var * variance
             | CommaRenaming of rnm * rnm
             | IdRenaming of context
             | CompositionRenaming of rnm * rnm
             | InverseRenaming of rnm
             | FlipRenaming of rnm

    type renaming = Renaming of context * rnm * context
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
    | CompositionRenaming (IdRenaming psi , r) -> EquivRen (CompositionRenaming (IdRenaming psi , r), r)
    | CompositionRenaming (r , IdRenaming psi) -> EquivRen (CompositionRenaming (r , IdRenaming psi), r)
    | CompositionRenaming (CompositionRenaming (r1 , r2) , r3) ->
      EquivRen (CompositionRenaming (CompositionRenaming (r1 , r2) , r3) , CompositionRenaming (r1 , CompositionRenaming (r2,r3)))
  (*  | CompositionRenaming (InverseRenaming r , r') when r = r' -> EquivRen ( , ) *)
    | _ -> failwith "composition equiv renaming"
  end;;

type renaming = Renaming.renaming

let flipRenaming : renaming -> renaming = Renaming.flipRenaming
