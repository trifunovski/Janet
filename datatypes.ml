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
    val emptyJudge : context -> ctx
    val singleJudge : context -> ctx
    val commaJudge : ctx -> ctx -> ctx
    val flipJudge : ctx -> ctx
end;;
module Ctx : CONTEXT_JUDGEMENT =
  struct
    type ctx = Context of context

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

  end;;

type ctx = Ctx.ctx

module type EQUIVALENCE =
sig
    type equiv
    val comm : context -> equiv
    val assoc : context -> equiv
    val unitL : context -> equiv
    val unitR : context -> equiv
end
module Equivalence : EQUIVALENCE =
  struct
    open Ctx
    type equiv = Equiv of context * context

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
  end


(*

module type RENAMING =
sig
    type renaming
    val emptyRenaming : unit -> renaming
    val varRenaming : var * var * variance * cat -> renaming
    val commaRenaming : renaming -> renaming -> renaming option
    val idRenaming : context -> renaming
    val compositionRenaming : renaming -> renaming -> renaming option
    val inverseRenaming : renaming -> renaming
    val flipRenaming : renaming -> renaming
end
module Renaming : RENAMING =
  struct
    type rnm = EmptyRenaming
             | SingleRenaming of var * var * variance
             | CommaRenaming of rnm * rnm
             | IdRenaming
             | CompositionRenaming of rnm * rnm
             | InverseRenaming of rnm
             | FlipRenaming of rnm

    type renaming = context * rnm * context

    let rec applyToSubs (f : (var * var * variance) -> (var * var * variance)) r =
      match r with
      | EmptyRenaming -> EmptyRenaming
      | SingleRenaming (x , y , v) -> (match f (x , y , v) with
                                      | (x',y',v') -> SingleRenaming (x',y',v'))
      | CommaRenaming (r1 , r2) -> CommaRenaming (applyToSubs f r1, applyToSubs f r2)
      | IdRenaming -> IdRenaming
      | CompositionRenaming (r1 , r2) ->
          CompositionRenaming (applyToSubs f r1 , applyToSubs f r2)
      | InverseRenaming r1 -> InverseRenaming (applyToSubs f r1)
      | FlipRenaming r1 -> FlipRenaming (applyToSubs f r1)

    let emptyRenaming (_ : unit) = (Context.empty (), EmptyRenaming, Context.empty ())

    let varRenaming (x , y , v , c) =
      (Context.single (x,v,c) , SingleRenaming (x,y,v), Context.single (y,v,c))

    let commaRenaming (psi1 , r1 , psi1') (psi2 , r2 , psi2') =
      match ((Context.comma psi1 psi2) , (Context.comma psi1' psi2')) with
      | (Some psi3 , Some psi4) -> Some (psi3 , CommaRenaming (r1 , r2) , psi4)
      | _ -> None

    let idRenaming (psi : ctx) = (psi , IdRenaming , psi)

    let compositionRenaming r1 r2 =
      match (r1 , r2) with
      | ((psi1 , rnm1 , psi2) , (psi2' , rnm2 , psi3)) when psi2 = psi2' ->
        Some (psi1 , CompositionRenaming (rnm1 , rnm2) , psi3)
      | _ -> None
    let inverseRenaming (psi1 , r , psi2) = (psi2, applyToSubs (fun (x , y , v) -> (y , x , v)) r, psi1)

    let flipRenaming (psi1 , r , psi2) =
          (Context.flip psi1, applyToSubs (fun (x , y , v) -> (x , y, flipVar v)) r,
           Context.flip psi2)
  end;;

module Rename (PSI1 : CONTEXT) (RHO : RENAMING) (PSI2 : CONTEXT) =
  struct

  end

type renaming = Renaming.renaming

let flipRenaming : renaming -> renaming = Renaming.flipRenaming
*)
