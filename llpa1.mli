exception Unimplemented
exception UnmatchedVariable
exception UnknownRule
type rule =
    Id of Termvar.TermVar.t
  | Rtensor
  | Rplus1
  | Rplus2
  | Rwith
  | Rone
  | Rlolli
  | Llolli of Termvar.TermVar.t
  | Ltensor of Termvar.TermVar.t
  | Lwith1 of Termvar.TermVar.t
  | Lwith2 of Termvar.TermVar.t
  | Lplus of Termvar.TermVar.t
  | Lone of Termvar.TermVar.t
type seq = Typecheck.context * Typecheck.rest * Syntax.Term.t * Syntax.Typ.t
type hole = Syntax.Term.t
module SS :
  sig
    type elt = String.t
    type t = Set.Make(String).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val of_list : elt list -> t
  end
val holeCtr : int ref
val placeCtr : int ref
val makeIdSub : 'a Tmhshtbl.TmHshtbl.t -> Syntax.Term.t Tmhshtbl.TmHshtbl.t
val ctxToString : Syntax.Typ.t Tmhshtbl.TmHshtbl.t -> string
val getContext :
  unit ->
  Syntax.Typ.t Tmhshtbl.TmHshtbl.t *
  (string * Termvar.TermVar.t * Syntax.Typ.t) list
val getType : unit -> Syntax.Typ.t
val possibleRules :
  Syntax.Typ.t Tmhshtbl.TmHshtbl.t ->
  Tmvarrest.SetTmVar.t -> Syntax.Typ.t -> SS.elt list
val listToString : string list -> string
val seqToString :
  Syntax.Typ.t Tmhshtbl.TmHshtbl.t * 'a * Syntax.Term.t * Syntax.Typ.t ->
  string
val removeHole :
  'a ->
  'b ->
  ('a, 'c) Hashtbl.t ->
  ('b, 'd) Hashtbl.t -> ('b, 'd) Hashtbl.t * ('a, 'c) Hashtbl.t
val createHole :
  (Metavar.MetaVar.t, 'a Tmhshtbl.TmHshtbl.t * 'b * 'c) Hashtbl.t ->
  (string, Metavar.MetaVar.t) Hashtbl.t ->
  'c ->
  'a Tmhshtbl.TmHshtbl.t ->
  'b ->
  Metavar.MetaVar.t * Syntax.Term.t * (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t, 'a Tmhshtbl.TmHshtbl.t * 'b * 'c) Hashtbl.t
val createPlace :
  'a Plhshtbl.PlHshtbl.t ->
  'a -> 'a Plhshtbl.PlHshtbl.t * Placevar.PlaceVar.t
val fixEqs2 :
  Typecheck.eqs list ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t ->
  Typecheck.rest ->
  Tmvarrest.SetTmVar.t ->
  Typecheck.eqs list -> Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t
val fixEqs :
  Typecheck.eqs list ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t ->
  Typecheck.rest ->
  Tmvarrest.SetTmVar.t ->
  Typecheck.eqs list -> Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t
val createTerm :
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t ->
  rule ->
  Metavar.MetaVar.t ->
  string ->
  Syntax.Typ.t Tmhshtbl.TmHshtbl.t ->
  Plhshtbl.PlHshtbl.key ->
  Syntax.Typ.t ->
  Typecheck.eqs list ->
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Placevar.PlaceVar.t * Syntax.Typ.t)
  Hashtbl.t ->
  (string, Metavar.MetaVar.t) Hashtbl.t ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t * Syntax.Term.t *
  Typecheck.eqs list * (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Placevar.PlaceVar.t * Syntax.Typ.t)
  Hashtbl.t
val recurInTerm :
  Syntax.Term.t -> Metavar.MetaVar.t -> Syntax.Term.t -> Syntax.Term.t
val occurs : Termvar.TermVar.t -> Termvar.TermVar.t list -> bool
val removeDups : Termvar.TermVar.t list -> Termvar.TermVar.t list
val pick_termvar : Termvar.TermVar.t list -> Termvar.TermVar.t
val pick_rule : Termvar.TermVar.t list -> rule
val analyzeHole :
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t ->
  (string, Metavar.MetaVar.t) Hashtbl.t ->
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t ->
  'a * 'b * Syntax.Term.t * 'c ->
  Typecheck.eqs list ->
  string ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t * ('a * 'b * Syntax.Term.t * 'c) * Typecheck.eqs list
val runStep :
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t ->
  (string, Metavar.MetaVar.t) Hashtbl.t ->
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t ->
  'a * 'b * Syntax.Term.t * 'c ->
  Typecheck.eqs list ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t * ('a * 'b * Syntax.Term.t * 'c) * Typecheck.eqs list
val startSeq :
  'a Tmhshtbl.TmHshtbl.t ->
  ('b * Tmvarrest.SetTmVar.elt * 'c) list ->
  'd ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t, 'a Tmhshtbl.TmHshtbl.t * Placevar.PlaceVar.t * 'd)
  Hashtbl.t *
  ('a Tmhshtbl.TmHshtbl.t * Placevar.PlaceVar.t * Syntax.Term.t * 'd)
val completed : ('a, 'b) Hashtbl.t -> bool
val loop :
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t *
  (Syntax.Typ.t Tmhshtbl.TmHshtbl.t * 'a * Syntax.Term.t * Syntax.Typ.t) *
  Typecheck.eqs list ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t *
  (Syntax.Typ.t Tmhshtbl.TmHshtbl.t * 'a * Syntax.Term.t * Syntax.Typ.t) *
  Typecheck.eqs list
val main :
  unit ->
  Tmvarrest.SetTmVar.t Plhshtbl.PlHshtbl.t *
  (string, Metavar.MetaVar.t) Hashtbl.t *
  (Metavar.MetaVar.t,
   Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Plhshtbl.PlHshtbl.key * Syntax.Typ.t)
  Hashtbl.t *
  (Syntax.Typ.t Tmhshtbl.TmHshtbl.t * Placevar.PlaceVar.t * Syntax.Term.t *
   Syntax.Typ.t) *
  Typecheck.eqs list
val run : unit -> unit
