functor CheckFun(structure E : EXP)
	:> CHECK where type exp = E.exp and type typ = Typ.typ =
struct

    type exp = E.exp
    type typ = Typ.typ

    exception TypeError of string

    (* return the type of e
       or raise TypeError if it is ill-typed *)
    fun check e = raise TypeError "unimplemented"
	
end
