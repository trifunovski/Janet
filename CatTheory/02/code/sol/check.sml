functor CheckFun(structure E : EXP)
	:> CHECK where type exp = E.exp and type typ = Typ.typ =
struct

    type exp = E.exp
    type typ = Typ.typ

    exception TypeError of string

    type ctx = (E.N.name * typ) list;

    fun lookup (v, ctx) = 
	(case List.find (fn (v', t) => E.N.equal(v,v')) ctx of
	     NONE => raise TypeError "unbound variable!"
	   | SOME (_, t) => t)
	    
    fun checkWithCtx (ctx, e) =
	(case (E.show e) of
	     E.Var fv => lookup (fv, ctx)
	   | E.Num _ => Typ.Num
	   | E.Str _ => Typ.Str
	   | E.Plus(e1, e2) => if (checkWithCtx(ctx, e1) = Typ.Num andalso
				   checkWithCtx(ctx, e2) = Typ.Num)
			       then Typ.Num
			       else raise TypeError "subexpressions of Plus must have type Num"
	   | E.Cat (e1, e2) => if (checkWithCtx(ctx, e1) = Typ.Str andalso
				   checkWithCtx(ctx, e2) = Typ.Str)
			       then Typ.Str
			       else raise TypeError "subexpressions of Cat must have type Str"
	   | E.Let (e1, bv, e2) => 
               let val t1 = checkWithCtx (ctx, e1) 
	       in
		   (* this context is wf because bv is fresh 
		      because of the show above *)
		   checkWithCtx ((bv,t1)::ctx, e2)
	       end
	     )
	     
    fun check e = checkWithCtx ([], e);
	
end
