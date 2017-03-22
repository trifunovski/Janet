structure NamedExp :> EXP = 
struct

    structure N = Name

    datatype exp1 = 
	Var of N.name
      | Num of int
      | Str of string
      | Plus of exp * exp
      | Cat of exp * exp
      | Let of exp * N.name * exp
    withtype exp = exp1

    fun hide e = e;

    fun swapName (x, y) z =
	if N.equal(z, x) then y
	else if N.equal(z, y) then x
	else z

    fun swapExp (x, y) e =
	let val se = swapExp (x, y)
	    val sn = swapName (x, y) in
	    (case e
	       of Var z => Var(sn z)
		| Plus(e1, e2) => Plus(se e1, se e2)
		| Cat(e1, e2) => Cat(se e1, se e2)
		| Let(e1, x, e2) => Let(se e1, sn x, se e2)
		| _ => e)
	end

    (* rename bound variables to something fresh *)
    fun show (Let (e1, oldName, e2)) = 
	let val freshName = N.new (N.toString oldName) in
	    Let (e1, freshName, swapExp (oldName, freshName) e2)
	end
      | show e = e;

end
