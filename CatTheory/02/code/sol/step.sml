functor StepFun(structure E : EXP)
	:> STEP where type exp = E.exp =
struct

    type exp = E.exp;

    exception Stuck of string

    fun sub (n, e') e = 
	let val s = sub (n, e') in
	    case E.show e
	      of E.Var n' => if E.N.equal(n, n') then e' else e
	       | E.Plus(e1, e2) => E.hide(E.Plus(s e1, s e2))
	       | E.Cat(e1, e2) => E.hide(E.Cat(s e1, s e2))
	       | E.Let(e1, n', e2) => E.hide(E.Let(s e1, n', s e2))
	       | _ => e
	end

    fun value e =
	case E.show e
	  of E.Num _ => true
	   | E.Str _ => true
	   | _ => false

    fun step e = 
	case E.show e
	  of E.Plus(e1, e2) =>
	       if not (value e1) then E.hide(E.Plus(step e1, e2))
	       else if not (value e2) then E.hide(E.Plus(e1, step e2))
	       else (case (E.show e1, E.show e2)
		      of (E.Num m, E.Num n) => E.hide(E.Num(m + n))
		       | _ => raise Stuck "Plus")
	   | E.Cat(e1, e2) =>
	       if not (value e1) then E.hide(E.Cat(step e1, e2))
	       else if not (value e2) then E.hide(E.Cat(e1, step e2))
	       else (case (E.show e1, E.show e2)
		      of (E.Str s, E.Str t) => E.hide(E.Str(s ^ t))
		       | _ => raise Stuck "Cat")
	   | E.Let(e1, n, e2) =>
	       if not (value e1) then E.hide(E.Let(step e1, n, e2))
	       else sub (n, e1) e2
	   | _ => raise Stuck "?"
end
