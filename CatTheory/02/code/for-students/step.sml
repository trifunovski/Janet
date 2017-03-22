functor StepFun(structure E : EXP)
	:> STEP where type exp = E.exp =
struct

    type exp = E.exp;

    exception Stuck of string

    (* true iff e is a value *)
    fun value e = false

    (* step the expression, raise Stuck if you can't *)
    fun step e = raise Stuck "unimplemented"
end
