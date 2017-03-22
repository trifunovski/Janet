
signature STEP =
sig

    type exp 

    exception Stuck of string

    (* step the expression, raise Stuck if you can't *)
    val step : exp -> exp

    (* true iff exp is a value *)
    val value : exp -> bool	
end
