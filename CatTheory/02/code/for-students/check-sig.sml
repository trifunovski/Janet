
signature CHECK = 
sig

    type exp
    type typ
	
    exception TypeError of string

    (* check(e) = the t such that . |- e : t if such a t exists
       raises TypeError otherwise *)
    val check : exp -> typ

end
    
    