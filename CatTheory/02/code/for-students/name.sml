structure Name :> NAME = 
struct
    type name = string;

    (* broken because of overflow.... *)
    local 
	val suffix = ref 0 
    in
	fun new s = 
	     (suffix := (!suffix)+1;
	      s^(Int.toString(!suffix)))
    end

    fun equal(n1 : name, n2) = n1 = n2;

    fun toString n = n;
end
