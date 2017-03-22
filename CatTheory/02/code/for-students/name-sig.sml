
signature NAME =
sig 
    type name;
    
    (* never returns equal names *)
    val new : string -> name;
    
    val equal : name * name -> bool;

    val toString : name -> string;

end