signature TOP =
sig
    type exp

    (* interactive loop *)
    val loop_print : unit -> unit (* just print the same expression back *)
    val loop_type  : unit -> unit (* just type check *)
    val loop_eval  : unit -> unit (* type check and show the final value *)
    val loop_step  : unit -> unit (* type check and show all steps of evaluation *)

    (* read an EXP source file *)
    val file_print : string -> unit
    val file_type  : string -> unit
    val file_eval  : string -> unit
    val file_step  : string -> unit
end;  (* signature TOP *)

functor TopFun(structure E : EXP)
	:> TOP where type exp = E.exp =
struct

    type exp = E.exp

    type action = exp -> unit

    structure Parse = ParseFun(structure E = E)
    structure Print = PrintFun(structure E = E)
    structure Check = CheckFun(structure E = E)
    structure Step = StepFun(structure E = E)

    fun typing e =
        (" : " ^ (case Check.check e
		   of Typ.Num => "num"
		    | Typ.Str => "str") ^ ";")
        handle Check.TypeError _ => " has no type."

  (* A few actions *)

  fun show e =
      List.app print [Print.expToString e, ";\n"]

  fun showType e =
      List.app print [Print.expToString e, typing e, "\n"]

  fun stepToValue e =
          if Step.value e then e
          else stepToValue (Step.step e)

  fun eval action e = action (stepToValue e)

  fun wait action e =
      (action e;
       print "Press return:";
       TextIO.inputLine TextIO.stdIn;
       ())

  fun step action e =
          (action e;
           if Step.value e then () else step action (Step.step e))

  (* Running the actions on an interactive loop or a file *)

  fun loop action =
         Stream.app action
         (Input.promptKeybd "EXP>" "...  >"
         (fn s => Parse.parse (Lexer.lex s)))

  fun loopFile name action =
         Stream.app action
         (Parse.parse(Lexer.lex(Input.readFile name)))

    fun hdl f x = (f x)
            handle Lexer.Error s => print ("\nLexer error: " ^ s ^ "\n")
                 | Parse.Error s => print ("\nParse error: " ^ s ^ "\n")
                 | Check.TypeError s =>
                       print ("\nType error: " ^ s ^ "\n")
                 | Step.Stuck s =>
                       print ("\nStep error: " ^ s ^ "\n")

    fun loop_print () = hdl loop show
    fun loop_type () = hdl loop showType
    fun loop_eval () = hdl loop (eval showType)
    fun loop_step () = hdl loop (step (wait showType))
    fun file_print f = hdl (loopFile f) show
    fun file_type f = hdl (loopFile f) showType
    fun file_eval f = hdl (loopFile f) (eval showType)
    fun file_step f = hdl (loopFile f) (step (wait showType))
end;  (* functor TopFun *)

structure Top :> TOP =
  TopFun(structure E = NamedExp)

