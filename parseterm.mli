open Syntax

type pr = | PVar of string
          | PLam of (string * Typ.t) * pr
          | PApp of pr * pr
          | PTenPair of pr * pr
          | PWithPair of pr * pr
          | PLetten of pr * string * pr
          | PLetapp of pr * (string * pr) * pr
          | PLetfst of pr * string * pr
          | PLetsnd of pr * string * pr
          | PInl of pr
          | PInr of pr
          | PCase of string * (string * pr) * (string * pr)
          | PStar (* One *)
