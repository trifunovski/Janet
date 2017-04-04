open Syntax

type pr = | PVar of string
          | PLam of (string * Typ.t) * pr
          | PApp of pr * pr
          | PTenPair of pr * pr
          | PWithPair of pr * pr
          | PLetten of pr * pr * pr
          | PLetapp of string * pr * pr
          | PLetfst of pr * pr * pr
          | PLetsnd of pr * pr * pr
          | PLetmv of string * pr * pr
          | PLetone of pr * pr * pr
          | PInl of pr
          | PInr of pr
          | PCase of string * (string * pr) * (string * pr)
          | PStar (* One *)
