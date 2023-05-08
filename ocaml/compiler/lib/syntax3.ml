open Names

type value =
  | Zero
  | Reg of V.t
  | Env of int
  | Proj of value * int

and values = value list

and proc =
  { name : V.t
  ; arg : V.t option
  ; body : instrs
  ; return : value
  }

and chs = V.t list
and def = proc list

and trg =
  | TCh of V.t * value * int * values
  | TStdin
  | TStdout
  | TStderr

and instr =
  | Mov of V.t * value
  | Clo of V.t * V.t * int * values
  | Call of V.t * value * value
  | Struct of V.t * int * values
  | Switch of value * cls
  | Break
  | Open of V.t * trg
  | Send of V.t * value
  | Recv of V.t * value * int
  | Close of V.t * value
  | FreeClo of value
  | FreeStruct of value
  | FreeThread

and instrs = instr list
and cl = int * instrs
and cls = cl list