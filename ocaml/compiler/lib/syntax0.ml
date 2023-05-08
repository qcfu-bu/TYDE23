type id = string [@@deriving show { with_path = false }]
and id_opt = id option

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type tm =
  | Ann of tm * tm
  | Type of sort
  | Id of id
  | Pi of sort * args * tm
  | Fun of id_opt * tm_opt * cls
  | App of tms
  | Let of p * tm * tm
  | Match of tms * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * args * tm
  | Ch of bool * tm
  | Fork of id * tm * tm * tm
  | Send of tm
  | Recv of tm
  | Close of tm
[@@deriving show { with_path = false }]

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of id_opt
  | PCons of id * ps
  | PAbsurd

and ps = p list
and arg = id_opt * tm
and args = arg list
and cl = Cl of (ps * tm_opt)
and cls = cl list

type dcl =
  | DTm of id_opt * tm_opt * tm
  | DFun of id * tm * cls
  | DData of id * ptl * dconss
  | DOpen of id * id
  | DAxiom of id * tm
[@@deriving show { with_path = false }]

and dcls = dcl list
and dcons = DCons of id * ptl
and dconss = dcons list
and ptl = PTl of args * tl
and tl = Tl of args * tm

let lam x m = Fun (None, None, [ Cl ([ PVar x ], Some m) ])
