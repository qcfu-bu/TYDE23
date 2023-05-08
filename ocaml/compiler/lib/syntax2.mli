open Names

type sort =
  | U
  | L

type 'a abs
and 'a pabs

and tm =
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * tm abs
  | Fix of tm abs abs
  | Lam of sort * tm abs
  | App of sort * tm * tm
  | Let of tm * tm abs
  | Data of D.t * tms
  | Cons of C.t * tms
  | Case of sort * tm * cls
  | Absurd
  | Main
  | Proto
  | End
  | Act of bool * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm * tm abs
  | Send of tm
  | Recv of sort * tm
  | Close of bool * tm

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of V.t
  | PCons of C.t * ps

and ps = p list
and cl = Cl of tm pabs
and cls = cl list

type trg =
  | TStdin
  | TStdout
  | TStderr

type dcl =
  | DTm of V.t * tm
  | DData of D.t * ptl * dconss
  | DOpen of trg * V.t
  | DAxiom of V.t * tm

and dcls = dcl list
and dcons = DCons of C.t * ptl
and dconss = dcons list

and ptl =
  | PBase of tl
  | PBind of tm * ptl abs

and tl =
  | TBase of tm
  | TBind of tm * tl abs

val var : V.t -> tm
val bind_tm : V.t -> tm -> tm abs
val bind_tm_abs : V.t -> V.t -> tm -> tm abs abs
val bindp_tm : p -> tm -> tm pabs
val bind_ptl : V.t -> ptl -> ptl abs
val bind_tl : V.t -> tl -> tl abs
val unbind_tm : tm abs -> V.t * tm
val unbind_tm_abs : tm abs abs -> V.t * V.t * tm
val unbindp_tm : tm pabs -> p * tm
val unbind_ptl : ptl abs -> V.t * ptl
val unbind_tl : tl abs -> V.t * tl
val equal_abs : ('a -> 'b -> bool) -> 'a abs -> 'b abs -> bool
val equal_pabs : ('a -> 'b -> bool) -> 'a pabs -> 'b pabs -> bool
val asubst_tm : tm abs -> tm -> tm
val asubst_tl : tl abs -> tm -> tl
val asubst_ptl : ptl abs -> tm -> ptl
val subst_tm : V.t -> tm -> tm -> tm
val mkApps : sort -> tm -> tms -> tm
val unApps : tm -> tm * tms
val occurs_tm : V.t -> tm -> bool
val occurs_tl : V.t -> tl -> bool
