open Names

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type 'a abs [@@deriving show { with_path = false }]
and 'a pabs

and tm =
  | Ann of tm * tm
  | Meta of M.t * tms
  | Type of sort
  | Var of V.t
  | Pi of sort * tm * tm abs
  | Fun of tm_opt * cls abs
  | App of tm * tm
  | Let of tm * tm abs
  | Data of D.t * tms
  | Cons of C.t * tms
  | Absurd
  | Match of tms * tm * cls
  | If of tm * tm * tm
  | Main
  | Proto
  | End
  | Act of bool * tm * tm abs
  | Ch of bool * tm
  | Fork of tm * tm * tm abs
  | Send of tm
  | Recv of tm
  | Close of tm

and tms = tm list
and tm_opt = tm option

and p =
  | PVar of V.t
  | PCons of C.t * ps
  | PAbsurd

and ps = p list
and cl = Cl of tm_opt pabs
and cls = cl list

type trg =
  | TStdin
  | TStdout
  | TStderr
[@@deriving show { with_path = false }]

type dcl =
  | DTm of V.t * tm_opt * tm
  | DFun of V.t * tm * cls abs
  | DData of D.t * ptl * dconss
  | DOpen of trg * V.t
  | DAxiom of V.t * tm
[@@deriving show { with_path = false }]

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
val xs_of_ps : ps -> V.t list
val bind_tm : V.t -> tm -> tm abs
val bindp_tm_opt : ps -> tm_opt -> tm_opt pabs
val bind_cls : V.t -> cls -> cls abs
val bind_ptl : V.t -> ptl -> ptl abs
val bind_tl : V.t -> tl -> tl abs
val unbind_cls : cls abs -> V.t * cls
val unbind_tm : tm abs -> V.t * tm
val unbindp_tm_opt : tm_opt pabs -> ps * tm_opt
val unbind_ptl : ptl abs -> V.t * ptl
val unbind_tl : tl abs -> V.t * tl
val unbind2_tm : tm abs -> tm abs -> V.t * tm * tm
val unbindp2_tm_opt : tm_opt pabs -> tm_opt pabs -> ps * tm_opt * tm_opt
val unbind2_cls : cls abs -> cls abs -> V.t * cls * cls
val equal_abs : ('a -> 'b -> bool) -> 'a abs -> 'b abs -> bool
val equal_pabs : ('a -> 'b -> bool) -> 'a pabs -> 'b pabs -> bool
val asubst_tm : tm abs -> tm -> tm
val asubst_tl : tl abs -> tm -> tl
val asubst_ptl : ptl abs -> tm -> ptl
val asubst_cls : cls abs -> tm -> cls
val substp_tm_opt : ps -> tm_opt -> tms -> tm_opt
val subst_tm : V.t -> tm -> tm -> tm
val lam : V.t -> tm -> tm
val mLam : V.t list -> tm -> tm
val fold_tl : ('a -> tm -> V.t -> tl -> 'a * tl) -> 'a -> tl -> 'a * tm
val mkApps : tm -> tms -> tm
val unApps : tm -> tm * tms
val occurs_tm : V.t -> tm -> bool
val occurs_cls : V.t -> cls -> bool
val occurs_tl : V.t -> tl -> bool