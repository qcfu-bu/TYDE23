open Names

type sort =
  | U
  | L

type 'a abs = Abs of V.t * 'a
and 'a pabs = PAbs of p * 'a

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

let var x = Var x

let rec freshen_p p =
  match p with
  | PVar x -> PVar (V.freshen x)
  | PCons (c, ps) -> PCons (c, List.map freshen_p ps)

let rec xs_of_p p =
  match p with
  | PVar x -> [ x ]
  | PCons (_, ps) -> List.concat_map xs_of_p ps

let findi_opt f ls =
  let rec aux k ls =
    match ls with
    | [] -> None
    | h :: t ->
      if f k h then
        Some (k, h)
      else
        aux (k + 1) t
  in
  aux 0 ls

let bindn_tm k xs m =
  let rec aux k m =
    match m with
    | Type s -> Type s
    | Var y -> (
      let opt = findi_opt (fun _ x -> V.equal x y) xs in
      match opt with
      | Some (i, _) -> Var (V.bind (i + k))
      | None -> Var y)
    | Pi (s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (s, a, Abs (x, b))
    | Fix (Abs (f, Abs (x, m))) ->
      let m = aux (k + 2) m in
      Fix (Abs (f, Abs (x, m)))
    | Lam (s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (s, Abs (x, m))
    | App (s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (s, m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Case (s, m, cls) ->
      let m = aux k m in
      let cls =
        List.map
          (fun (Cl (PAbs (p, rhs))) ->
            let xs = xs_of_p p in
            let k = k + List.length xs in
            let rhs = aux k rhs in
            Cl (PAbs (p, rhs)))
          cls
      in
      Case (s, m, cls)
    | Absurd -> Absurd
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (r, a, Abs (x, b))
    | Ch (r, a) -> Ch (r, aux k a)
    | Fork (a, m, Abs (x, n)) ->
      let a = aux k a in
      let m = aux k m in
      let n = aux (k + 1) n in
      Fork (a, m, Abs (x, n))
    | Send m -> Send (aux k m)
    | Recv (s, m) -> Recv (s, aux k m)
    | Close (r, m) -> Close (r, aux k m)
  in
  aux k m

let unbindn_tm k xs m =
  let sz = List.length xs in
  let rec aux k m =
    match m with
    | Type s -> Type s
    | Var y -> (
      match V.is_bound y sz k with
      | Some i -> List.nth xs (i - k)
      | None -> Var y)
    | Pi (s, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Pi (s, a, Abs (x, b))
    | Fix (Abs (f, Abs (x, m))) ->
      let m = aux (k + 2) m in
      Fix (Abs (f, Abs (x, m)))
    | Lam (s, Abs (x, m)) ->
      let m = aux (k + 1) m in
      Lam (s, Abs (x, m))
    | App (s, m, n) ->
      let m = aux k m in
      let n = aux k n in
      App (s, m, n)
    | Let (m, Abs (x, n)) ->
      let m = aux k m in
      let n = aux (k + 1) n in
      Let (m, Abs (x, n))
    | Data (d, ms) ->
      let ms = List.map (aux k) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (aux k) ms in
      Cons (c, ms)
    | Case (s, m, cls) ->
      let m = aux k m in
      let cls =
        List.map
          (fun (Cl (PAbs (p, rhs))) ->
            let xs = xs_of_p p in
            let k = k + List.length xs in
            let rhs = aux k rhs in
            Cl (PAbs (p, rhs)))
          cls
      in
      Case (s, m, cls)
    | Absurd -> Absurd
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, Abs (x, b)) ->
      let a = aux k a in
      let b = aux (k + 1) b in
      Act (r, a, Abs (x, b))
    | Ch (r, a) -> Ch (r, aux k a)
    | Fork (a, m, Abs (x, n)) ->
      let a = aux k a in
      let m = aux k m in
      let n = aux (k + 1) n in
      Fork (a, m, Abs (x, n))
    | Send m -> Send (aux k m)
    | Recv (s, m) -> Recv (s, aux k m)
    | Close (r, m) -> Close (r, aux k m)
  in
  aux k m

let bindn_cls k xs cls =
  List.map
    (fun (Cl (PAbs (p, rhs))) ->
      let k = k + List.length (xs_of_p p) in
      let rhs = bindn_tm k xs rhs in
      Cl (PAbs (p, rhs)))
    cls

let rec bindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (bindn_tl k xs tl)
    | PBind (a, Abs (x, ptl)) ->
      let a = bindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, Abs (x, ptl))
  in
  aux k ptl

and bindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase b -> TBase (bindn_tm k xs b)
    | TBind (a, Abs (x, tl)) ->
      let a = bindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (a, Abs (x, tl))
  in
  aux k tl

let unbindn_cls k xs cls =
  List.map
    (fun (Cl (PAbs (p, rhs))) ->
      let k = k + List.length (xs_of_p p) in
      let rhs = unbindn_tm k xs rhs in
      Cl (PAbs (p, rhs)))
    cls

let rec unbindn_ptl k xs ptl =
  let rec aux k ptl =
    match ptl with
    | PBase tl -> PBase (unbindn_tl k xs tl)
    | PBind (a, Abs (x, ptl)) ->
      let a = unbindn_tm k xs a in
      let ptl = aux (k + 1) ptl in
      PBind (a, Abs (x, ptl))
  in
  aux k ptl

and unbindn_tl k xs tl =
  let rec aux k tl =
    match tl with
    | TBase a -> TBase (unbindn_tm k xs a)
    | TBind (a, Abs (x, tl)) ->
      let a = unbindn_tm k xs a in
      let tl = aux (k + 1) tl in
      TBind (a, Abs (x, tl))
  in
  aux k tl

let bind_tm x m = Abs (x, bindn_tm 0 [ x ] m)
let bind_tm_abs f x m = Abs (f, Abs (x, bindn_tm 0 [ f; x ] m))

let bindp_tm p m =
  let xs = xs_of_p p in
  PAbs (p, bindn_tm 0 xs m)

let bind_ptl x ptl = Abs (x, bindn_ptl 0 [ x ] ptl)
let bind_tl x tl = Abs (x, bindn_tl 0 [ x ] tl)

let unbind_tm (Abs (x, m)) =
  let x = V.freshen x in
  (x, unbindn_tm 0 [ Var x ] m)

let unbind_tm_abs (Abs (f, Abs (x, m))) =
  let f = V.freshen f in
  let x = V.freshen x in
  (f, x, unbindn_tm 0 [ Var f; Var x ] m)

let unbindp_tm (PAbs (p, rhs)) =
  let ps = freshen_p p in
  let xs = ps |> xs_of_p |> List.map var in
  (ps, unbindn_tm 0 xs rhs)

let unbind_ptl (Abs (x, ptl)) =
  let x = V.freshen x in
  (x, unbindn_ptl 0 [ Var x ] ptl)

let unbind_tl (Abs (x, tl)) =
  let x = V.freshen x in
  (x, unbindn_tl 0 [ Var x ] tl)

let rec equal_p p1 p2 =
  match (p1, p2) with
  | PVar _, PVar _ -> true
  | PCons (c1, ps1), PCons (c2, ps2) ->
    C.equal c1 c2 && List.equal equal_p ps1 ps2
  | _ -> false

let rec match_p p m =
  match (p, m) with
  | PVar x, _ -> [ m ]
  | PCons (c1, ps), Cons (c2, ms) ->
    if C.equal c1 c2 then
      List.fold_left2 (fun acc p m -> acc @ match_p p m) [] ps ms
    else
      failwith "match_p"
  | _ -> failwith "match_p"

let asubst_tm (Abs (_, m)) n = unbindn_tm 0 [ n ] m
let asubst_tl (Abs (_, tl)) n = unbindn_tl 0 [ n ] tl
let asubst_ptl (Abs (_, ptl)) n = unbindn_ptl 0 [ n ] ptl
let asubstp_tm (PAbs (p, m)) n = unbindn_tm 0 (match_p p n) m
let subst_tm x m n = unbindn_tm 0 [ n ] (bindn_tm 0 [ x ] m)

let rec mkApps s hd ms =
  match ms with
  | m :: ms -> mkApps s (App (s, hd, m)) ms
  | [] -> hd

let unApps m =
  let rec aux m ns =
    match m with
    | App (_, m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []

let equal_abs eq (Abs (_, m)) (Abs (_, n)) = eq m n
let equal_pabs eq (PAbs (_, m)) (PAbs (_, n)) = eq m n

let rec occurs_tm x m =
  match m with
  | Type _ -> false
  | Var y -> V.equal x y
  | Pi (_, a, abs) ->
    let _, b = unbind_tm abs in
    occurs_tm x a || occurs_tm x b
  | Fix abs ->
    let _, _, m = unbind_tm_abs abs in
    occurs_tm x m
  | Lam (_, abs) ->
    let _, m = unbind_tm abs in
    occurs_tm x m
  | App (_, m, n) -> occurs_tm x m || occurs_tm x n
  | Let (m, abs) ->
    let _, n = unbind_tm abs in
    occurs_tm x m || occurs_tm x n
  | Data (_, ms) -> List.exists (occurs_tm x) ms
  | Cons (_, ms) -> List.exists (occurs_tm x) ms
  | Case (_, m, cls) ->
    occurs_tm x m
    || List.exists
         (fun (Cl pabs) ->
           let _, rhs = unbindp_tm pabs in
           occurs_tm x rhs)
         cls
  | Absurd -> false
  | Main -> false
  | Proto -> false
  | End -> false
  | Act (_, a, abs) ->
    let _, b = unbind_tm abs in
    occurs_tm x a || occurs_tm x b
  | Ch (_, a) -> occurs_tm x a
  | Fork (a, m, abs) ->
    let _, n = unbind_tm abs in
    occurs_tm x a || occurs_tm x m || occurs_tm x n
  | Send m -> occurs_tm x m
  | Recv (s, m) -> occurs_tm x m
  | Close (r, m) -> occurs_tm x m

let rec occurs_tl x tl =
  match tl with
  | TBase b -> occurs_tm x b
  | TBind (a, abs) ->
    if occurs_tm x a then
      true
    else
      let _, tl = unbind_tl abs in
      occurs_tl x tl