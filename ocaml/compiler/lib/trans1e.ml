open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

type ctx =
  { vs : tm VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x a ctx = { ctx with vs = VMap.add x a ctx.vs }
let add_d d ptl cs ctx = { ctx with ds = DMap.add d (ptl, cs) ctx.ds }
let add_c c ptl ctx = { ctx with cs = CMap.add c ptl ctx.cs }
let add_m x a map = MMap.add x (None, Some a) map

let find_v x ctx =
  match VMap.find_opt x ctx.vs with
  | Some a -> a
  | None -> failwith "find_v(%a)" V.pp x

let find_d d ctx =
  match DMap.find_opt d ctx.ds with
  | Some res -> res
  | None -> failwith "find_d(%a)" D.pp d

let find_c c ctx =
  match CMap.find_opt c ctx.cs with
  | Some ptl -> ptl
  | None -> failwith "find_c(%a)" C.pp c

let find_m x map =
  match MMap.find_opt x map with
  | Some (_, Some a) -> a
  | _ -> failwith "find_m(%a)" M.pp x

let pp_vs fmt vs =
  let aux fmt vs =
    VMap.iter (fun x a -> pf fmt "@[%a :@;<1 2>%a@]@;<1 2>" V.pp x pp_tm a) vs
  in
  pf fmt "@[<v 0>vs={@;<1 2>%a}@]" aux vs

let pp_ds fmt ds =
  let aux fmt ds =
    DMap.iter
      (fun d (ptl, _) -> pf fmt "@[%a : %a@]@;<1 2>" D.pp d pp_ptl ptl)
      ds
  in
  pf fmt "@[<v 0>ds={@;<1 2>%a}@]" aux ds

let pp_cs fmt cs =
  let aux fmt cs =
    CMap.iter (fun c ptl -> pf fmt "@[%a : %a@]@;<1 2>" C.pp c pp_ptl ptl) cs
  in
  pf fmt "@[<v 0>cs={@;<1 2>%a}@]" aux cs

let pp_ctx fmt ctx = pf fmt "@[<v 0>ctx{@;<1 2>%a}@]" pp_vs ctx.vs

let msubst_ctx map ctx =
  let vs = VMap.map (fun a -> UVar.msubst_tm map a) ctx.vs in
  { ctx with vs }

let subst_ctx x ctx m =
  let ctx = { ctx with vs = VMap.remove x ctx.vs } in
  msubst_ctx (VMap.singleton x m) ctx

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env eqns map m n =
  if equal rd_all env m n then
    (eqns, map)
  else
    (UMeta.Eq (env, m, n) :: eqns, map)

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let rec infer_sort ctx env eqns map a =
  let srt, eqns, map = infer_tm ctx env eqns map a in
  let srt = UMeta.resolve_tm map srt in
  match whnf rd_all env srt with
  | Type s -> (s, eqns, map)
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env eqns map m =
  match m with
  | Ann (a, m) -> (
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let eqns, map = check_tm ctx env eqns map (Let (m, abs)) a in
      (a, eqns, map)
    | _ ->
      let eqns, map = check_tm ctx env eqns map m a in
      (a, eqns, map))
  | Meta (x, xs) -> (
    try (find_m x map, eqns, map) with
    | _ ->
      let meta, _ = meta_mk ctx in
      (meta, eqns, add_m x meta map))
  | Type _ -> (Type U, eqns, map)
  | Var x -> (find_v x ctx, eqns, map)
  | Pi (s, a, abs) ->
    let x, b = unbind_tm abs in
    let _, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    let _, eqns, map = infer_sort ctx env eqns map b in
    (Type s, eqns, map)
  | Fun (a_opt, cls) -> (
    match a_opt with
    | Some a ->
      let _, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map (Fun (a_opt, cls)) a in
      (a, eqns, map)
    | None -> failwith "infer_Fun(%a)" pp_tm m)
  | App (m, n) -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Pi (_, a, abs) ->
      let eqns, map = check_tm ctx env eqns map n a in
      (asubst_tm abs (Ann (a, n)), eqns, map)
    | a -> (fst (meta_mk ctx), eqns, map))
  | Let (m, abs) ->
    let a, eqns, map = infer_tm ctx env eqns map m in
    let s, eqns, map = infer_sort ctx env eqns map a in
    let map = UMeta.unify map eqns in
    let m = UMeta.resolve_tm map m in
    let a = UMeta.resolve_tm map a in
    let x, n = unbind_tm abs in
    let ctx = add_v x a ctx in
    let env =
      match s with
      | U -> VMap.add x m env
      | L -> env
    in
    infer_tm ctx env eqns map n
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    check_ptl ctx env eqns map ms ptl
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    check_ptl ctx env eqns map ms ptl
  | Absurd -> failwith "infer_Absurd(%a)" pp_tm m
  | Match (ms, b, cls) ->
    let ms_ty, eqns, map =
      List.fold_left
        (fun (acc, eqns, map) m ->
          let a, eqns, map = infer_tm ctx env eqns map m in
          (a :: acc, eqns, map))
        ([], eqns, map) ms
    in
    let a =
      List.fold_left
        (fun acc m_ty -> Pi (L, m_ty, bind_tm (V.blank ()) acc))
        b ms_ty
    in
    let prbm = UVar.prbm_of_cls cls in
    let map = UMeta.unify map eqns in
    let eqns, map = check_prbm ctx env eqns map prbm a in
    let map = UMeta.unify map eqns in
    (UMeta.resolve_tm map b, eqns, map)
  | If (m, tt, ff) ->
    let eqns, map = check_tm ctx env eqns map m (Data (Prelude.bool_d, [])) in
    let tt_ty, eqns, map = infer_tm ctx env eqns map tt in
    let ff_ty, eqns, map = infer_tm ctx env eqns map ff in
    let eqns, map = assert_equal env eqns map tt_ty ff_ty in
    (tt_ty, eqns, map)
  | Main -> (Type L, eqns, map)
  | Proto -> (Type U, eqns, map)
  | End -> (Proto, eqns, map)
  | Act (r, a, abs) ->
    let s, eqns, map = infer_sort ctx env eqns map a in
    let x, b = unbind_tm abs in
    let eqns, map = check_tm (add_v x a ctx) env eqns map b Proto in
    (Proto, eqns, map)
  | Ch (r, m) ->
    let eqns, map = check_tm ctx env eqns map m Proto in
    (Type L, eqns, map)
  | Fork (a, m, abs) -> (
    let _, eqns, map = infer_sort ctx env eqns map a in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (true, a) ->
      let x, n = unbind_tm abs in
      let eqns, map = check_tm ctx env eqns map a Proto in
      let eqns, map = check_tm ctx env eqns map m Main in
      let unit = Data (Prelude.unit_d, []) in
      let ctx = add_v x (Ch (true, a)) ctx in
      let eqns, map = check_tm ctx env eqns map n unit in
      let a = Ch (false, a) in
      (Data (Prelude.tnsr_d, [ a; Main ]), eqns, map)
    | _ -> failwith "infer_Fork(%a)" pp_tm m)
  | Send m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, abs), eqns, map)
    | a -> failwith "infer_Send(%a, %a)" pp_tm m pp_tm a)
  | Recv m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 = r2 -> (
      let x, b = unbind_tm abs in
      let s, eqns, map = infer_sort ctx env eqns map a in
      match s with
      | U -> (Data (Prelude.sig_d, [ a; lam x (Ch (r1, b)) ]), eqns, map)
      | L -> (Data (Prelude.tnsr_d, [ a; Ch (r1, b) ]), eqns, map))
    | a -> failwith "infer_Recv(%a : %a)" pp_tm m pp_tm a)
  | Close m -> (
    let a, eqns, map = infer_tm ctx env eqns map m in
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Ch (_, End) -> (Data (Prelude.unit_d, []), eqns, map)
    | _ -> failwith "infer_Close(%a)" pp_tm m)

and check_ptl ctx env eqns map ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) ->
    let s, eqns, map = infer_sort ctx env eqns map a in
    let eqns, map = check_tm ctx env eqns map m a in
    check_ptl ctx env eqns map ms (asubst_ptl abs (Ann (a, m)))
  | ms, PBase tl -> check_tl ctx env eqns map ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env eqns map ms tl =
  match (ms, tl) with
  | m :: ms, TBind (a, abs) ->
    let s, eqns, mpa = infer_sort ctx env eqns map a in
    let eqns, map = check_tm ctx env eqns map m a in
    check_tl ctx env eqns map ms (asubst_tl abs (Ann (a, m)))
  | [], TBase a ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    (a, eqns, map)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env eqns map m a =
  match m with
  | Meta (x, _) -> (eqns, add_m x a map)
  | Fun (b_opt, abs) ->
    let eqns, map =
      match b_opt with
      | Some b ->
        let _, eqns, map = infer_sort ctx env eqns map b in
        assert_equal env eqns map a b
      | None -> (eqns, map)
    in
    let x, cls = unbind_cls abs in
    let prbm = UVar.prbm_of_cls cls in
    let map = UMeta.unify map eqns in
    check_prbm (add_v x a ctx) env eqns map prbm a
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, eqns, map = infer_tm ctx env eqns map (Let (m, abs)) in
    assert_equal env eqns map a b
  | Cons (c, ms) -> (
    let a = UMeta.resolve_tm map a in
    match whnf rd_all env a with
    | Data (_, ns) ->
      let ptl = find_c c ctx in
      let ptl =
        List.fold_left
          (fun ptl n ->
            match ptl with
            | PBind (a, abs) -> asubst_ptl abs (Ann (a, n))
            | PBase _ -> ptl)
          ptl ns
      in
      let b, eqns, map = check_ptl ctx env eqns map ms ptl in
      assert_equal env eqns map a b
    | _ ->
      let b, eqns, map = infer_tm ctx env eqns map m in
      assert_equal env eqns map a b)
  | Match (ms, b, cls) ->
    let eqns, map = assert_equal env eqns map a b in
    let ms_ty, eqns, map =
      List.fold_left
        (fun (acc, eqns, map) m ->
          let a, eqns, map = infer_tm ctx env eqns map m in
          (a :: acc, eqns, map))
        ([], eqns, map) ms
    in
    let a =
      List.fold_left
        (fun acc m_ty -> Pi (L, m_ty, bind_tm (V.blank ()) acc))
        a ms_ty
    in
    let prbm = UVar.prbm_of_cls cls in
    let map = UMeta.unify map eqns in
    let eqns, map = check_prbm ctx env eqns map prbm a in
    let map = UMeta.unify map eqns in
    (eqns, map)
  | _ ->
    let b, eqns, map = infer_tm ctx env eqns map m in
    assert_equal env eqns map a b

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (a, abs), n :: ns ->
    let ptl = asubst_ptl abs (Ann (a, n)) in
    tl_of_ptl ptl ns
  | PBase tl, _ -> tl
  | _ -> failwith "tl_of_ptl"

and check_prbm ctx env eqns map prbm a =
  let rec is_absurd es rhs =
    match (es, rhs) with
    | UVar.Eq (_, Var _, Absurd, _) :: _, None -> true
    | UVar.Eq (_, Var _, Absurd, _) :: _, Some _ -> failwith "is_absurd"
    | _ :: es, _ -> is_absurd es rhs
    | [], _ -> false
  in
  let rec get_absurd = function
    | UVar.Eq (_, Var _, Absurd, a) :: _ -> a
    | _ :: es -> get_absurd es
    | [] -> failwith "get_absurd"
  in
  let rec can_split = function
    | UVar.Eq (_, Var _, Cons (_, _), _) :: _ -> true
    | _ :: es -> can_split es
    | [] -> false
  in
  let rec first_split = function
    | UVar.Eq (_, Var x, Cons (c, ms), a) :: _ -> (x, a)
    | _ :: es -> first_split es
    | [] -> failwith "first_split"
  in
  let fail_on_d ctx eqns map d ns s a =
    let _, cs = find_d d ctx in
    let ptls = List.map (fun c -> find_c c ctx) cs in
    let rec loop = function
      | [] -> (eqns, map)
      | ptl :: ptls ->
        let tl = tl_of_ptl ptl ns in
        let _, targ = fold_tl (fun () _ _ tl -> ((), tl)) () tl in
        let global = UVar.Eq (env, a, targ, Type s) :: prbm.global in
        if has_failed (fun () -> UVar.unify global) then
          loop ptls
        else
          failwith "fail_on_d(%a)" pp_tm (Data (d, ns))
    in
    loop ptls
  in
  match prbm.clause with
  | [] -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      (eqns, map)
    else
      let a = UMeta.resolve_tm map a in
      match whnf rd_all env a with
      | Pi (_, a, _) -> (
        let s, eqns, map = infer_sort ctx env eqns map a in
        match whnf rd_all env a with
        | Data (d, ns) -> fail_on_d ctx eqns map d ns s a
        | _ -> failwith "check_Empty")
      | a -> failwith "check_Empty(%a)" pp_tm a)
  | (es, ps, rhs) :: _ when is_absurd es rhs -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      (eqns, map)
    else
      let a = get_absurd es in
      let s, eqns, map = infer_sort ctx env eqns map a in
      let a = UMeta.resolve_tm map a in
      match whnf rd_all env a with
      | Data (d, ns) -> fail_on_d ctx eqns map d ns s a
      | _ -> failwith "check_Absurd")
  | (es, ps, rhs) :: _ when can_split es -> (
    let x, b = first_split es in
    let s, eqns, map = infer_sort ctx env eqns map b in
    let b = UMeta.resolve_tm map b in
    match whnf rd_all env b with
    | Data (d, ns) ->
      let _, cs = find_d d ctx in
      let ptls = List.map (fun c -> find_c c ctx) cs in
      List.fold_left2
        (fun (eqns, map) ptl c ->
          let tl = tl_of_ptl ptl ns in
          let (ctx, args), targ =
            fold_tl
              (fun (ctx, acc) a x tl ->
                let ctx = add_v x a ctx in
                ((ctx, Var x :: acc), tl))
              (ctx, []) tl
          in
          let c = Ann (targ, Cons (c, List.rev args)) in
          let a = subst_tm x a c in
          let ctx = subst_ctx x ctx c in
          let prbm = prbm_subst ctx map x prbm c in
          let prbm =
            UVar.{ prbm with global = Eq (env, b, targ, Type s) :: prbm.global }
          in
          check_prbm ctx env eqns map prbm a)
        (eqns, map) ptls cs
    | b -> failwith "check_Split(%a)" pp_tm b)
  | (es, [], rhs) :: _ ->
    let es = prbm.global @ es in
    let vmap = UVar.unify es in
    let a = UVar.msubst_tm vmap a in
    let ctx = msubst_ctx vmap ctx in
    let rhs =
      match rhs with
      | Some m -> UVar.msubst_tm vmap m
      | None -> failwith "check_Finish"
    in
    check_tm ctx env eqns map rhs a
  | (es, ps, rhs) :: clause -> (
    let a = UMeta.resolve_tm map a in
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (s, a, abs), p :: ps ->
      let x, b = unbind_tm abs in
      let ctx = add_v x a ctx in
      let prbm = prbm_add ctx env prbm x a in
      check_prbm ctx env eqns map prbm b
    | _ -> failwith "check_Intro")

and prbm_add ctx env prbm x a =
  let rec tm_of_p p =
    match p with
    | PVar x -> Var x
    | PCons (c, ps) ->
      let ptl = find_c c ctx in
      let ps = ps_of_ptl ps ptl in
      let ps = List.map tm_of_p ps in
      Cons (c, ps)
    | PAbsurd -> Absurd
  and ps_of_ptl ps ptl =
    match ptl with
    | PBase tl -> ps_of_tl ps tl
    | PBind (_, abs) ->
      let _, ptl = unbind_ptl abs in
      ps_of_ptl ps ptl
  and ps_of_tl ps tl =
    match tl with
    | TBase _ -> ps
    | TBind (_, abs) -> (
      let _, tl = unbind_tl abs in
      match ps with
      | p :: ps -> p :: ps_of_tl ps tl
      | _ -> failwith "ps_of_tl")
  in
  match prbm.clause with
  | [] -> prbm
  | (es, p :: ps, rhs) :: clause ->
    let prbm = prbm_add ctx env { prbm with clause } x a in
    let clause =
      (UVar.Eq (env, Var x, tm_of_p p, a) :: es, ps, rhs) :: prbm.clause
    in
    { prbm with clause }
  | _ -> failwith "prbm_add"

and prbm_subst ctx map x prbm m =
  match prbm.clause with
  | [] -> prbm
  | (es, ps, rhs) :: clause -> (
    let prbm = prbm_subst ctx map x { prbm with clause } m in
    let opt =
      List.fold_left
        (fun acc (UVar.Eq (env, l, r, a)) ->
          match acc with
          | Some acc -> (
            let l = subst_tm x l m in
            let a = subst_tm x a m in
            match p_simpl ctx env map l r a with
            | Some es -> Some (acc @ es)
            | None -> None)
          | None -> None)
        (Some []) es
    in
    match opt with
    | Some es -> { prbm with clause = (es, ps, rhs) :: prbm.clause }
    | _ -> prbm)

and p_simpl ctx env map m n a =
  let m = whnf rd_all env m in
  let n = whnf rd_all env n in
  let a = UMeta.resolve_tm map a in
  let a = whnf rd_all env a in
  match (m, n, a) with
  | Cons (c1, xs), Cons (c2, ys), Data (d, ns) ->
    if C.equal c1 c2 then
      let _, cs = find_d d ctx in
      if List.exists (fun c -> c = c1) cs then
        let ptl = find_c c1 ctx in
        let tl = tl_of_ptl ptl ns in
        ps_simpl_tl ctx env map xs ys tl
      else
        failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
    else
      None
  | Cons (c1, _), _, Data (d, _) ->
    let _, cs = find_d d ctx in
    if List.exists (fun c -> c = c1) cs then
      Some [ UVar.Eq (env, m, n, a) ]
    else
      failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
  | _, Cons (c2, _), Data (d, _) ->
    let _, cs = find_d d ctx in
    if List.exists (fun c -> c = c2) cs then
      Some [ UVar.Eq (env, m, n, a) ]
    else
      failwith "p_simpl(%a, %a, %a)" pp_tm m pp_tm n pp_tm a
  | _ -> Some [ UVar.Eq (env, m, n, a) ]

and ps_simpl_tl ctx env map ms ns tl =
  match (ms, ns, tl) with
  | m :: ms, n :: ns, TBind (a, abs) -> (
    let opt1 = p_simpl ctx env map m n a in
    let tl = asubst_tl abs m in
    let opt2 = ps_simpl_tl ctx env map ms ns tl in
    match (opt1, opt2) with
    | Some es1, Some es2 -> Some (es1 @ es2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None

let rec infer_dcl ctx env eqns map dcl =
  match dcl with
  | DTm (x, a_opt, m) -> (
    match a_opt with
    | Some a ->
      let s, eqns, map = infer_sort ctx env eqns map a in
      let eqns, map = check_tm ctx env eqns map m a in
      let map = UMeta.unify map eqns in
      let m = UMeta.resolve_tm map m in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      if s = U then
        let env = VMap.add x m env in
        (ctx, env, eqns, map)
      else
        (ctx, env, eqns, map)
    | None ->
      let a, eqns, map = infer_tm ctx env eqns map m in
      let s, eqns, map = infer_sort ctx env eqns map a in
      let map = UMeta.unify map eqns in
      let m = UMeta.resolve_tm map m in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      if s = U then
        let env = VMap.add x m env in
        (ctx, env, eqns, map)
      else
        (ctx, env, eqns, map))
  | DFun (x, a, abs) ->
    let s, eqns, map = infer_sort ctx env eqns map a in
    let y, cls = unbind_cls abs in
    if s = U then
      let local_ctx = add_v y a ctx in
      let prbm = UVar.prbm_of_cls cls in
      let eqns, map = check_prbm local_ctx env eqns map prbm a in
      let map = UMeta.unify map eqns in
      let abs = UMeta.resolve_cls_abs map abs in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      let env = VMap.add x (Fun (Some a, abs)) env in
      (ctx, env, eqns, map)
    else
      let prbm = UVar.prbm_of_cls cls in
      let eqns, map = check_prbm ctx env eqns map prbm a in
      let map = UMeta.unify map eqns in
      let a = UMeta.resolve_tm map a in
      let ctx = add_v x a ctx in
      (ctx, env, eqns, map)
  | DData (d, ptl, dconss) ->
    let eqns, map = infer_ptl ctx env eqns map ptl U in
    let map = UMeta.unify map eqns in
    let ptl = UMeta.resolve_ptl map ptl in
    let ctx = add_d d ptl [] ctx in
    let eqns, map, cs, ctx =
      List.fold_right
        (fun (DCons (c, ptl)) (eqns, map, acc, ctx) ->
          let eqns, map = infer_ptl ctx env eqns map ptl U in
          let _ = param_ptl ptl d [] in
          let ptl = UMeta.resolve_ptl map ptl in
          let ctx = add_c c ptl ctx in
          (eqns, map, c :: acc, ctx))
        dconss (eqns, map, [], ctx)
    in
    let map = UMeta.unify map eqns in
    let ctx = add_d d ptl cs ctx in
    (ctx, env, eqns, map)
  | DOpen (trg, x) -> (
    match trg with
    | TStdin ->
      let a = Ch (true, Var Prelude.stdin_t) in
      (add_v x a ctx, env, eqns, map)
    | TStdout ->
      let a = Ch (true, Var Prelude.stdout_t) in
      (add_v x a ctx, env, eqns, map)
    | TStderr ->
      let a = Ch (true, Var Prelude.stderr_t) in
      (add_v x a ctx, env, eqns, map))
  | DAxiom (x, a) ->
    let _, eqns, map = infer_sort ctx env eqns map a in
    (add_v x a ctx, env, eqns, map)

and infer_dcls ctx env eqns map dcls =
  match dcls with
  | [] -> (eqns, map)
  | dcl :: dcls ->
    let ctx, env, eqns, map = infer_dcl ctx env eqns map dcl in
    infer_dcls ctx env eqns map dcls

and param_ptl ptl d xs =
  match ptl with
  | PBase a -> param_tl a d (List.rev xs)
  | PBind (_, abs) ->
    let x, ptl = unbind_ptl abs in
    param_ptl ptl d (x :: xs)

and param_tl tl d xs =
  let rec param xs ms =
    match (xs, ms) with
    | [], _ -> ()
    | x :: xs, Var y :: ms ->
      if V.equal x y then
        param xs ms
      else
        failwith "param(%a, %a)" V.pp x V.pp y
    | _ -> failwith "param"
  in
  match tl with
  | TBase b -> (
    match b with
    | Data (d', ms) ->
      if D.equal d d' then
        param xs ms
      else
        failwith "param_tl(%a, %a)" D.pp d D.pp d'
    | _ -> failwith "param_tl")
  | TBind (_, abs) ->
    let _, tl = unbind_tl abs in
    param_tl tl d xs

and infer_tl ctx env eqns map tl s =
  match tl with
  | TBase a ->
    let t, eqns, map = infer_sort ctx env eqns map a in
    if cmp_sort t s then
      (eqns, map)
    else
      failwith "infer_tl"
  | TBind (a, abs) ->
    let x, tl = unbind_tl abs in
    let t, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    infer_tl ctx env eqns map tl (min_sort s t)

and infer_ptl ctx env eqns map ptl s =
  match ptl with
  | PBase tl -> infer_tl ctx env eqns map tl s
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let t, eqns, map = infer_sort ctx env eqns map a in
    let ctx = add_v x a ctx in
    infer_ptl ctx env eqns map ptl (min_sort s t)

and min_sort s1 s2 =
  match s1 with
  | U -> s2
  | L -> s1

and cmp_sort s1 s2 =
  match (s1, s2) with
  | U, L -> false
  | _ -> true

let trans_dcls dcls =
  let ctx =
    { vs = VMap.singleton Prelude.main_v Main
    ; ds = DMap.empty
    ; cs = CMap.empty
    }
  in
  let _, map = infer_dcls ctx VMap.empty [] MMap.empty dcls in
  UMeta.resolve_dcls map dcls
