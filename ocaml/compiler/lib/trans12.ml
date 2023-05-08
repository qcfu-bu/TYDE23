open Fmt
open Names
open Syntax1
open Pprint1
open Equality1
open Unify1

let pp_usage fmt usage =
  let aux fmt usage =
    VMap.iter (fun x b -> pf fmt "%a ?%b@;<1 2>" V.pp x b) usage
  in
  pf fmt "@[<v 0>{@;<1 2>%a}]" aux usage

let merge usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some false, Some false -> failwith "merge"
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None)
    usage1 usage2

let refine_equal usage1 usage2 =
  VMap.merge
    (fun _ opt1 opt2 ->
      match (opt1, opt2) with
      | Some b1, Some b2 -> Some (b1 && b2)
      | Some true, None -> None
      | None, Some true -> None
      | None, None -> None
      | _ -> failwith "refine_equal")
    usage1 usage2

let assert_empty usage =
  if VMap.for_all (fun _ b -> b) usage then
    ()
  else
    failwith "assert_empty"

let remove x usage s =
  match s with
  | U -> usage
  | L ->
    if VMap.exists (fun y _ -> V.equal x y) usage then
      VMap.remove x usage
    else
      failwith "remove(%a)" V.pp x

type ctx =
  { vs : (sort * tm) VMap.t
  ; ds : (ptl * C.t list) DMap.t
  ; cs : ptl CMap.t
  }

let add_v x s a ctx = { ctx with vs = VMap.add x (s, a) ctx.vs }
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
    VMap.iter
      (fun x (s, a) ->
        pf fmt "@[%a :%a@;<1 2>%a@]@;<1 2>" V.pp x pp_sort s pp_tm a)
      vs
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

let pp_ctx fmt ctx =
  pf fmt "@[<v 0>ctx{@;<1 2>%a@;<1 2>%a@;<1 2>%a}@]" pp_vs ctx.vs pp_ds ctx.ds
    pp_cs ctx.cs

let msubst_ctx map ctx =
  let vs = VMap.map (fun (s, a) -> (s, UVar.msubst_tm map a)) ctx.vs in
  { ctx with vs }

let subst_ctx x ctx m =
  let ctx = { ctx with vs = VMap.remove x ctx.vs } in
  msubst_ctx (VMap.singleton x m) ctx

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.vs |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

let assert_equal env m n =
  if equal rd_all env m n then
    ()
  else
    failwith "@[assert_equal(@;<1 2>%a@;<1 2>!=@;<1 2>%a)@]" pp_tm m pp_tm n

let has_failed f =
  try
    f ();
    false
  with
  | _ -> true

let usage_of_ctx ctx = VMap.map (fun _ -> true) ctx.vs

let trans_sort s =
  match s with
  | U -> Syntax2.U
  | L -> Syntax2.L

let trans_trg trg =
  match trg with
  | TStdin -> Syntax2.TStdin
  | TStdout -> Syntax2.TStdout
  | TStderr -> Syntax2.TStderr

let rec infer_sort ctx env a =
  let srt, a_elab, usage = infer_tm ctx env a in
  match whnf rd_all env srt with
  | Type s ->
    let _ = assert_empty usage in
    (s, a_elab)
  | _ -> failwith "infer_sort(%a : %a)" pp_tm a pp_tm srt

and infer_tm ctx env m : tm * Syntax2.tm * bool VMap.t =
  match m with
  | Ann (a, m) -> (
    let _, _ = infer_sort ctx env a in
    match m with
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let abs = bind_tm x (Ann (a, n)) in
      let m_elab, usage = check_tm ctx env (Let (m, abs)) a in
      (a, m_elab, usage)
    | _ ->
      let m_elab, ctx = check_tm ctx env m a in
      (a, m_elab, ctx))
  | Meta _ -> failwith "infer_tm_Meta(%a)" pp_tm m
  | Type s -> (Type U, Syntax2.Type (trans_sort s), VMap.empty)
  | Var x -> (
    let s, a = find_v x ctx in
    match s with
    | U -> Syntax2.(a, Var x, VMap.empty)
    | L -> Syntax2.(a, Var x, VMap.singleton x false))
  | Pi (s, a, abs) ->
    let x, b = unbind_tm abs in
    let t, a_elab = infer_sort ctx env a in
    let _, b_elab = infer_sort (add_v x t a ctx) env b in
    (Type s, Syntax2.(Pi (trans_sort s, a_elab, bind_tm x b_elab)), VMap.empty)
  | Fun (a_opt, abs) -> (
    match a_opt with
    | Some a ->
      let _ = infer_sort ctx env a in
      let m_elab, usage = check_tm ctx env (Fun (a_opt, abs)) a in
      (a, m_elab, usage)
    | None -> failwith "infer2_Fun(%a)" pp_tm m)
  | App (m, n) -> (
    let a, m_elab, usage1 = infer_tm ctx env m in
    match whnf rd_all env a with
    | Pi (s, a, abs) -> (
      let t, _ = infer_sort ctx env a in
      let n_elab, usage2 = check_tm ctx env n a in
      match t with
      | U ->
        let _ = assert_empty usage2 in
        ( asubst_tm abs (Ann (a, n))
        , Syntax2.(App (trans_sort s, m_elab, n_elab))
        , usage1 )
      | L ->
        ( asubst_tm abs (Ann (a, n))
        , Syntax2.(App (trans_sort s, m_elab, n_elab))
        , merge usage1 usage2 ))
    | _ -> failwith "infer_App(%a)" pp_tm m)
  | Let (m, abs) -> (
    let a, m_elab, usage1 = infer_tm ctx env m in
    let s, _ = infer_sort ctx env a in
    let x, n = unbind_tm abs in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      let b, n_elab, usage = infer_tm (add_v x s a ctx) (VMap.add x m env) n in
      (b, Syntax2.(Let (m_elab, bind_tm x n_elab)), usage)
    | L ->
      let b, n_elab, usage2 = infer_tm (add_v x s a ctx) env n in
      ( b
      , Syntax2.(Let (m_elab, bind_tm x n_elab))
      , merge usage1 (remove x usage2 s) ))
  | Data (d, ms) ->
    let ptl, _ = find_d d ctx in
    let a, ms_elab, usage = check_ptl ctx env ms ptl in
    (a, Syntax2.(Data (d, ms_elab)), usage)
  | Cons (c, ms) ->
    let ptl = find_c c ctx in
    let a, ms_elab, usage = check_ptl ctx env ms ptl in
    (a, Syntax2.(Cons (c, ms_elab)), usage)
  | Absurd -> failwith "infer_Absurd"
  | Match (ms, a, cls) ->
    let _ = infer_sort ctx env a in
    let m_elab, usage = check_tm ctx env (Match (ms, a, cls)) a in
    (a, m_elab, usage)
  | If (m, tt, ff) ->
    let m_elab, usage1 = check_tm ctx env m (Data (Prelude.bool_d, [])) in
    let tt_ty, tt_elab, tt_u = infer_tm ctx env tt in
    let ff_ty, ff_elab, ff_u = infer_tm ctx env ff in
    let _ = assert_equal env tt_ty ff_ty in
    let usage2 = refine_equal tt_u ff_u in
    let tt_cl = Syntax2.(Cl (bindp_tm (PCons (Prelude.true_c, [])) tt_elab)) in
    let ff_cl = Syntax2.(Cl (bindp_tm (PCons (Prelude.false_c, [])) ff_elab)) in
    (tt_ty, Syntax2.(Case (U, m_elab, [ tt_cl; ff_cl ])), merge usage1 usage2)
  | Main -> (Type L, Syntax2.Main, VMap.empty)
  | Proto -> (Type U, Syntax2.Proto, VMap.empty)
  | End -> (Proto, Syntax2.End, VMap.empty)
  | Act (r, a, abs) ->
    let x, b = unbind_tm abs in
    let s, a_elab = infer_sort ctx env a in
    let b_elab, usage = check_tm (add_v x s a ctx) env b Proto in
    let _ = assert_empty usage in
    (Proto, Syntax2.(Act (r, a_elab, bind_tm x b_elab)), VMap.empty)
  | Ch (r, m) ->
    let m_elab, usage = check_tm ctx env m Proto in
    let _ = assert_empty usage in
    (Type L, Syntax2.(Ch (r, m_elab)), VMap.empty)
  | Fork (a, m, abs) -> (
    let _, a_elab = infer_sort ctx env a in
    match whnf rd_all env a with
    | Ch (true, a) ->
      let x, n = unbind_tm abs in
      let _, usage1 = check_tm ctx env a Proto in
      let m_elab, usage2 = check_tm ctx env m Main in
      let unit = Data (Prelude.unit_d, []) in
      let n_elab, usage3 = check_tm (add_v x L (Ch (true, a)) ctx) env n unit in
      let usage3 = remove x usage3 L in
      let a = Ch (false, a) in
      let _ = assert_empty usage1 in
      ( Data (Prelude.tnsr_d, [ a; Main ])
      , Syntax2.(Fork (a_elab, m_elab, bind_tm x n_elab))
      , merge usage2 usage3 )
    | _ -> failwith "infer_Fork(%a)" pp_tm a)
  | Send m -> (
    let a, m_elab, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 <> r2 ->
      let x, b = unbind_tm abs in
      let abs = bind_tm x (Ch (r1, b)) in
      (Pi (L, a, abs), Syntax2.(Send m_elab), usage)
    | _ -> failwith "infer_Send(%a)" pp_tm a)
  | Recv m -> (
    let a, m_elab, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r1, Act (r2, a, abs)) when r1 = r2 -> (
      let x, b = unbind_tm abs in
      let s, _ = infer_sort ctx env a in
      match s with
      | U ->
        ( Data (Prelude.sig_d, [ a; lam x (Ch (r1, b)) ])
        , Syntax2.(Recv (trans_sort s, m_elab))
        , usage )
      | L ->
        ( Data (Prelude.tnsr_d, [ a; Ch (r1, b) ])
        , Syntax2.(Recv (trans_sort s, m_elab))
        , usage ))
    | _ -> failwith "infer_Recv(%a)" pp_tm a)
  | Close m -> (
    let a, m_elab, usage = infer_tm ctx env m in
    match whnf rd_all env a with
    | Ch (r, End) ->
      (Data (Prelude.unit_d, []), Syntax2.(Close (r, m_elab)), usage)
    | a -> failwith "infer_Close(%a)" pp_tm a)

and check_ptl ctx env ms ptl =
  match (ms, ptl) with
  | m :: ms, PBind (a, abs) -> (
    let s, _ = infer_sort ctx env a in
    let m_elab, usage1 = check_tm ctx env m a in
    let a, ms_elab, usage2 =
      check_ptl ctx env ms (asubst_ptl abs (Ann (a, m)))
    in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      (a, m_elab :: ms_elab, usage2)
    | L -> (a, m_elab :: ms_elab, merge usage1 usage2))
  | ms, PBase tl -> check_tl ctx env ms tl
  | _ -> failwith "check_ptl(%a, %a)" pp_tms ms pp_ptl ptl

and check_tl ctx env ms tl =
  match (ms, tl) with
  | m :: ms, TBind (a, abs) -> (
    let s, _ = infer_sort ctx env a in
    let m_elab, usage1 = check_tm ctx env m a in
    let a, ms_elab, usage2 = check_tl ctx env ms (asubst_tl abs (Ann (a, m))) in
    match s with
    | U ->
      let _ = assert_empty usage1 in
      (a, m_elab :: ms_elab, usage2)
    | L -> (a, m_elab :: ms_elab, merge usage1 usage2))
  | [], TBase a ->
    let _ = infer_sort ctx env a in
    (a, [], VMap.empty)
  | _ -> failwith "check_tl(%a, %a)" pp_tms ms pp_tl tl

and check_tm ctx env m a : Syntax2.tm * bool VMap.t =
  match m with
  | Fun (b_opt, abs) ->
    let s, _ =
      match b_opt with
      | Some b ->
        let s = infer_sort ctx env b in
        let _ = assert_equal env a b in
        s
      | None -> infer_sort ctx env a
    in
    let x, cls = unbind_cls abs in
    let prbm = UVar.prbm_of_cls cls in
    let ctx, opt =
      match s with
      | U -> (add_v x s a ctx, Some x)
      | L -> (ctx, None)
    in
    check_prbm ctx env prbm a opt
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let abs = bind_tm x (Ann (a, n)) in
    let b, m_elab, usage = infer_tm ctx env (Let (m, abs)) in
    let _ = assert_equal env a b in
    (m_elab, usage)
  | Cons (c, ms) -> (
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
      let b, ms_elab, usage = check_ptl ctx env ms ptl in
      let _ = assert_equal env a b in
      (Syntax2.(Cons (c, ms_elab)), usage)
    | _ ->
      let b, m_elab, usage = infer_tm ctx env m in
      let _ = assert_equal env a b in
      (m_elab, usage))
  | Match (ms, b, cls) ->
    let ms_ty, ms_elab, usage1 =
      List.fold_left
        (fun (ms_ty, ms_elab, acc) m ->
          let m_ty, m_elab, usage = infer_tm ctx env m in
          (m_ty :: ms_ty, m_elab :: ms_elab, merge usage acc))
        ([], [], VMap.empty) ms
    in
    let mot =
      List.fold_left
        (fun acc m_ty -> Pi (L, m_ty, bind_tm (V.blank ()) acc))
        b ms_ty
    in
    let _ = infer_sort ctx env mot in
    let prbm = UVar.prbm_of_cls cls in
    let ct, usage2 = check_prbm ctx env prbm mot None in
    let _ = assert_equal env a b in
    (Syntax2.(mkApps L ct (List.rev ms_elab)), merge usage1 usage2)
  | _ ->
    let b, m_elab, usage = infer_tm ctx env m in
    let _ = assert_equal env a b in
    (m_elab, usage)

and tl_of_ptl ptl ns =
  match (ptl, ns) with
  | PBind (a, abs), n :: ns ->
    let ptl = asubst_ptl abs (Ann (a, n)) in
    tl_of_ptl ptl ns
  | PBase tl, _ -> tl
  | _ -> failwith "tl_of_ptl"

and check_prbm ctx env prbm a opt =
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
  let fail_on_d ctx d ns s a =
    let _, cs = find_d d ctx in
    let ptls = List.map (fun c -> find_c c ctx) cs in
    let rec loop = function
      | [] -> (Syntax2.Absurd, usage_of_ctx ctx)
      | ptl :: ptls ->
        let tl = tl_of_ptl ptl ns in
        let _, targ = fold_tl (fun () a x tl -> ((), tl)) () tl in
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
      (Syntax2.Absurd, usage_of_ctx ctx)
    else
      match whnf rd_all env a with
      | Pi (_, a, _) -> (
        let s, _ = infer_sort ctx env a in
        match whnf rd_all env a with
        | Data (d, ns) -> fail_on_d ctx d ns s a
        | _ -> failwith "check_Empty")
      | _ -> failwith "check_Empty")
  | (es, ps, rhs) :: _ when is_absurd es rhs -> (
    if has_failed (fun () -> UVar.unify prbm.global) then
      (Syntax2.Absurd, usage_of_ctx ctx)
    else
      let a = get_absurd es in
      let s, _ = infer_sort ctx env a in
      match whnf rd_all env a with
      | Data (d, ns) -> fail_on_d ctx d ns s a
      | _ -> failwith "check_Absurd")
  | (es, ps, rhs) :: _ when can_split es -> (
    let x, b = first_split es in
    let s, _ = infer_sort ctx env b in
    match whnf rd_all env b with
    | Data (d, ns) ->
      let _, cs = find_d d ctx in
      let ptls = List.map (fun c -> find_c c ctx) cs in
      let usage, cls =
        List.fold_left2
          (fun (acc, cls) ptl c ->
            let tl = tl_of_ptl ptl ns in
            let (ctx, xs), targ =
              fold_tl
                (fun (ctx, acc) a x tl ->
                  let s, _ = infer_sort ctx env a in
                  let ctx = add_v x s a ctx in
                  ((ctx, (x, s) :: acc), tl))
                (ctx, []) tl
            in
            let xs = List.rev xs in
            let var_args = List.map (fun (x, _) -> Var x) xs in
            let pvar_args = List.map (fun (x, _) -> Syntax2.PVar x) xs in
            let cons = Ann (targ, Cons (c, var_args)) in
            let a = subst_tm x a cons in
            let ctx = subst_ctx x ctx cons in
            let prbm = prbm_subst ctx x prbm cons in
            let prbm =
              UVar.
                { prbm with global = Eq (env, b, targ, Type s) :: prbm.global }
            in
            let ct, usage = check_prbm ctx env prbm a opt in
            let usage =
              List.fold_left (fun acc (x, s) -> remove x acc s) usage xs
            in
            let usage =
              match s with
              | U -> usage
              | L -> VMap.add x false usage
            in
            let cl = Syntax2.(Cl (bindp_tm (PCons (c, pvar_args)) ct)) in
            (refine_equal acc usage, cl :: cls))
          (usage_of_ctx ctx, [])
          ptls cs
      in
      (Syntax2.(Case (trans_sort s, Var x, List.rev cls)), usage)
    | _ -> failwith "check_Split(%a)" pp_tm b)
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
    let _ = infer_sort ctx env a in
    check_tm ctx env rhs a
  | (es, ps, rhs) :: clause -> (
    let a = whnf rd_all env a in
    match (a, ps) with
    | Pi (s, a, abs), p :: ps -> (
      let x, b = unbind_tm abs in
      let t, _ = infer_sort ctx env a in
      let ctx = add_v x t a ctx in
      let prbm = prbm_add ctx env prbm x a in
      let ct, usage = check_prbm ctx env prbm b None in
      let usage = remove x usage t in
      match (s, opt) with
      | U, Some f ->
        let _ = assert_empty usage in
        (Syntax2.(Fix (bind_tm_abs f x ct)), VMap.empty)
      | U, None ->
        let _ = assert_empty usage in
        (Syntax2.(Lam (trans_sort s, bind_tm x ct)), VMap.empty)
      | L, _ -> (Syntax2.(Lam (trans_sort s, bind_tm x ct)), usage))
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

and prbm_subst ctx x prbm m =
  match prbm.clause with
  | [] -> prbm
  | (es, ps, rhs) :: clause -> (
    let prbm = prbm_subst ctx x { prbm with clause } m in
    let opt =
      List.fold_left
        (fun acc (UVar.Eq (env, l, r, a)) ->
          match acc with
          | Some acc -> (
            let l = subst_tm x l m in
            let a = subst_tm x a m in
            match p_simpl ctx env l r a with
            | Some es -> Some (acc @ es)
            | None -> None)
          | None -> None)
        (Some []) es
    in
    match opt with
    | Some es -> { prbm with clause = (es, ps, rhs) :: prbm.clause }
    | _ -> prbm)

and p_simpl ctx env m n a =
  let m = whnf rd_all env m in
  let n = whnf rd_all env n in
  let a = whnf rd_all env a in
  match (m, n, a) with
  | Cons (c1, xs), Cons (c2, ys), Data (d, ns) ->
    if C.equal c1 c2 then
      let _, cs = find_d d ctx in
      if List.exists (fun c -> c = c1) cs then
        let ptl = find_c c1 ctx in
        let tl = tl_of_ptl ptl ns in
        ps_simpl_tl ctx env xs ys tl
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

and ps_simpl_tl ctx env ms ns tl =
  match (ms, ns, tl) with
  | m :: ms, n :: ns, TBind (a, abs) -> (
    let opt1 = p_simpl ctx env m n a in
    let tl = asubst_tl abs m in
    let opt2 = ps_simpl_tl ctx env ms ns tl in
    match (opt1, opt2) with
    | Some es1, Some es2 -> Some (es1 @ es2)
    | _ -> None)
  | [], [], TBase _ -> Some []
  | _ -> None

let rec infer_dcls ctx env dcls =
  match dcls with
  | [ DTm (x, a_opt, m) ] -> (
    match a_opt with
    | Some a ->
      let _ = infer_sort ctx env a in
      let _ = assert_equal env a Main in
      let m_elab, usage = check_tm ctx env m a in
      Syntax2.([ DTm (x, m_elab) ], usage)
    | None ->
      let m_elab, usage = check_tm ctx env m Main in
      Syntax2.([ DTm (x, m_elab) ], usage))
  | DTm (x, a_opt, m) :: dcls -> (
    match a_opt with
    | Some a -> (
      let s, _ = infer_sort ctx env a in
      let m_elab, usage1 = check_tm ctx env m a in
      match s with
      | U ->
        let _ = assert_empty usage1 in
        let dcls_elab, usage =
          infer_dcls (add_v x s a ctx) (VMap.add x m env) dcls
        in
        Syntax2.(DTm (x, m_elab) :: dcls_elab, usage)
      | L ->
        let dcls_elab, usage2 = infer_dcls (add_v x s a ctx) env dcls in
        Syntax2.(DTm (x, m_elab) :: dcls_elab, merge usage1 (remove x usage2 s))
      )
    | None -> (
      let a, m_elab, usage1 = infer_tm ctx env m in
      let s, _ = infer_sort ctx env a in
      match s with
      | U ->
        let _ = assert_empty usage1 in
        let dcls_elab, usage =
          infer_dcls (add_v x s a ctx) (VMap.add x m env) dcls
        in
        Syntax2.(DTm (x, m_elab) :: dcls_elab, usage)
      | L ->
        let dcls_elab, usage2 = infer_dcls (add_v x s a ctx) env dcls in
        Syntax2.(DTm (x, m_elab) :: dcls_elab, merge usage1 (remove x usage2 s))
      ))
  | DFun (x, a, abs) :: dcls ->
    let s, _ = infer_sort ctx env a in
    let y, cls = unbind_cls abs in
    if s = U then
      let ctx1 = add_v y s a ctx in
      let prbm = UVar.prbm_of_cls cls in
      let ct, usage = check_prbm ctx1 env prbm a (Some y) in
      let ctx = add_v x s a ctx in
      let env = VMap.add x (Fun (Some a, abs)) env in
      let _ = assert_empty usage in
      let dcls_elab, usage = infer_dcls ctx env dcls in
      Syntax2.(DTm (x, ct) :: dcls_elab, usage)
    else
      let prbm = UVar.prbm_of_cls cls in
      let ct, usage1 = check_prbm ctx env prbm a None in
      let dcls_elab, usage2 = infer_dcls (add_v x s a ctx) env dcls in
      Syntax2.(DTm (x, ct) :: dcls_elab, merge usage1 (remove x usage2 s))
  | DData (d, ptl, dconss) :: dcls ->
    let ptl_elab = infer_ptl ctx env ptl U in
    let ctx = add_d d ptl [] ctx in
    let dconss_elab, cs, ctx =
      List.fold_right
        (fun (DCons (c, ptl)) (dconss_elab, acc, ctx) ->
          let ptl_elab = infer_ptl ctx env ptl U in
          let _ = param_ptl ptl d [] in
          let ctx = add_c c ptl ctx in
          (Syntax2.DCons (c, ptl_elab) :: dconss_elab, c :: acc, ctx))
        dconss ([], [], ctx)
    in
    let ctx = add_d d ptl cs ctx in
    let dcls_elab, usage = infer_dcls ctx env dcls in
    Syntax2.(DData (d, ptl_elab, dconss_elab) :: dcls_elab, usage)
  | DOpen (trg, x) :: dcls -> (
    match trg with
    | TStdin ->
      let a = Ch (true, Var Prelude.stdin_t) in
      let dcls_elab, usage = infer_dcls (add_v x L a ctx) env dcls in
      Syntax2.(DOpen (trans_trg trg, x) :: dcls_elab, remove x usage L)
    | TStdout ->
      let a = Ch (true, Var Prelude.stdout_t) in
      let dcls_elab, usage = infer_dcls (add_v x L a ctx) env dcls in
      Syntax2.(DOpen (trans_trg trg, x) :: dcls_elab, remove x usage L)
    | TStderr ->
      let a = Ch (true, Var Prelude.stderr_t) in
      let dcls_elab, usage = infer_dcls (add_v x L a ctx) env dcls in
      Syntax2.(DOpen (trans_trg trg, x) :: dcls_elab, remove x usage L))
  | DAxiom (x, a) :: dcls ->
    let s, a_elab = infer_sort ctx env a in
    let dcls_elab, usage = infer_dcls (add_v x s a ctx) env dcls in
    Syntax2.(DAxiom (x, a_elab) :: dcls_elab, remove x usage s)
  | [] -> failwith "infer_dcls"

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

and infer_tl ctx env tl s =
  match tl with
  | TBase a ->
    let t, a = infer_sort ctx env a in
    if cmp_sort t s then
      Syntax2.TBase a
    else
      failwith "infer_tl"
  | TBind (a, abs) ->
    let x, tl = unbind_tl abs in
    let t, a_elab = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    let tl_elab = infer_tl ctx env tl (min_sort s t) in
    Syntax2.(TBind (a_elab, bind_tl x tl_elab))

and infer_ptl ctx env ptl s =
  match ptl with
  | PBase tl -> Syntax2.PBase (infer_tl ctx env tl s)
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    let t, a_elab = infer_sort ctx env a in
    let ctx = add_v x t a ctx in
    let ptl = infer_ptl ctx env ptl (min_sort s t) in
    Syntax2.(PBind (a_elab, bind_ptl x ptl))

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
    { vs = VMap.singleton Prelude.main_v (L, Main)
    ; ds = DMap.empty
    ; cs = CMap.empty
    }
  in
  let dcls_elab, usage = infer_dcls ctx VMap.empty dcls in
  let _ = refine_equal (VMap.singleton Prelude.main_v false) usage in
  dcls_elab