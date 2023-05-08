open Fmt
open Names
open Syntax1
open Equality1
open Pprint1

let pp_map fmt map =
  let aux fmt map =
    VMap.iter (fun x m -> pf fmt "%a := %a@;<1 2>" V.pp x pp_tm m) map
  in
  pf fmt "@[<v 0>map{@;<1 2>%a}@]" aux map

module UVar : sig
  type eqn = Eq of tm VMap.t * tm * tm * tm
  and eqns = eqn list

  type prbm =
    { global : eqns
    ; clause : (eqns * ps * tm_opt) list
    }

  val pp_eqn : Format.formatter -> eqn -> unit
  val pp_eqns : Format.formatter -> eqns -> unit
  val pp_prbm : Format.formatter -> prbm -> unit
  val pp_vmap : Format.formatter -> tm VMap.t -> unit
  val prbm_of_cls : Syntax1.cls -> prbm
  val msubst_tm : tm VMap.t -> tm -> tm
  val unify : eqns -> tm VMap.t
end = struct
  type eqn = Eq of tm VMap.t * tm * tm * tm
  and eqns = eqn list

  type prbm =
    { global : eqns
    ; clause : (eqns * ps * tm_opt) list
    }

  let pp_eqn fmt (Eq (_, m, n, a)) =
    pf fmt "(%a ?= %a : %a)" pp_tm m pp_tm n pp_tm a

  let pp_eqns fmt eqns =
    let rec aux fmt eqns =
      match eqns with
      | [] -> ()
      | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
      | eqn :: eqns -> pf fmt "@[%a@]@;<1 0>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[eqns{@;<1 2>@[%a@]}@]" aux eqns

  let rec pp_clause fmt cls =
    match cls with
    | [] -> ()
    | [ (eqns, ps, rhs) ] ->
      pf fmt "[%a](%a)@;<1 0>=>@;<1 2>%a" pp_eqns eqns (Pprint1.pp_ps ", ") ps
        (option Pprint1.pp_tm) rhs
    | (eqns, ps, rhs) :: cls ->
      pf fmt "[%a](%a)@;<1 0>=>@;<1 2>%a@;<1 0>%a" pp_eqns eqns
        (Pprint1.pp_ps ", ") ps (option Pprint1.pp_tm) rhs pp_clause cls

  let pp_prbm fmt prbm =
    pf fmt
      "@[{@;\
       <1 2>@[global=(@;\
       <1 2>@[%a@])@]@;\
       <1 2>@[clause=(@;\
       <1 2>@[<v 0>%a@])@]@;\
       <1 0>}@]" pp_eqns prbm.global pp_clause prbm.clause

  let pp_vmap fmt vmap =
    let aux fmt vmap =
      VMap.iter (fun x m -> pf fmt "%a := %a@;<1 2>" V.pp x pp_tm m) vmap
    in
    pf fmt "@[<v 0>vmap{@;<1 2>%a}@]" aux vmap

  let rec prbm_of_cls cls : prbm =
    match cls with
    | [] -> { global = []; clause = [] }
    | Syntax1.Cl pabs :: cls ->
      let ps, rhs = Syntax1.unbindp_tm_opt pabs in
      let prbm = prbm_of_cls cls in
      { prbm with clause = ([], ps, rhs) :: prbm.clause }

  let rec simpl (env, m1, m2) =
    if equal rd_all env m1 m2 then
      []
    else
      let m1 = whnf rd_all env m1 in
      let m2 = whnf rd_all env m2 in
      match (m1, m2) with
      | _, Var _ -> [ (env, m1, m2) ]
      | Var _, _ -> [ (env, m2, m1) ]
      | Type s1, Type s2 ->
        if s1 = s2 then
          []
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
        if s1 = s2 then
          let _, b1, b2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, a1, a2) in
          let eqns2 = simpl (env, b1, b2) in
          eqns1 @ eqns2
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
        let _, cls1, cls2 = unbind2_cls abs1 abs2 in
        let eqns1 =
          match (a1_opt, a2_opt) with
          | Some a1, Some a2 -> simpl (env, a1, a2)
          | _ -> []
        in
        let eqns2 =
          List.fold_left2
            (fun acc (Cl pabs1) (Cl pabs2) ->
              let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
              match (m_opt, n_opt) with
              | Some m, Some n -> simpl (env, m, n)
              | None, None -> []
              | _ -> failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2)
            [] cls1 cls2
        in
        eqns1 @ eqns2
      | Let (m1, abs1), Let (m2, abs2) ->
        let _, n1, n2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl (env, n1, n2) in
        eqns1 @ eqns2
      | Data (d1, ms1), Data (d2, ms2) ->
        if D.equal d1 d2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Cons (c1, ms1), Cons (c2, ms2) ->
        if C.equal c1 c2 then
          List.fold_left2
            (fun acc m1 m2 -> acc @ simpl (env, m1, m2))
            [] ms1 ms2
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
        let eqns1 =
          List.fold_left2 (fun acc m1 m2 -> simpl (env, m1, m2)) [] ms1 ms2
        in
        let eqns2 = simpl (env, a1, a2) in
        let eqns3 =
          List.fold_left2
            (fun acc (Cl pabs1) (Cl pabs2) ->
              let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
              match (m_opt, n_opt) with
              | Some m, Some n -> simpl (env, m, n)
              | None, None -> []
              | _ -> failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2)
            [] cls1 cls2
        in
        eqns1 @ eqns2 @ eqns3
      | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
        let eqns1 = simpl (env, m1, m2) in
        let eqns2 = simpl (env, tt1, tt2) in
        let eqns3 = simpl (env, ff1, ff2) in
        eqns1 @ eqns2 @ eqns3
      | Main, Main -> []
      | Proto, Proto -> []
      | End, End -> []
      | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
        if r1 = r2 then
          let _, b1, b2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (env, a1, a2) in
          let eqns2 = simpl (env, b1, b2) in
          eqns1 @ eqns2
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Ch (r1, a1), Ch (r2, a2) ->
        if r1 = r2 then
          simpl (env, a1, a2)
        else
          failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2
      | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
        let _, n1, n2 = unbind2_tm abs1 abs2 in
        let eqns1 = simpl (env, a1, a2) in
        let eqns2 = simpl (env, m1, m2) in
        let eqns3 = simpl (env, n1, n2) in
        eqns1 @ eqns2 @ eqns3
      | Send m1, Send m2 -> simpl (env, m1, m2)
      | Recv m1, Recv m2 -> simpl (env, m1, m2)
      | Close m1, Close m2 -> simpl (env, m1, m2)
      | _ -> failwith "uvar_simpl(%a, %a)" pp_tm m1 pp_tm m2

  let solve map (env, m1, m2) =
    let m1 = whnf rd_all env m1 in
    let m2 = whnf rd_all env m2 in
    match (m1, m2) with
    | _, Var x ->
      if occurs_tm x m1 then
        failwith "solve_occurs (%a, %a)" V.pp x pp_tm m1
      else
        VMap.add x m1 map
    | _ -> failwith "solve(%a, %a)" pp_tm m1 pp_tm m2

  let rec msubst_tm map m =
    match m with
    | Ann (a, m) ->
      let a = msubst_tm map a in
      let m = msubst_tm map m in
      Ann (a, m)
    | Meta (x, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Meta (x, ms)
    | Type s -> Type s
    | Var x -> (
      match VMap.find_opt x map with
      | Some m -> msubst_tm map m
      | None -> Var x)
    | Pi (s, a, abs) ->
      let a = msubst_tm map a in
      let x, b = unbind_tm abs in
      let b = msubst_tm map b in
      Pi (s, a, bind_tm x b)
    | Fun (a_opt, abs) ->
      let a_opt = Option.map (msubst_tm map) a_opt in
      let x, cls = unbind_cls abs in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let p, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (msubst_tm map) m_opt in
            Cl (bindp_tm_opt p m_opt))
          cls
      in
      Fun (a_opt, bind_cls x cls)
    | App (m, n) ->
      let m = msubst_tm map m in
      let n = msubst_tm map n in
      App (m, n)
    | Let (m, abs) ->
      let m = msubst_tm map m in
      let x, n = unbind_tm abs in
      let n = msubst_tm map n in
      Let (m, bind_tm x n)
    | Data (d, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (msubst_tm map) ms in
      Cons (c, ms)
    | Absurd -> Absurd
    | Match (ms, a, cls) ->
      let ms = List.map (msubst_tm map) ms in
      let a = msubst_tm map a in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let p, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (msubst_tm map) m_opt in
            Cl (bindp_tm_opt p m_opt))
          cls
      in
      Match (ms, a, cls)
    | If (m, n1, n2) ->
      let m = msubst_tm map m in
      let n1 = msubst_tm map n1 in
      let n2 = msubst_tm map n2 in
      If (m, n1, n2)
    | Main -> Main
    | Proto -> Proto
    | End -> End
    | Act (r, a, abs) ->
      let a = msubst_tm map a in
      let x, b = unbind_tm abs in
      let b = msubst_tm map b in
      Act (r, a, bind_tm x b)
    | Ch (r, a) ->
      let a = msubst_tm map a in
      Ch (r, a)
    | Fork (a, m, abs) ->
      let a = msubst_tm map a in
      let m = msubst_tm map m in
      let x, n = unbind_tm abs in
      let n = msubst_tm map n in
      Fork (a, m, bind_tm x n)
    | Send m ->
      let m = msubst_tm map m in
      Send m
    | Recv m ->
      let m = msubst_tm map m in
      Recv m
    | Close m ->
      let m = msubst_tm map m in
      Close m

  let unify eqns =
    let eqns = List.map (fun (Eq (env, m, n, _)) -> (env, m, n)) eqns in
    let rec aux map eqns =
      let eqns =
        List.map
          (fun (env, m1, m2) -> (env, msubst_tm map m1, msubst_tm map m2))
          eqns
      in
      match List.concat_map simpl eqns with
      | [] -> map
      | eqn :: eqns ->
        let map = solve map eqn in
        aux map eqns
    in
    aux VMap.empty eqns
end

module UMeta : sig
  type eqn = Eq of tm VMap.t * tm * tm
  and eqns = eqn list

  type map = (tm_opt * tm_opt) MMap.t

  val pp_eqn : Format.formatter -> eqn -> unit
  val pp_eqns : Format.formatter -> eqns -> unit
  val resolve_tm : map -> tm -> tm
  val resolve_cls_abs : map -> cls abs -> cls abs
  val resolve_tl : map -> tl -> tl
  val resolve_ptl : map -> ptl -> ptl
  val resolve_dcons : map -> dcons -> dcons
  val resolve_dcl : map -> dcl -> dcl
  val resolve_dcls : map -> dcls -> dcls
  val unify : map -> eqns -> map
end = struct
  type eqn = Eq of tm VMap.t * tm * tm
  and eqns = eqn list

  type map = (tm_opt * tm_opt) MMap.t

  let pp_eqn fmt (Eq (_, m, n)) = pf fmt "%a ?= %a" pp_tm m pp_tm n

  let pp_eqns fmt eqns =
    let rec aux fmt eqns =
      match eqns with
      | [] -> ()
      | [ eqn ] -> pf fmt "@[%a@]" pp_eqn eqn
      | eqn :: eqns -> pf fmt "@[%a@]@;<1 2>%a" pp_eqn eqn aux eqns
    in
    pf fmt "@[<v 0>eqns{@;<1 2>%a}@]" aux eqns

  let rec fv ctx m =
    match m with
    | Ann (a, m) -> VSet.union (fv ctx a) (fv ctx m)
    | Meta (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Type _ -> VSet.empty
    | Var x -> (
      match VSet.find_opt x ctx with
      | Some _ -> VSet.empty
      | None -> VSet.singleton x)
    | Pi (_, a, abs) ->
      let x, b = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv (VSet.add x ctx) b in
      VSet.union fv1 fv2
    | Fun (a_opt, abs) ->
      let x, cls = unbind_cls abs in
      let fv1 =
        match a_opt with
        | Some a -> fv ctx a
        | None -> VSet.empty
      in
      let fv2 =
        List.fold_left
          (fun acc (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let xs = xs_of_ps ps in
            let ctx = VSet.union (VSet.of_list (x :: xs)) ctx in
            match m_opt with
            | Some m -> VSet.union acc (fv ctx m)
            | None -> acc)
          VSet.empty cls
      in
      VSet.union fv1 fv2
    | App (m, n) -> VSet.union (fv ctx m) (fv ctx n)
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let fv1 = fv ctx m in
      let fv2 = fv (VSet.add x ctx) n in
      VSet.union fv1 fv2
    | Data (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Cons (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
    | Absurd -> VSet.empty
    | Match (ms, a, cls) ->
      let fv1 =
        List.fold_left (fun acc m -> VSet.union acc (fv ctx m)) VSet.empty ms
      in
      let fv2 = fv ctx a in
      let fv3 =
        List.fold_left
          (fun acc (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let xs = xs_of_ps ps in
            let ctx = VSet.union (VSet.of_list xs) ctx in
            match m_opt with
            | Some m -> VSet.union acc (fv ctx m)
            | None -> acc)
          VSet.empty cls
      in
      VSet.union (VSet.union fv1 fv2) fv3
    | If (m, tt, ff) ->
      let fv1 = fv ctx m in
      let fv2 = fv ctx tt in
      let fv3 = fv ctx ff in
      VSet.union (VSet.union fv1 fv2) fv3
    | Main -> VSet.empty
    | Proto -> VSet.empty
    | End -> VSet.empty
    | Act (_, a, abs) ->
      let x, b = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv (VSet.add x ctx) b in
      VSet.union fv1 fv2
    | Ch (_, m) -> fv ctx m
    | Fork (a, m, abs) ->
      let x, n = unbind_tm abs in
      let fv1 = fv ctx a in
      let fv2 = fv ctx m in
      let fv3 = fv (VSet.add x ctx) n in
      VSet.union (VSet.union fv1 fv2) fv3
    | Send m -> fv ctx m
    | Recv m -> fv ctx m
    | Close m -> fv ctx m

  let rec occurs x m =
    match m with
    | Ann (a, m) -> occurs x a || occurs x m
    | Meta (y, _) -> M.equal x y
    | Type _ -> false
    | Var y -> false
    | Pi (_, a, abs) ->
      let _, b = unbind_tm abs in
      occurs x a || occurs x b
    | Fun (a_opt, abs) ->
      let _, cls = unbind_cls abs in
      let a_res =
        match a_opt with
        | Some a -> occurs x a
        | None -> false
      in
      a_res
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | App (m, n) -> occurs x m || occurs x n
    | Let (m, abs) ->
      let _, n = unbind_tm abs in
      occurs x m || occurs x n
    | Data (_, ms) -> List.exists (occurs x) ms
    | Cons (_, ms) -> List.exists (occurs x) ms
    | Absurd -> false
    | Match (ms, a, cls) ->
      List.exists (occurs x) ms
      || occurs x a
      || List.exists
           (fun (Cl pabs) ->
             let _, m_opt = unbindp_tm_opt pabs in
             match m_opt with
             | Some m -> occurs x m
             | None -> false)
           cls
    | If (m, tt, ff) -> occurs x m || occurs x tt || occurs x ff
    | Main -> false
    | Proto -> false
    | End -> false
    | Act (_, a, abs) ->
      let _, b = unbind_tm abs in
      occurs x a || occurs x b
    | Ch (_, a) -> occurs x a
    | Fork (a, m, abs) ->
      let _, n = unbind_tm abs in
      occurs x a || occurs x m || occurs x n
    | Send m -> occurs x m
    | Recv m -> occurs x m
    | Close m -> occurs x m

  let rec asimpl (Eq (env, m1, m2)) =
    if equal rd_all env m1 m2 then
      []
    else
      let h1, sp1 = unApps m1 in
      let h2, sp2 = unApps m2 in
      let eqns_sp =
        List.fold_left2
          (fun acc m n ->
            let eqns = asimpl (Eq (env, m, n)) in
            acc @ eqns)
          [] sp1 sp2
      in
      let eqns_h =
        match (h1, h2) with
        | Meta _, _ -> [ Eq (env, m1, m2) ]
        | _, Meta _ -> [ Eq (env, m2, m1) ]
        | Type s1, Type s2 ->
          if s1 = s2 then
            []
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var x1, Var x2 ->
          if V.equal x1 x2 then
            []
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var x, _ -> (
          match VMap.find_opt x env with
          | Some m1 -> asimpl (Eq (env, mkApps m1 sp1, m2))
          | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
        | _, Var y -> (
          match VMap.find_opt y env with
          | Some m2 -> asimpl (Eq (env, m1, mkApps m2 sp2))
          | None -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2)
        | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
          if s1 = s2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = asimpl (Eq (env, a1, a2)) in
            let eqns2 = asimpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
          let _, cls1, cls2 = unbind2_cls abs1 abs2 in
          let eqns1 =
            match (a1_opt, a2_opt) with
            | Some a1, Some a2 -> asimpl (Eq (env, a1, a2))
            | _ -> []
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> asimpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
        | Let (m1, abs1), Let (m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = asimpl (Eq (env, m1, m2)) in
          let eqns2 = asimpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2
        | Data (d1, ms1), Data (d2, ms2) ->
          if D.equal d1 d2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ asimpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Cons (c1, ms1), Cons (c2, ms2) ->
          if C.equal c1 c2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ asimpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
          let eqns1 =
            List.fold_left2
              (fun acc m1 m2 -> asimpl (Eq (env, m1, m2)))
              [] ms1 ms2
          in
          let eqns2 = asimpl (Eq (env, a1, a2)) in
          let eqns3 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> asimpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2 @ eqns3
        | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
          let eqns1 = asimpl (Eq (env, m1, m2)) in
          let eqns2 = asimpl (Eq (env, tt1, tt2)) in
          let eqns3 = asimpl (Eq (env, ff1, ff2)) in
          eqns1 @ eqns2 @ eqns3
        | Main, Main -> []
        | Proto, Proto -> []
        | End, End -> []
        | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
          if r1 = r2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = asimpl (Eq (env, a1, a2)) in
            let eqns2 = asimpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Ch (r1, a1), Ch (r2, a2) ->
          if r1 = r2 then
            asimpl (Eq (env, a1, a2))
          else
            failwith "asimpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = asimpl (Eq (env, a1, a2)) in
          let eqns2 = asimpl (Eq (env, m1, m2)) in
          let eqns3 = asimpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2 @ eqns3
        | Send m1, Send m2 -> asimpl (Eq (env, m1, m2))
        | Recv m1, Recv m2 -> asimpl (Eq (env, m1, m2))
        | Close m1, Close m2 -> asimpl (Eq (env, m1, m2))
        | _ -> failwith "asimpl(%a, %a)" pp_tm m1 pp_tm m2
      in
      eqns_h @ eqns_sp

  let rec simpl (Eq (env, m1, m2)) =
    try asimpl (Eq (env, m1, m2)) with
    | _ ->
      let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
      let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
      let h1, sp1 = unApps m1 in
      let h2, sp2 = unApps m2 in
      let eqns_sp =
        try
          List.fold_left2
            (fun acc m n ->
              let eqns = simpl (Eq (env, m, n)) in
              acc @ eqns)
            [] sp1 sp2
        with
        | _ -> []
      in
      let eqns_h =
        match (h1, h2) with
        | Meta _, _ -> [ Eq (env, m1, m2) ]
        | _, Meta _ -> [ Eq (env, m2, m1) ]
        | Type s1, Type s2 ->
          if s1 = s2 then
            []
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var x1, Var x2 ->
          if V.equal x1 x2 then
            []
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Var x, _ -> (
          match VMap.find_opt x env with
          | Some m1 -> simpl (Eq (env, mkApps m1 sp1, m2))
          | None -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2)
        | _, Var y -> (
          match VMap.find_opt y env with
          | Some m2 -> simpl (Eq (env, m1, mkApps m2 sp2))
          | None -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2)
        | Pi (s1, a1, abs1), Pi (s2, a2, abs2) ->
          if s1 = s2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (Eq (env, a1, a2)) in
            let eqns2 = simpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fun (a1_opt, abs1), Fun (a2_opt, abs2) ->
          let _, cls1, cls2 = unbind2_cls abs1 abs2 in
          let eqns1 =
            match (a1_opt, a2_opt) with
            | Some a1, Some a2 -> simpl (Eq (env, a1, a2))
            | _ -> []
          in
          let eqns2 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2
        | Let (m1, abs1), Let (m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (Eq (env, m1, m2)) in
          let eqns2 = simpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2
        | Data (d1, ms1), Data (d2, ms2) ->
          if D.equal d1 d2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Cons (c1, ms1), Cons (c2, ms2) ->
          if C.equal c1 c2 then
            List.fold_left2
              (fun acc m1 m2 -> acc @ simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Match (ms1, a1, cls1), Match (ms2, a2, cls2) ->
          let eqns1 =
            List.fold_left2
              (fun acc m1 m2 -> simpl (Eq (env, m1, m2)))
              [] ms1 ms2
          in
          let eqns2 = simpl (Eq (env, a1, a2)) in
          let eqns3 =
            List.fold_left2
              (fun acc (Cl pabs1) (Cl pabs2) ->
                let _, m_opt, n_opt = unbindp2_tm_opt pabs1 pabs2 in
                match (m_opt, n_opt) with
                | Some m, Some n -> simpl (Eq (env, m, n))
                | None, None -> []
                | _ -> failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2)
              [] cls1 cls2
          in
          eqns1 @ eqns2 @ eqns3
        | If (m1, tt1, ff1), If (m2, tt2, ff2) ->
          let eqns1 = simpl (Eq (env, m1, m2)) in
          let eqns2 = simpl (Eq (env, tt1, tt2)) in
          let eqns3 = simpl (Eq (env, ff1, ff2)) in
          eqns1 @ eqns2 @ eqns3
        | Main, Main -> []
        | Proto, Proto -> []
        | End, End -> []
        | Act (r1, a1, abs1), Act (r2, a2, abs2) ->
          if r1 = r2 then
            let _, b1, b2 = unbind2_tm abs1 abs2 in
            let eqns1 = simpl (Eq (env, a1, a2)) in
            let eqns2 = simpl (Eq (env, b1, b2)) in
            eqns1 @ eqns2
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Ch (r1, a1), Ch (r2, a2) ->
          if r1 = r2 then
            simpl (Eq (env, a1, a2))
          else
            failwith "umeta_simpl(%a, %a)" pp_tm h1 pp_tm h2
        | Fork (a1, m1, abs1), Fork (a2, m2, abs2) ->
          let _, n1, n2 = unbind2_tm abs1 abs2 in
          let eqns1 = simpl (Eq (env, a1, a2)) in
          let eqns2 = simpl (Eq (env, m1, m2)) in
          let eqns3 = simpl (Eq (env, n1, n2)) in
          eqns1 @ eqns2 @ eqns3
        | Send m1, Send m2 -> simpl (Eq (env, m1, m2))
        | Recv m1, Recv m2 -> simpl (Eq (env, m1, m2))
        | Close m1, Close m2 -> simpl (Eq (env, m1, m2))
        | _ -> failwith "umeta_simpl(%a, %a)" pp_tm m1 pp_tm m2
      in
      eqns_h @ eqns_sp

  let meta_spine sp =
    List.map
      (fun m ->
        match m with
        | Var x -> x
        | _ -> V.blank ())
      sp

  let solve map (Eq (env, m1, m2)) =
    let m1 = whnf [ Beta; Iota; Zeta ] env m1 in
    let m2 = whnf [ Beta; Iota; Zeta ] env m2 in
    match (m1, m2) with
    | Meta _, Meta _ -> map
    | Meta (x, xs), _ ->
      if occurs x m2 then
        failwith "occurs(%a, %a)" M.pp x pp_tm m2
      else
        let xs = meta_spine xs in
        let ctx = fv VSet.empty m2 in
        if VSet.subset ctx (VSet.of_list xs) then
          let m = mLam xs m2 in
          MMap.add x (Some m, None) map
        else
          failwith "solve0(%a{%a} ?= %a)" pp_tm m1 V.pps xs pp_tm m2
    | _ -> failwith "solve1(%a ?= %a)" pp_tm m1 pp_tm m2

  let rec resolve_tm map m =
    match m with
    | Meta (x, xs) -> (
      try
        match MMap.find x map with
        | Some h, _ ->
          let m = mkApps h xs in
          resolve_tm map (whnf [ Beta; Iota; Zeta ] VMap.empty m)
        | _ -> m
      with
      | _ -> m)
    | Ann (a, m) -> Ann (resolve_tm map a, resolve_tm map m)
    | Type _ -> m
    | Var _ -> m
    | Pi (s, a, abs) ->
      let x, b = unbind_tm abs in
      let a = resolve_tm map a in
      let b = resolve_tm map b in
      Pi (s, a, bind_tm x b)
    | Fun (a_opt, abs) ->
      let a_opt = Option.map (resolve_tm map) a_opt in
      Fun (a_opt, resolve_cls_abs map abs)
    | App (m, n) ->
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      App (m, n)
    | Let (m, abs) ->
      let x, n = unbind_tm abs in
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      Let (m, bind_tm x n)
    | Data (d, ms) ->
      let ms = List.map (resolve_tm map) ms in
      Data (d, ms)
    | Cons (c, ms) ->
      let ms = List.map (resolve_tm map) ms in
      Cons (c, ms)
    | Absurd -> m
    | Match (ms, a, cls) ->
      let ms = List.map (resolve_tm map) ms in
      let a = resolve_tm map a in
      let cls =
        List.map
          (fun (Cl pabs) ->
            let ps, m_opt = unbindp_tm_opt pabs in
            let m_opt = Option.map (resolve_tm map) m_opt in
            Cl (bindp_tm_opt ps m_opt))
          cls
      in
      Match (ms, a, cls)
    | If (m, tt, ff) ->
      let m = resolve_tm map m in
      let tt = resolve_tm map tt in
      let ff = resolve_tm map ff in
      If (m, tt, ff)
    | Main -> m
    | Proto -> m
    | End -> m
    | Act (r, a, abs) ->
      let x, b = unbind_tm abs in
      let a = resolve_tm map a in
      let b = resolve_tm map b in
      Act (r, a, bind_tm x b)
    | Ch (r, m) -> Ch (r, resolve_tm map m)
    | Fork (a, m, abs) ->
      let x, n = unbind_tm abs in
      let a = resolve_tm map a in
      let m = resolve_tm map m in
      let n = resolve_tm map n in
      Fork (a, m, bind_tm x n)
    | Send m -> Send (resolve_tm map m)
    | Recv m -> Recv (resolve_tm map m)
    | Close m -> Close (resolve_tm map m)

  and resolve_cls_abs map abs =
    let x, cls = unbind_cls abs in
    let cls =
      List.map
        (fun (Cl pabs) ->
          let ps, m_opt = unbindp_tm_opt pabs in
          let m_opt = Option.map (resolve_tm map) m_opt in
          Cl (bindp_tm_opt ps m_opt))
        cls
    in
    bind_cls x cls

  let rec resolve_tl map tl =
    match tl with
    | TBase b -> TBase (resolve_tm map b)
    | TBind (a, abs) ->
      let x, tl = unbind_tl abs in
      let a = resolve_tm map a in
      let tl = resolve_tl map tl in
      TBind (a, bind_tl x tl)

  let rec resolve_ptl map ptl =
    match ptl with
    | PBase tl -> PBase (resolve_tl map tl)
    | PBind (a, abs) ->
      let x, ptl = unbind_ptl abs in
      let a = resolve_tm map a in
      let ptl = resolve_ptl map ptl in
      PBind (a, bind_ptl x ptl)

  let rec resolve_dcons map (DCons (c, ptl)) = DCons (c, resolve_ptl map ptl)

  let resolve_dcl map dcl =
    match dcl with
    | DTm (x, a_opt, m) ->
      let a_opt = Option.map (resolve_tm map) a_opt in
      let m = resolve_tm map m in
      DTm (x, a_opt, m)
    | DFun (x, a, abs) ->
      let a = resolve_tm map a in
      DFun (x, a, resolve_cls_abs map abs)
    | DData (d, ptl, dconss) ->
      let ptl = resolve_ptl map ptl in
      let dconss = List.map (resolve_dcons map) dconss in
      DData (d, ptl, dconss)
    | DOpen _ -> dcl
    | DAxiom (x, a) -> DAxiom (x, resolve_tm map a)

  let resolve_dcls map dcls = List.map (resolve_dcl map) dcls

  let rec unify map eqns =
    let eqns =
      List.map
        (fun (Eq (env, m1, m2)) ->
          Eq (env, resolve_tm map m1, resolve_tm map m2))
        eqns
    in
    match List.concat_map simpl eqns with
    | [] -> map
    | eqn :: eqns ->
      let map = solve map eqn in
      unify map eqns
end
