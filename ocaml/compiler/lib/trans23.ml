open Fmt
open Names
open Syntax2
open Syntax3
open Pprint2
open Pprint3

let extend_env local env = List.map fst local @ env

let pp_local fmt local =
  let rec aux fmt = function
    | [] -> ()
    | [ (x, v) ] -> pf fmt "%a := %a;" V.pp x pp_value v
    | (x, v) :: local -> pf fmt "%a := %a;@;<1 0>%a" V.pp x pp_value v aux local
  in
  pf fmt "@[<v 0>%a@]" aux local

let value_of local = List.map snd local

let findi y ls =
  let rec loop i = function
    | [] -> failwith "findi(%a)" V.pp y
    | x :: xs ->
      if V.equal x y then
        i
      else
        loop (i + 1) xs
  in
  loop 0 ls

let trans_p local p v s =
  let aux local c i = function
    | PVar x -> ([ Mov (x, Proj (v, i)) ], local @ [ (x, Reg x) ])
    | _ -> failwith "trans_p"
  in
  match p with
  | PCons (c, ps) -> (
    let _, instr, local =
      List.fold_left
        (fun (i, instr, local) p ->
          let p_instr, local = aux local c i p in
          (i + 1, instr @ p_instr, local))
        (0, [], local) ps
    in
    match s with
    | U -> (c, instr, local)
    | L -> (c, instr @ [ FreeStruct v ], local))
  | _ -> failwith "trans_p"

let rec trans_tm def local env m =
  match m with
  | Type _ -> (def, [], Zero)
  | Var x -> (
    try
      let v = List.find (fun (y, _) -> V.equal x y) local in
      (def, [], snd v)
    with
    | _ -> (def, [], Env (findi x env)))
  | Pi _ -> (def, [], Zero)
  | Fix abs ->
    let f, x, m = unbind_tm_abs abs in
    let def, instr, v =
      trans_tm def [ (x, Reg x) ] (f :: extend_env local env) m
    in
    let name = V.freshen f in
    let tmp = V.freshen f in
    let proc = { name; arg = Some x; body = instr; return = v } in
    ( def @ [ proc ]
    , [ Clo (tmp, name, List.length env, value_of local) ]
    , Reg tmp )
  | Lam (_, abs) ->
    let f = V.blank () in
    let x, m = unbind_tm abs in
    let def, instr, v =
      trans_tm def [ (x, Reg x) ] (f :: extend_env local env) m
    in
    let name = V.mk "lam" in
    let tmp = V.mk "clo" in
    let proc = { name; arg = Some x; body = instr; return = v } in
    ( def @ [ proc ]
    , [ Clo (tmp, name, List.length env, value_of local) ]
    , Reg tmp )
  | App (s, m, n) ->
    let def, m_instr, m_v = trans_tm def local env m in
    let def, n_instr, n_v = trans_tm def local env n in
    let tmp = V.mk "tmp" in
    let app_instr =
      match s with
      | U -> [ Call (tmp, m_v, n_v) ]
      | L -> [ Call (tmp, m_v, n_v); FreeClo m_v ]
    in
    (def, m_instr @ n_instr @ app_instr, Reg tmp)
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let def, m_instr, m_v = trans_tm def local env m in
    let def, n_instr, n_v = trans_tm def ((x, Reg x) :: local) env n in
    (def, m_instr @ [ Mov (x, m_v) ] @ n_instr, n_v)
  | Data _ -> (def, [], Zero)
  | Cons (c, ms) ->
    let def, ms_instr, ms_v =
      List.fold_left
        (fun (def, ms_instr, ms_v) m ->
          let def, m_instr, m_v = trans_tm def local env m in
          (def, ms_instr @ m_instr, ms_v @ [ m_v ]))
        (def, [], []) ms
    in
    let tmp = V.mk (str "%a" C.pp c) in
    (def, ms_instr @ [ Struct (tmp, C.get_id c, ms_v) ], Reg tmp)
  | Case (s, m, cls) ->
    let def, m_instr, m_v = trans_tm def local env m in
    let tmp = V.mk "case" in
    let def, cls =
      List.fold_left
        (fun (def, cls) (Cl pabs) ->
          let p, rhs = unbindp_tm pabs in
          let c, p_instr, local = trans_p local p m_v s in
          let def, rhs_instr, rhs_v = trans_tm def local env rhs in
          let cl =
            (C.get_id c, p_instr @ rhs_instr @ [ Mov (tmp, rhs_v); Break ])
          in
          (def, cls @ [ cl ]))
        (def, []) cls
    in
    (def, m_instr @ [ Switch (m_v, cls) ], Reg tmp)
  | Absurd -> (def, [], Zero)
  | Main -> (def, [], Zero)
  | Proto -> (def, [], Zero)
  | End -> (def, [], Zero)
  | Act _ -> (def, [], Zero)
  | Ch _ -> (def, [], Zero)
  | Fork (_, m, abs) ->
    let x, n = unbind_tm abs in
    let def, m_instr, m_v = trans_tm def local env m in
    let def, n_instr, n_v = trans_tm def [] (x :: extend_env local env) n in
    let final = V.mk "fork_final" in
    let n_instr = n_instr @ [ Mov (final, n_v); FreeThread ] in
    let res = V.mk "fork_res" in
    let name = V.mk "fork_proc" in
    let proc = { name; arg = None; body = n_instr; return = Reg final } in
    ( def @ [ proc ]
    , m_instr @ [ Open (res, TCh (name, m_v, List.length env, value_of local)) ]
    , Reg res )
  | Send m ->
    let def, instr, ch = trans_tm def local env m in
    let tmp = V.mk "send_clo" in
    (def, instr @ [ Send (tmp, ch) ], Reg tmp)
  | Recv (s, m) ->
    let def, instr, ch = trans_tm def local env m in
    let tag =
      match s with
      | U -> C.get_id Prelude.sig_intro_c
      | L -> C.get_id Prelude.tnsr_intro_c
    in
    let tmp = V.mk "recv_struct" in
    (def, instr @ [ Recv (tmp, ch, tag) ], Reg tmp)
  | Close (r, m) ->
    let tmp = V.mk "unit_struct" in
    if not r then
      let def, instr, ch = trans_tm def local env m in
      (def, instr @ [ Close (tmp, ch) ], Reg tmp)
    else
      let def, instr, ch = trans_tm def local env m in
      (def, instr @ [ Struct (tmp, C.get_id Prelude.tt_c, []) ], Reg tmp)

let trans_dcls dcls =
  let rec aux def local env dcls =
    match dcls with
    | [] -> (def, [], Zero)
    | DTm (x, m) :: dcls ->
      let def, m_instr, m_v = trans_tm def local env m in
      let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
      (def, m_instr @ [ Mov (x, m_v) ] @ instr, v)
    | DData (_, _, _) :: dcls -> aux def local env dcls
    | DOpen (trg, x) :: dcls -> (
      match trg with
      | TStdout ->
        let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
        (def, [ Open (x, TStdout) ] @ instr, v)
      | TStdin ->
        let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
        (def, [ Open (x, TStdin) ] @ instr, v)
      | TStderr ->
        let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
        (def, [ Open (x, TStderr) ] @ instr, v))
    | DAxiom (x, a) :: dcls ->
      let def, instr, v = aux def ((x, Reg x) :: local) env dcls in
      (def, [ Mov (x, Zero) ] @ instr, v)
  in
  aux [] [ (Prelude.main_v, Zero) ] [] dcls