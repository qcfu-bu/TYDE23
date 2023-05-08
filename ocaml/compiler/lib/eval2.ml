open Fmt
open Names
open MParser
open Parser0
open Syntax2
open Pprint2
open Thread
open Event

type ch =
  | Channel of (value channel[@opaque])
  | Stdin of bool
  | Stdout of bool
  | Stderr of bool
[@@deriving show { with_path = false }]

and value =
  | VBox
  | VCons of C.t * values
  | VLam of V.t * tm * env
  | VFix of V.t * V.t * tm * env
  | VCh of ch
  | VSend of ch

and values = value list
and res = (V.t * value) list
and env = (value VMap.t[@opaque])

let bin_of ms =
  List.map
    (fun m ->
      match m with
      | VCons (c, []) when C.equal Prelude.true_c c -> 1
      | VCons (c, []) when C.equal Prelude.false_c c -> 0
      | _ -> failwith "bin_of")
    ms

let dec_of ns = List.fold_left (fun acc n -> (acc * 2) + n) 0 ns

let char_of m =
  match m with
  | VCons (c, ms) when C.equal Prelude.ascii0_c c ->
    let n = ms |> bin_of |> dec_of in
    Char.chr n
  | _ -> failwith "char_of"

let rec string_of m =
  match m with
  | VCons (c, []) when C.equal Prelude.emptyString_c c -> ""
  | VCons (c, [ m; n ]) when C.equal Prelude.string0_c c ->
    let c = char_of m in
    let s = string_of n in
    str "%c%s" c s
  | _ -> failwith "string_of(%a)" pp_value m

let of_string s =
  let rec aux m =
    match m with
    | Syntax1.Cons (id, ms) -> Cons (id, List.map aux ms)
    | _ -> failwith "of_string"
  in
  match parse_string (asciix_parser ()) s Prelude.state0 with
  | Success m ->
    let m = Trans01.trans_tm Prelude.nspc Prelude.cs m in
    aux m
  | Failed (s, _) -> failwith "%s" s

let rec mk_env env p m =
  match (p, m) with
  | PVar x, m -> VMap.add x m env
  | PCons (c1, ps), VCons (c2, ms) ->
    if C.equal c1 c2 then
      List.fold_left2 (fun acc p m -> mk_env acc p m) env ps ms
    else
      failwith "mk_env"
  | _ -> failwith "mk_env"

let rec eval_tm env m =
  match m with
  | Type _ -> VBox
  | Var x -> (
    try VMap.find x env with
    | _ -> failwith "eval_Var(%a)" V.pp x)
  | Pi _ -> VBox
  | Fix abs ->
    let f, x, m = unbind_tm_abs abs in
    VFix (f, x, m, env)
  | Lam (_, abs) ->
    let x, m = unbind_tm abs in
    VLam (x, m, env)
  | App (_, m, n) -> (
    let m = eval_tm env m in
    let n = eval_tm env n in
    match m with
    | VLam (x, m, local) ->
      let local = VMap.add x n local in
      eval_tm local m
    | VFix (f, x, m, local) ->
      let local = VMap.add f (VFix (f, x, m, local)) local in
      let local = VMap.add x n local in
      eval_tm local m
    | VSend m -> (
      match m with
      | Channel ch ->
        let _ = sync (send ch n) in
        VCh m
      | Stdin false -> VCh (Stdin true)
      | Stdout false -> VCh (Stdout true)
      | Stdout true ->
        let _ = pr "%s%!" (string_of n) in
        VCh (Stdout false)
      | Stderr false -> VCh (Stderr true)
      | Stderr true ->
        let _ = epr "%s%!" (string_of n) in
        VCh (Stderr false)
      | _ -> failwith "eval_App(%a)" pp_ch m)
    | _ -> failwith "eval_App(%a)" pp_value m)
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    let m = eval_tm env m in
    let env = VMap.add x m env in
    eval_tm env n
  | Data _ -> VBox
  | Cons (c, ms) ->
    let ms = List.map (eval_tm env) ms in
    VCons (c, ms)
  | Case (s, m, cls) -> (
    let v = eval_tm env m in
    let opt =
      List.fold_left
        (fun opt (Cl pabs) ->
          match opt with
          | Some _ -> opt
          | None -> (
            try
              let p, rhs = unbindp_tm pabs in
              let env = mk_env env p v in
              Some (eval_tm env rhs)
            with
            | _ -> None))
        None cls
    in
    match opt with
    | Some m -> m
    | None -> failwith "eval_Case(%a)" pp_tm (Case (s, m, cls)))
  | Absurd -> failwith "eval_Absurd"
  | Main -> VBox
  | Proto -> VBox
  | End -> VBox
  | Act _ -> VBox
  | Ch _ -> VBox
  | Fork (_, m, abs) ->
    let x, n = unbind_tm abs in
    let m = eval_tm env m in
    let ch = VCh (Channel (new_channel ())) in
    let env = VMap.add x ch env in
    let _ = create (fun env -> eval_tm env n) env in
    VCons (Prelude.tnsr_intro_c, [ ch; m ])
  | Send m -> (
    let m = eval_tm env m in
    match m with
    | VCh ch -> VSend ch
    | m -> failwith "eval_Send(%a)" pp_value m)
  | Recv (s, m) -> (
    let m = eval_tm env m in
    let c =
      match s with
      | U -> Prelude.sig_intro_c
      | L -> Prelude.tnsr_intro_c
    in
    match m with
    | VCh (Channel ch) ->
      let n = sync (receive ch) in
      VCons (c, [ n; m ])
    | VCh (Stdin true) ->
      let s = read_line () |> of_string |> eval_tm env in
      VCons (c, [ s; VCh (Stdin false) ])
    | _ -> failwith "eval_Recv")
  | Close _ -> VCons (Prelude.tt_c, [])

let eval_dcls dcls =
  let env = VMap.singleton Prelude.main_v VBox in
  let rec aux env dcls =
    match dcls with
    | [] -> []
    | DTm (x, m) :: dcls ->
      let m = eval_tm env m in
      let dcls = aux (VMap.add x m env) dcls in
      (x, m) :: dcls
    | DOpen (trg, x) :: dcls -> (
      match trg with
      | TStdin -> aux (VMap.add x (VCh (Stdin false)) env) dcls
      | TStdout -> aux (VMap.add x (VCh (Stdout false)) env) dcls
      | TStderr -> aux (VMap.add x (VCh (Stderr false)) env) dcls)
    | DData _ :: dcls -> aux env dcls
    | DAxiom (x, _) :: dcls -> aux (VMap.add x VBox env) dcls
  in
  aux env dcls