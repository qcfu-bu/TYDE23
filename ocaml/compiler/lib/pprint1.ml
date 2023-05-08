open Fmt
open Names
open Syntax1

let rec pp_p fmt p =
  match p with
  | PVar x -> V.pp fmt x
  | PCons (c, []) -> C.pp fmt c
  | PCons (c, ps) -> pf fmt "(%a %a)" C.pp c (pp_ps " ") ps
  | PAbsurd -> pf fmt "absurd"

and pp_ps sep fmt ps =
  match ps with
  | [] -> ()
  | [ p ] -> pp_p fmt p
  | p :: ps -> pf fmt "%a%s%a" pp_p p sep (pp_ps sep) ps

let rec nat_of m =
  match m with
  | Cons (c, []) when C.equal c Prelude.zero_c -> Some 0
  | Cons (c, [ m ]) when C.equal c Prelude.succ_c -> (
    match nat_of m with
    | Some n -> Some (1 + n)
    | None -> None)
  | _ -> None

let bin_of ms =
  List.map
    (fun m ->
      match m with
      | Cons (c, []) when C.equal Prelude.true_c c -> Some 1
      | Cons (c, []) when C.equal Prelude.false_c c -> Some 0
      | _ -> None)
    ms

let dec_of ns =
  List.fold_left
    (fun acc opt ->
      match (acc, opt) with
      | Some acc, Some n -> Some ((acc * 2) + n)
      | _ -> None)
    (Some 0) ns

let char_of m =
  match m with
  | Cons (c, ms) when C.equal Prelude.ascii0_c c -> (
    let n = ms |> bin_of |> dec_of in
    match n with
    | Some n -> Some (Char.chr n)
    | None -> None)
  | _ -> None

let rec string_of m =
  match m with
  | Cons (c, []) when C.equal Prelude.emptyString_c c -> Some ""
  | Cons (c, [ m; n ]) when C.equal Prelude.string0_c c -> (
    match (char_of m, string_of n) with
    | Some c, Some s -> Some (str "%c%s" c s)
    | _ -> None)
  | _ -> None

let pp_sort fmt s =
  match s with
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let rec pp_tm fmt m =
  match m with
  | Ann (a, m) -> pf fmt "@[(@@[%a]@,%a)@]" pp_tm a pp_tm m
  | Meta (x, ms) -> pf fmt "%a" M.pp x
  | Type s -> pp_sort fmt s
  | Var x -> V.pp fmt x
  | Pi (s, a, abs) -> (
    let x, b = unbind_tm abs in
    match (s, occurs_tm x b) with
    | U, false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tm b
    | U, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | L, false -> pf fmt "@[%a -o@;<1 2>%a@]" pp_tm a pp_tm b
    | L, true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) -o@]@;<1 2>%a@]" V.pp x pp_tm a pp_tm b)
  | Fun (a_opt, abs) -> (
    let x, cls = unbind_cls abs in
    match (a_opt, occurs_cls x cls) with
    | Some a, false ->
      pf fmt "@[<v 0>(@[fun : %a@]@;<1 2>%a)@]" pp_tm a (pp_cls " ") cls
    | Some a, true ->
      pf fmt "@[<v 0>(@[fun %a : %a@]@;<1 2>%a)@]" V.pp x pp_tm a (pp_cls " ")
        cls
    | None, false -> pf fmt "@[<v 0>(fun@;<1 2>%a)@]" (pp_cls " ") cls
    | None, true ->
      pf fmt "@[<v 0>(@[fun %a@]@;<1 2>%a)@]" V.pp x (pp_cls " ") cls)
  | App _ ->
    let m, ms = unApps m in
    pf fmt "@[((%a)@;<1 2>@[%a@])@]" pp_tm m (list ~sep:sp pp_tm) ms
  | Let (m, abs) ->
    let x, n = unbind_tm abs in
    pf fmt "@[@[let %a :=@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  | Data (d, ms) -> (
    match ms with
    | [] -> D.pp fmt d
    | _ -> pf fmt "@[(%a@;<1 2>%a)@]" D.pp d (list ~sep:sp pp_tm) ms)
  | Cons (c, ms) -> (
    match ms with
    | [] -> C.pp fmt c
    | _ ->
      if C.equal c Prelude.zero_c || C.equal c Prelude.succ_c then
        match nat_of m with
        | Some n -> pf fmt "%d" n
        | None -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms
      else if C.equal c Prelude.string0_c || C.equal c Prelude.emptyString_c
      then
        match string_of m with
        | Some s -> pf fmt "\"%s\"" (String.escaped s)
        | None -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms
      else if C.equal c Prelude.ascii0_c then
        match char_of m with
        | Some c -> pf fmt "\'%s\'" (Char.escaped c)
        | None -> pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms
      else
        pf fmt "@[(%a@;<1 2>%a)@]" C.pp c (list ~sep:sp pp_tm) ms)
  | Absurd -> pf fmt "absurd"
  | Match (ms, a, cls) ->
    pf fmt
      "@[<v 0>(@[@[match@;\
       <1 2>%a@;\
       <1 0>return@;\
       <1 2>%a@;\
       <1 0>@]with@]@;\
       <1 2>%a)@]" (list ~sep:comma pp_tm) ms pp_tm a (pp_cls ", ") cls
  | If (m, n1, n2) ->
    pf fmt "@[if %a then@;<1 2>%a@.else@;<1 2>%a@]" pp_tm m pp_tm n1 pp_tm n2
  | Main -> pf fmt "@main"
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (r, a, abs) -> (
    let x, b = unbind_tm abs in
    match (r, occurs_tm x b) with
    | true, false -> pf fmt "@[?%a ⋅@;<1 2>%a@]" pp_tm a pp_tm b
    | true, true -> pf fmt "@[?(%a : %a) ⋅@;<1 2>%a@]" V.pp x pp_tm a pp_tm b
    | false, false -> pf fmt "@[!%a ⋅@;<1 2>%a@]" pp_tm a pp_tm b
    | false, true -> pf fmt "@[!(%a : %a) ⋅@;<1 2>%a@]" V.pp x pp_tm a pp_tm b)
  | Ch (r, m) ->
    if r then
      pf fmt "ch‹%a›" pp_tm m
    else
      pf fmt "hc‹%a›" pp_tm m
  | Fork (a, m, abs) ->
    let x, n = unbind_tm abs in
    pf fmt "@[@[fork (%a :@;<1 2>%a) <-@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x
      pp_tm a pp_tm m pp_tm n
  | Send m -> pf fmt "send %a" pp_tm m
  | Recv m -> pf fmt "recv %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m

and pp_tms fmt ms = pf fmt "[%a]" (list ~sep:semi pp_tm) ms

and pp_cl sep fmt (Cl abs) =
  let ps, m_opt = unbindp_tm_opt abs in
  match m_opt with
  | Some m -> pf fmt "| %a =>@;<1 2>%a" (pp_ps sep) ps pp_tm m
  | None -> pf fmt "| %a" (pp_ps sep) ps

and pp_cls sep fmt cls =
  match cls with
  | [] -> ()
  | [ cl ] -> pf fmt "@[%a@]" (pp_cl sep) cl
  | cl :: cls -> pf fmt "@[%a@]@;<1 2>%a" (pp_cl sep) cl (pp_cls sep) cls

let pp_trg fmt targ =
  match targ with
  | TStdin -> pf fmt "@stdin"
  | TStdout -> pf fmt "@stdout"
  | TStderr -> pf fmt "@stderr"

let rec pp_ptl fmt ptl =
  match ptl with
  | PBase tl -> pf fmt ":@;<1 2>%a" pp_tl tl
  | PBind (a, abs) ->
    let x, ptl = unbind_ptl abs in
    pf fmt "(%a : %a) %a" V.pp x pp_tm a pp_ptl ptl

and pp_tl fmt tl =
  match tl with
  | TBase b -> pp_tm fmt b
  | TBind (a, abs) -> (
    let x, tl = unbind_tl abs in
    match occurs_tl x tl with
    | false -> pf fmt "@[%a ->@;<1 2>%a@]" pp_tm a pp_tl tl
    | true ->
      pf fmt "@[@[∀ (%a :@;<1 2>%a) ->@]@;<1 2>%a@]" V.pp x pp_tm a pp_tl tl)

let pp_dcons fmt (DCons (c, ptl)) = pf fmt "| %a %a" C.pp c pp_ptl ptl

let rec pp_dconss fmt dconss =
  match dconss with
  | [] -> ()
  | [ dcons ] -> pf fmt "@[%a@]" pp_dcons dcons
  | dcons :: dconss -> pf fmt "@[%a@]@;<1 2>%a" pp_dcons dcons pp_dconss dconss

let pp_dcl fmt dcl =
  match dcl with
  | DTm (x, a_opt, m) -> (
    match a_opt with
    | Some a ->
      pf fmt "@[def %a :@;<1 2>%a :=@;<1 2>%a@]" V.pp x pp_tm a pp_tm m
    | None -> pf fmt "@[def %a :=@;<1 2>%a@]" V.pp x pp_tm m)
  | DFun (x, a, abs) ->
    let y, cls = unbind_cls abs in
    pf fmt "@[<v 0>@[def (%a := %a) :@;<1 2>%a@]@;<1 2>%a@]" V.pp x V.pp y pp_tm
      a (pp_cls " ") cls
  | DData (d, ptl, dconss) ->
    pf fmt "@[<v 0>@[data %a %a@]@;<1 2>%a@]" D.pp d pp_ptl ptl pp_dconss dconss
  | DOpen (targ, x) -> pf fmt "open %a as %a" pp_trg targ V.pp x
  | DAxiom (x, a) -> pf fmt "@[axiom %a :@;<1 2>%a@]" V.pp x pp_tm a

let rec pp_dcls fmt dcls =
  match dcls with
  | [] -> ()
  | [ dcl ] -> pf fmt "%a@." pp_dcl dcl
  | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl pp_dcls dcls
