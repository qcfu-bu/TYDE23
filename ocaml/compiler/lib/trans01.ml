open Fmt
open Names
open Syntax0

type entry =
  | V of V.t
  | D of D.t
  | C of C.t

type nspc = (string * entry) list

let trans_id_opt id_opt =
  match id_opt with
  | Some id -> V.mk id
  | None -> V.blank ()

let trans_sort s =
  match s with
  | U -> Syntax1.U
  | L -> Syntax1.L

let rec spine_of_nspc nspc =
  List.fold_left
    (fun acc (_, entry) ->
      match entry with
      | V x -> Syntax1.Var x :: acc
      | D _ -> acc
      | C _ -> acc)
    [] nspc

let rec trans_p nspc cs p =
  match p with
  | PVar id_opt -> (
    let x = trans_id_opt id_opt in
    match id_opt with
    | Some id -> ((id, V x) :: nspc, Syntax1.PVar x)
    | None -> (("", V x) :: nspc, Syntax1.PVar x))
  | PCons (id, ps) -> (
    match SMap.find_opt id cs with
    | Some c ->
      let nspc, ps = trans_ps nspc cs ps in
      (nspc, Syntax1.PCons (c, ps))
    | _ -> failwith "trans_of_p")
  | PAbsurd -> (nspc, Syntax1.PAbsurd)

and trans_ps nspc cs ps =
  match ps with
  | [] -> (nspc, [])
  | p :: ps ->
    let nspc, p = trans_p nspc cs p in
    let nspc, ps = trans_ps nspc cs ps in
    (nspc, p :: ps)

let rec trans_tm nspc cs m =
  match m with
  | Ann (a, m) ->
    let a = trans_tm nspc cs a in
    let m = trans_tm nspc cs m in
    Syntax1.Ann (a, m)
  | Type s -> Syntax1.Type (trans_sort s)
  | Id "_" -> Syntax1.Meta (M.mk (), spine_of_nspc nspc)
  | Id id -> (
    match List.assoc_opt id nspc with
    | Some (V x) -> Syntax1.Var x
    | Some (D d) -> Syntax1.Data (d, [])
    | Some (C c) -> Syntax1.Cons (c, [])
    | _ -> failwith "trans_tm unbound(%s)" id)
  | Pi (s, args, b) ->
    let nspc, args =
      List.fold_left
        (fun (nspc, acc) (id_opt, a) ->
          let a = trans_tm nspc cs a in
          let x = trans_id_opt id_opt in
          match id_opt with
          | Some id -> ((id, V x) :: nspc, (x, a) :: acc)
          | None -> (nspc, (x, a) :: acc))
        (nspc, []) args
    in
    List.fold_right
      (fun (x, a) acc ->
        let b = Syntax1.bind_tm x acc in
        Syntax1.Pi (trans_sort s, a, b))
      (List.rev args) (trans_tm nspc cs b)
  | Fun (id_opt, a_opt, cls) -> (
    let a_opt = Option.map (trans_tm nspc cs) a_opt in
    let x = trans_id_opt id_opt in
    match id_opt with
    | Some id ->
      let cls = trans_cls ((id, V x) :: nspc) cs cls in
      Fun (a_opt, Syntax1.bind_cls x cls)
    | None ->
      let cls = trans_cls nspc cs cls in
      Fun (a_opt, Syntax1.bind_cls x cls))
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      let ms = List.map (trans_tm nspc cs) ms in
      match List.assoc_opt id nspc with
      | Some (V x) -> Syntax1.mkApps (Var x) ms
      | Some (D d) -> Data (d, ms)
      | Some (C c) -> Cons (c, ms)
      | None -> failwith "trans_tm(%a)" pp_tm m)
    | m :: ms ->
      let m = trans_tm nspc cs m in
      let ms = List.map (trans_tm nspc cs) ms in
      Syntax1.mkApps m ms
    | _ -> failwith "trans(%a)" pp_tm m)
  | Let (p, m, n) -> (
    match p with
    | PVar id_opt ->
      let x = trans_id_opt id_opt in
      let m = trans_tm nspc cs m in
      let nspc =
        match id_opt with
        | Some id -> (id, V x) :: nspc
        | None -> nspc
      in
      let n = trans_tm nspc cs n in
      Let (m, Syntax1.bind_tm x n)
    | _ ->
      let m = trans_tm nspc cs m in
      let nspc, p = trans_p nspc cs p in
      let n = trans_tm nspc cs n in
      let cl = Syntax1.bindp_tm_opt [ p ] (Some n) in
      let meta = Syntax1.Meta (M.mk (), spine_of_nspc nspc) in
      Syntax1.Match ([ m ], meta, [ Syntax1.Cl cl ]))
  | Match (ms, cls) ->
    let ms = List.map (trans_tm nspc cs) ms in
    let cls = trans_cls nspc cs cls in
    let meta = Syntax1.Meta (M.mk (), spine_of_nspc nspc) in
    Syntax1.Match (ms, meta, cls)
  | If (m, n1, n2) ->
    let m = trans_tm nspc cs m in
    let n1 = trans_tm nspc cs n1 in
    let n2 = trans_tm nspc cs n2 in
    Syntax1.If (m, n1, n2)
  | Main -> Syntax1.Main
  | Proto -> Syntax1.Proto
  | End -> Syntax1.End
  | Act (r, args, b) ->
    let nspc, args =
      List.fold_left
        (fun (nspc, acc) (id_opt, a) ->
          let a = trans_tm nspc cs a in
          let x = trans_id_opt id_opt in
          match id_opt with
          | Some id -> ((id, V x) :: nspc, (x, a) :: acc)
          | None -> (nspc, (x, a) :: acc))
        (nspc, []) args
    in
    List.fold_right
      (fun (x, a) acc ->
        let b = Syntax1.bind_tm x acc in
        Syntax1.Act (r, a, b))
      (List.rev args) (trans_tm nspc cs b)
  | Ch (r, a) -> Syntax1.Ch (r, trans_tm nspc cs a)
  | Fork (id, a, m, n) ->
    let x = V.mk id in
    let a = trans_tm nspc cs a in
    let m = trans_tm nspc cs m in
    let n = trans_tm ((id, V x) :: nspc) cs n in
    Syntax1.Fork (a, m, Syntax1.bind_tm x n)
  | Send a -> Syntax1.Send (trans_tm nspc cs a)
  | Recv a -> Syntax1.Recv (trans_tm nspc cs a)
  | Close a -> Syntax1.Close (trans_tm nspc cs a)

and trans_cl nspc cs (Cl (ps, m_opt)) =
  let nspc, ps = trans_ps nspc cs ps in
  let m_opt = Option.map (trans_tm nspc cs) m_opt in
  Syntax1.Cl (Syntax1.bindp_tm_opt ps m_opt)

and trans_cls nspc cs cls = List.map (trans_cl nspc cs) cls

let trans_trg s =
  match s with
  | "@stdin" -> Syntax1.TStdin
  | "@stdout" -> Syntax1.TStdout
  | "@stderr" -> Syntax1.TStdout
  | _ -> failwith "trans_trg(%s)" s

let rec trans_ptl nspc cs (PTl (args, tl)) =
  let nspc, args =
    List.fold_left
      (fun (nspc, acc) (id_opt, a) ->
        let a = trans_tm nspc cs a in
        let x = trans_id_opt id_opt in
        match id_opt with
        | Some id -> ((id, V x) :: nspc, (x, a) :: acc)
        | None -> (nspc, (x, a) :: acc))
      (nspc, []) args
  in
  let tl = Syntax1.PBase (trans_tl nspc cs tl) in
  List.fold_right
    (fun (x, a) acc -> Syntax1.PBind (a, Syntax1.bind_ptl x acc))
    (List.rev args) tl

and trans_tl nspc cs (Tl (args, b)) =
  let nspc, args =
    List.fold_left
      (fun (nspc, acc) (id_opt, a) ->
        let a = trans_tm nspc cs a in
        let x = trans_id_opt id_opt in
        match id_opt with
        | Some id -> ((id, V x) :: nspc, (x, a) :: acc)
        | None -> (nspc, (x, a) :: acc))
      (nspc, []) args
  in
  let b = Syntax1.TBase (trans_tm nspc cs b) in
  List.fold_right
    (fun (x, a) acc -> Syntax1.TBind (a, Syntax1.bind_tl x acc))
    (List.rev args) b

let trans_dcons nspc cs (DCons (id, ptl)) =
  let c = C.mk id in
  let ptl = trans_ptl nspc cs ptl in
  let nspc = (id, C c) :: nspc in
  let cs = SMap.add id c cs in
  (nspc, cs, Syntax1.DCons (c, ptl))

let rec trans_dconss npsc cs dconss =
  match dconss with
  | [] -> (npsc, cs, [])
  | dcons :: dconss ->
    let nspc, cs, dcons = trans_dcons npsc cs dcons in
    let nspc, cs, dconss = trans_dconss nspc cs dconss in
    (nspc, cs, dcons :: dconss)

let trans_dcl nspc cs dcl =
  match dcl with
  | DTm (id_opt, a_opt, m) ->
    let x = trans_id_opt id_opt in
    let a_opt = Option.map (trans_tm nspc cs) a_opt in
    let m = trans_tm nspc cs m in
    let nspc =
      match id_opt with
      | Some id -> (id, V x) :: nspc
      | None -> nspc
    in
    (nspc, cs, Syntax1.DTm (x, a_opt, m))
  | DFun (id, a, cls) ->
    let x = V.mk id in
    let a = trans_tm nspc cs a in
    let nspc = (id, V x) :: nspc in
    let cls = trans_cls nspc cs cls in
    (nspc, cs, Syntax1.DFun (x, a, Syntax1.bind_cls x cls))
  | DData (id, ptl, dconss) ->
    let d = D.mk id in
    let ptl = trans_ptl nspc cs ptl in
    let nspc = (id, D d) :: nspc in
    let nspc, cs, dconss = trans_dconss nspc cs dconss in
    (nspc, cs, Syntax1.DData (d, ptl, dconss))
  | DOpen (id1, id2) ->
    let targ = trans_trg id1 in
    let x = V.mk id2 in
    let nspc = (id2, V x) :: nspc in
    (nspc, cs, Syntax1.DOpen (targ, x))
  | DAxiom (id, a) ->
    let x = V.mk id in
    let a = trans_tm nspc cs a in
    let nspc = (id, V x) :: nspc in
    (nspc, cs, Syntax1.DAxiom (x, a))

let rec trans_dcls nspc cs dcls =
  match dcls with
  | [] -> (nspc, cs, [])
  | dcl :: dcls ->
    let nspc, cs, dcl = trans_dcl nspc cs dcl in
    let nspc, cs, dcls = trans_dcls nspc cs dcls in
    (nspc, cs, dcl :: dcls)