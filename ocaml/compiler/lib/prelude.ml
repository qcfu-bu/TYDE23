open Fmt
open MParser
open Names
open Syntax0
open Trans01

module Parser = struct
  let reserved =
    SSet.of_list
      [ "U"
      ; "L"
      ; "def"
      ; "data"
      ; "open"
      ; "forall"
      ; "fun"
      ; "let"
      ; "in"
      ; "rec"
      ; "match"
      ; "with"
      ; "absurd"
      ; "end"
      ; "axiom"
      ; "as"
      ; "if"
      ; "then"
      ; "else"
      ; "proto"
      ; "fork"
      ; "and"
      ; "send"
      ; "recv"
      ; "close"
      ]

  type 'a parser = ('a, int SMap.t) MParser.t

  let ( let* ) = bind
  let choice ls = choice (List.map attempt ls)
  let option p = option (attempt p)
  let trivial : unit parser = any_char_or_nl >>$ ()

  let rec nested_comment () : unit parser =
    let* _ = string "/-" in
    let* _ =
      many
        (let* opt =
           look_ahead (string "-/")
           >> return true
           <|> (nested_comment () <|> trivial >> return false)
         in
         if opt then
           zero
         else
           return ())
    in
    let* _ = string "-/" in
    return ()

  let rec line_comment () : unit parser =
    let terminal = newline >>$ () <|> eof in
    let* _ = string "--" in
    let* _ =
      many
        (let* opt =
           look_ahead terminal >> return true <|> (trivial >> return false)
         in
         if opt then
           zero
         else
           return ())
    in
    let* _ = terminal in
    return ()

  let ws : unit parser =
    many
      (choice
         [ blank >>$ (); newline >>$ (); nested_comment (); line_comment () ])
    >>$ ()

  let kw s : unit parser = string s >> ws
  let parens p = kw "(" >> p << kw ")"
  let angles p = kw "<" >> p << kw ">"
  let braces p = kw "{" >> p << kw "}"
  let bracks p = kw "[" >> p << kw "]"

  let id_parser : id parser =
    let* s1 = many1_chars (letter <|> char '_') in
    let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
    let* b = look_ahead (kw "‹") >>$ true <|> return false in
    if b then
      zero
    else
      let* _ = ws in
      let s = s1 ^ s2 in
      match SSet.find_opt s reserved with
      | Some _ -> fail (str "not a valid identifier(%s)" s)
      | None -> return s

  let id_opt_parser : id_opt parser =
    let* s1 = many1_chars (letter <|> char '_') in
    let* s2 = many_chars (alphanum <|> char '_' <|> char '\'') in
    let* b = look_ahead (kw "‹") >>$ true <|> return false in
    if b then
      zero
    else
      let* _ = ws in
      let s = s1 ^ s2 in
      match SSet.find_opt s reserved with
      | Some _ -> fail (str "not a valid identifier(%s)" s)
      | None ->
        if s = "_" then
          return None
        else
          return (Some s)

  let rec pvar_parser () =
    let* id_opt = id_opt_parser in
    return (PVar id_opt, false)

  and pcons_parser () =
    let* cs = get_user_state in
    let* id = id_parser in
    match SMap.find_opt id cs with
    | Some 0 -> return (PCons (id, []), false)
    | Some _ ->
      let* ps, absurd = ps_parser () in
      return (PCons (id, ps), absurd)
    | _ -> zero

  and pabsurd_parser () = kw "absurd" >>$ (PAbsurd, true)

  and p_parser () =
    let* _ = return () in
    choice
      [ pcons_parser ()
      ; pabsurd_parser ()
      ; pvar_parser ()
      ; parens (p_parser ())
      ]

  and ps_parser () =
    let* ps = many (p_parser ()) in
    let res =
      List.fold_right
        (fun (p, absurd) (ps, acc) -> (p :: ps, acc || absurd))
        ps ([], false)
    in
    return res

  and ps1_parser () =
    let* ps = many1 (p_parser ()) in
    let res =
      List.fold_right
        (fun (p, absurd) (ps, acc) -> (p :: ps, acc || absurd))
        ps ([], false)
    in
    return res

  and ps_sep_parser sep =
    let* ps = sep_by (p_parser ()) sep in
    let res =
      List.fold_right
        (fun (p, absurd) (ps, acc) -> (p :: ps, acc || absurd))
        ps ([], false)
    in
    return res

  and ps_sep1_parser sep =
    let* ps = sep_by1 (p_parser ()) sep in
    let res =
      List.fold_right
        (fun (p, absurd) (ps, acc) -> (p :: ps, acc || absurd))
        ps ([], false)
    in
    return res

  let rec type_parser () = kw "U" >>$ Type U <|> (kw "L" >>$ Type L)

  and ann_parser () =
    let* a = kw "@[" >> tm_parser () << kw "]" in
    let* m = tm_parser () in
    return (Ann (a, m))

  and arg_parser () =
    parens
      (let* ids = many1 id_parser in
       let* _ = kw ":" in
       let* a = tm_parser () in
       let arg = List.map (fun id -> (Some id, a)) ids in
       return arg)

  and args_parser () =
    let* args = many (arg_parser ()) in
    let args = List.concat args in
    return args

  and args1_parser () =
    let* args = many1 (arg_parser ()) in
    let args = List.concat args in
    return args

  and pi_parser () =
    let* _ = kw "∀" <|> kw "forall" in
    let* args = args1_parser () in
    let* srt = kw "→" <|> kw "->" >>$ U <|> (kw "⊸" <|> kw "-o" >>$ L) in
    let* b = tm_parser () in
    return (Pi (srt, args, b))

  and cl_parser () =
    let* _ = kw "|" in
    let* ps, absurd = ps_parser () in
    if absurd then
      return (Cl (ps, None))
    else
      let* _ = kw "=>" in
      let* rhs = tm_parser () in
      return (Cl (ps, Some rhs))

  and cls_parser () = many1 (cl_parser ())

  and fun0_parser () =
    let* id = id_parser in
    let* a_opt = option (kw ":" >> tm_parser ()) in
    let* cls = cls_parser () in
    return (Fun (Some id, a_opt, cls))

  and fun1_parser () =
    let* _ = kw ":" in
    let* a = tm_parser () in
    let* cls = cls_parser () in
    return (Fun (None, Some a, cls))

  and fun2_parser () =
    let* cls = cls_parser () in
    return (Fun (None, None, cls))

  and fun3_parser () =
    let* ps, absurd = ps1_parser () in
    if absurd then
      fail "absurd pattern not allowed here"
    else
      let* _ = kw "=>" in
      let* rhs = tm_parser () in
      return (Fun (None, None, [ Cl (ps, Some rhs) ]))

  and fun_parser () =
    let* _ = kw "λ" <|> kw "fun" in
    choice [ fun0_parser (); fun1_parser (); fun2_parser (); fun3_parser () ]

  and let0_parser () =
    let* _ = kw "rec" in
    let* id_opt = id_opt_parser in
    match id_opt with
    | None -> fail "recursive functions must be named"
    | Some id ->
      let* _ = kw ":" in
      let* a = tm_parser () in
      let* cls = cls_parser () in
      let* _ = kw "in" in
      let* n = tm_parser () in
      return (Let (PVar (Some id), Fun (Some id, Some a, cls), n))

  and let1_parser () =
    let* id_opt = id_opt_parser in
    let* _ = kw ":" in
    let* a = tm_parser () in
    let* cls = cls_parser () in
    let* _ = kw "in" in
    let* n = tm_parser () in
    return (Let (PVar id_opt, Fun (None, Some a, cls), n))

  and let2_parser () =
    let* p, absurd = p_parser () in
    if absurd then
      fail "absurd pattern not allowed here"
    else
      let* opt = option (kw ":" >> tm_parser ()) in
      let* _ = kw ":=" in
      let* m = tm_parser () in
      let m =
        match opt with
        | Some a -> Ann (m, a)
        | None -> m
      in
      let* _ = kw "in" in
      let* n = tm_parser () in
      return (Let (p, m, n))

  and let_parser () =
    let* _ = kw "let" in
    choice [ let0_parser (); let1_parser (); let2_parser () ]

  and branch_parser () =
    let* _ = kw "|" in
    let* ps, absurd = ps_sep1_parser (kw ",") in
    if absurd then
      return (Cl (ps, None))
    else
      let* _ = kw "=>" in
      let* rhs = tm_parser () in
      return (Cl (ps, Some rhs))

  and branches_parser () = many1 (branch_parser ())

  and match_parser () =
    let* _ = kw "match" in
    let* ms = sep_by1 (tm_parser ()) (kw ",") in
    let* _ = kw "with" in
    let* cls = branches_parser () in
    return (Match (ms, cls))

  and if_parser () =
    let* _ = kw "if" in
    let* m = tm_parser () in
    let* _ = kw "then" in
    let* tt = tm_parser () in
    let* _ = kw "else" in
    let* ff = tm_parser () in
    return (If (m, tt, ff))

  and main_parser () = kw "@main" >>$ Main
  and proto_parser () = kw "proto" >>$ Proto
  and end_parser () = kw "end" >>$ End

  and act0_parser () =
    let* args = args1_parser () in
    return args

  and act1_parser () =
    let* a = tm_parser () in
    return [ (None, a) ]

  and act_parser () =
    let* r = kw "?" >>$ true <|> (kw "!" >>$ false) in
    let* args = act0_parser () <|> act1_parser () in
    let* _ = kw "⋅" in
    let* b = tm_parser () in
    return (Act (r, args, b))

  and ch_parser () =
    let* r = kw "ch‹" >>$ true <|> (kw "hc‹" >>$ false) in
    let* m = tm_parser () in
    let* _ = kw "›" in
    return (Ch (r, m))

  and fork_parser () =
    let* _ = kw "fork" in
    let* _ = kw "(" in
    let* id = id_parser in
    let* _ = kw ":" in
    let* a = tm_parser () in
    let* _ = kw ")" in
    let* _ = kw "<-" in
    let* m = tm_parser () in
    let* _ = kw "with" in
    let* n = tm_parser () in
    return (Fork (id, a, m, n))

  and send_parser () =
    let* _ = kw "send" in
    let* m = tm0_parser () in
    return (Send m)

  and recv_parser () =
    let* _ = kw "recv" in
    let* m = tm0_parser () in
    return (Recv m)

  and close_parser () =
    let* _ = kw "close" in
    let* m = tm0_parser () in
    return (Close m)

  and tm0_parser () =
    let* _ = return () in
    choice
      [ (id_parser >>= fun id -> return (Id id))
      ; type_parser ()
      ; ann_parser ()
      ; pi_parser ()
      ; fun_parser ()
      ; let_parser ()
      ; match_parser ()
      ; if_parser ()
      ; main_parser ()
      ; proto_parser ()
      ; end_parser ()
      ; act_parser ()
      ; ch_parser ()
      ; fork_parser ()
      ; send_parser ()
      ; recv_parser ()
      ; close_parser ()
      ; parens (tm_parser ())
      ]

  and tm1_parser () =
    let* hd = tm0_parser () in
    let* tl = many (tm0_parser ()) in
    match tl with
    | [] -> return hd
    | _ -> return (App (hd :: tl))

  and tm2_parser () =
    let arrow_parser =
      let* _ = kw "→" <|> kw "->" in
      return (fun a b -> Pi (U, [ (None, a) ], b))
    in
    let lolli_parser =
      let* _ = kw "⊸" <|> kw "-o" in
      return (fun a b -> Pi (L, [ (None, a) ], b))
    in
    chain_right1 (tm1_parser ()) (arrow_parser <|> lolli_parser)

  and tm_parser () = tm2_parser ()

  let def_parser =
    let* _ = kw "def" in
    let* id_opt = id_opt_parser in
    let* a_opt = option (kw ":" >> tm_parser ()) in
    (let* cls = cls_parser () in
     match (id_opt, a_opt) with
     | Some id, Some a -> return (DFun (id, a, cls))
     | None, _ -> fail "toplevel functions must be named"
     | _, None -> fail "type annotation required for toplevel functions")
    <|> let* _ = kw ":=" in
        let* m = tm_parser () in
        return (DTm (id_opt, a_opt, m))

  let rec make_tl a =
    match a with
    | Pi (U, args1, a) ->
      let Tl (args2, a), sz = make_tl a in
      (Tl (args1 @ args2, a), sz + List.length args1)
    | _ -> (Tl ([], a), 0)

  let cons_parser args =
    let* _ = kw "|" in
    let* id = id_parser in
    let* _ = kw ":" in
    let* b = tm_parser () in
    let b, sz = make_tl b in
    let* _ = update_user_state (fun cs -> SMap.add id sz cs) in
    return (DCons (id, PTl (args, b)))

  let conss_parser args = many (cons_parser args)

  let ddata_parser =
    let* _ = kw "data" in
    let* id = id_parser in
    let* args = args_parser () in
    let* _ = kw ":" in
    let* b = tm_parser () in
    let b, _ = make_tl b in
    let* conss = conss_parser args in
    return (DData (id, PTl (args, b), conss))

  let directive_parser =
    choice
      [ kw "@stdin" >>$ "@stdin"
      ; kw "@stdout" >>$ "@stdout"
      ; kw "@stderr" >>$ "@stderr"
      ; kw "@main" >>$ "@main"
      ]

  let dopen_parser =
    let* _ = kw "open" in
    let* id1 = directive_parser in
    let* _ = kw "as" in
    let* id2 = id_parser in
    return (DOpen (id1, id2))

  let daxiom_parser =
    let* _ = kw "axiom" in
    let* id = id_parser in
    let* _ = kw ":" in
    let* a = tm_parser () in
    return (DAxiom (id, a))

  let dcl_parser =
    choice [ def_parser; ddata_parser; dopen_parser; daxiom_parser ]

  let dcls_parser =
    let* src = many1 dcl_parser in
    let* state = get_user_state in
    return (src, state)

  let parse_string s state = parse_string (ws >> dcls_parser << eof) s state
  let parse_channel ch state = parse_channel (ws >> dcls_parser << eof) ch state
end

let src0, state0 =
  let ch = open_in "./lib/prelude.clc" in
  match Parser.parse_channel ch SMap.empty with
  | Success res -> res
  | Failed (s, _) -> failwith "prelude"

let main_v = V.mk "main"
let nspc, cs, src1 = trans_dcls [ ("main", V main_v) ] SMap.empty src0

let find_v s =
  match List.assoc s nspc with
  | V x -> x
  | _ -> failwith "find_v(%s)" s

let find_d s =
  match List.assoc s nspc with
  | D d -> d
  | _ -> failwith "find_d(%s)" s

let find_c s =
  match List.assoc s nspc with
  | C c -> c
  | _ -> failwith "find_c(%s)" s

let unit_d = find_d "unit"
let tt_c = find_c "tt"
let bool_d = find_d "bool"
let true_c = find_c "true"
let false_c = find_c "false"
let ex_d = find_d "ex"
let ex_intro_c = find_c "ex_intro"
let sig_d = find_d "sig"
let sig_intro_c = find_c "sig_intro"
let tnsr_d = find_d "tnsr"
let tnsr_intro_c = find_c "tnsr_intro"
let box_d = find_d "box"
let box_intro_c = find_c "box_intro"
let nat_d = find_d "nat"
let zero_c = find_c "zero"
let succ_c = find_c "succ"
let ascii_d = find_d "ascii"
let ascii0_c = find_c "Ascii"
let string_d = find_d "string"
let emptyString_c = find_c "EmptyString"
let string0_c = find_c "String"
let stdin_t = find_v "stdin_t"
let stdout_t = find_v "stdout_t"
let stderr_t = find_v "stderr_t"

let gen_prelude ch =
  let _ = Printf.fprintf ch "#ifndef prelude_h\n\n" in
  let _ =
    SMap.iter
      (fun s c -> Printf.fprintf ch "#define %s_c %d\n" s (C.get_id c))
      cs
  in
  let _ = Printf.fprintf ch "\n#endif" in
  close_out ch
