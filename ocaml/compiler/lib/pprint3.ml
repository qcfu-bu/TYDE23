open Fmt
open Names
open Syntax3

let rec pp_value fmt v =
  match v with
  | Zero -> pf fmt "0"
  | Reg x -> V.pp fmt x
  | Env i -> pf fmt "env[%d]" i
  | Proj (v, i) -> pf fmt "((clc_node)%a)->data[%d]" pp_value v i

let pp_values fmt vs =
  let rec aux fmt vs =
    match vs with
    | [] -> ()
    | [ v ] -> pp_value fmt v
    | v :: vs -> pf fmt "%a,@ %a" pp_value v aux vs
  in
  match vs with
  | [] -> ()
  | _ -> pf fmt ",@;<1 2>@[%a@]" aux vs

let rec gather_var ctx instrs =
  match instrs with
  | [] -> ctx
  | Mov (x, v) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Clo (x, _, _, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Call (x, _, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Struct (x, _, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Switch (_, cls) :: instrs ->
    let ctx =
      List.fold_left (fun ctx (_, instrs) -> gather_var ctx instrs) ctx cls
    in
    gather_var ctx instrs
  | Break :: instrs -> gather_var ctx instrs
  | Open (x, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Send (x, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Recv (x, _, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | Close (x, _) :: instrs -> gather_var (VSet.add x ctx) instrs
  | FreeClo _ :: instrs -> gather_var ctx instrs
  | FreeStruct _ :: instrs -> gather_var ctx instrs
  | FreeThread :: instrs -> gather_var ctx instrs

let pp_xs fmt ctx =
  let xs = VSet.elements ctx in
  let rec aux fmt = function
    | [] -> ()
    | [ x ] -> pf fmt "clc_ptr %a;" V.pp x
    | x :: xs -> pf fmt "clc_ptr %a;@;<1 0>%a" V.pp x aux xs
  in
  aux fmt xs

let rec pp_proc fmt proc =
  let xs = gather_var VSet.empty proc.body in
  let pp_arg fmt opt =
    match opt with
    | None -> ()
    | Some x -> pf fmt "clc_ptr %a, " V.pp x
  in
  pf fmt
    "@[<v 0>clc_ptr %a(%aclc_env env)@;\
     <1 0>{@;\
     <1 2>@[<v 0>@[%a@]@;\
     <1 0>%a@;\
     <1 0>return %a@];@;\
     <1 0>}@]" V.pp proc.name pp_arg proc.arg pp_xs xs pp_instrs proc.body
    pp_value proc.return

and pp_def fmt def =
  match def with
  | [] -> ()
  | [ proc ] -> pp_proc fmt proc
  | proc :: def -> pf fmt "@[<v 0>%a@]@.@.%a" pp_proc proc pp_def def

and pp_instr fmt instr =
  match instr with
  | Mov (x, v) -> pf fmt "instr_mov(&%a, %a);" V.pp x pp_value v
  | Clo (x, f, sz, vs) ->
    pf fmt "@[instr_clo(&%a, &%a, %d, env, %d%a);@]" V.pp x V.pp f sz
      (List.length vs) pp_values vs
  | Call (x, v1, v2) ->
    pf fmt "instr_call(&%a, %a, %a);" V.pp x pp_value v1 pp_value v2
  | Struct (x, tag, []) -> pf fmt "instr_struct(&%a, %d, %d);" V.pp x tag 0
  | Struct (x, tag, vs) ->
    pf fmt "instr_struct(&%a, %d, %d%a);" V.pp x tag (List.length vs) pp_values
      vs
  | Switch (m, cls) ->
    pf fmt "@[<v 0>switch(((clc_node)%a)->tag){@;<1 2>@[%a@]}@]" pp_value m
      pp_cls cls
  | Break -> pf fmt "break;"
  | Open (x, trg) -> (
    match trg with
    | TCh (f, m, sz, vs) ->
      pf fmt "instr_open(&%a, &%a, %a, %d, env, %d%a);" V.pp x V.pp f pp_value m
        sz (List.length vs) pp_values vs
    | TStdout -> pf fmt "instr_trg(&%a, &proc_stdout);" V.pp x
    | TStdin -> pf fmt "instr_trg(&%a, &proc_stdin);" V.pp x
    | TStderr -> pf fmt "instr_trg(&%a, &proc_stderr);" V.pp x)
  | Send (x, v) -> pf fmt "instr_send(&%a, %a);" V.pp x pp_value v
  | Recv (x, v, tag) -> pf fmt "instr_recv(&%a, %a, %d);" V.pp x pp_value v tag
  | Close (x, v) -> pf fmt "instr_close(&%a, %a);" V.pp x pp_value v
  | FreeClo v -> pf fmt "instr_free_clo(%a);" pp_value v
  | FreeStruct v -> pf fmt "instr_free_struct(%a);" pp_value v
  | FreeThread -> pf fmt "instr_free_thread(env);"

and pp_instrs fmt instrs =
  let rec aux fmt instrs =
    match instrs with
    | [] -> ()
    | [ instr ] -> pp_instr fmt instr
    | instr :: instrs -> pf fmt "%a@;<1 0>%a" pp_instr instr pp_instrs instrs
  in
  pf fmt "@[<v 0>%a@]" aux instrs

and pp_cl fmt (i, instr) = pf fmt "@[case %d:@;<1 2>%a@]" i pp_instrs instr

and pp_cls fmt cls =
  match cls with
  | [] -> ()
  | [ cl ] -> pp_cl fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl cl pp_cls cls

let pp_prog fmt (def, instr, v) =
  let xs = gather_var VSet.empty instr in
  pf fmt
    "#include \"runtime.h\"@.@.%a@.@.@[<v 0>int main()@;\
     <1 0>{@;\
     <1 2>@[<v 0>@[%a@]@;\
     <1 0>clc_env env = 0;@;\
     <1 0>instr_init();@;\
     <1 0>%a@;\
     <1 0>return %a;@]@;\
     <1 0>}@]" pp_def def pp_xs xs pp_instrs instr pp_value v
