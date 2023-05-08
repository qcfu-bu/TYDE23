open Fmt
open Lang
open Names
open Parser0
open Prelude
open Equality1

let run s1 s2 s3 s4 =
  let ch1 = open_in s1 in
  let ch2 = open_out s2 in
  let ch3 = open_out s3 in
  let ch4 = open_out s4 in
  try
    match parse_channel ch1 state0 with
    | Success (dcls, _) ->
      let s = str "%a@." Syntax0.pp_dcls dcls in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ =
        Printf.fprintf ch2
          "parse success---------------------------------------\n\n"
      in
      let _, _, dcls = Trans01.trans_dcls nspc cs dcls in
      let dcls = src1 @ dcls in
      let s = str "%a@." Pprint1.pp_dcls dcls in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ =
        Printf.fprintf ch2
          "trans01 success-------------------------------------\n\n"
      in
      let dcls = Trans1e.trans_dcls dcls in
      let s = str "%a@." Pprint1.pp_dcls dcls in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ =
        Printf.fprintf ch2
          "trans1e success-------------------------------------\n\n"
      in
      let dcls = Trans12.trans_dcls dcls in
      let s = str "%a@." Pprint2.pp_dcls dcls in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ =
        Printf.fprintf ch2
          "trans12 success-------------------------------------\n\n"
      in
      let res = Eval2.eval_dcls dcls in
      let s = str "%a@." Eval2.pp_res res in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ =
        Printf.fprintf ch2
          "eval2 success---------------------------------------\n\n"
      in
      let prog = Trans23.trans_dcls dcls in
      let s = str "%a@." Pprint3.pp_prog prog in
      let _ = Printf.fprintf ch2 "%s" s in
      let _ = Prelude.gen_prelude ch3 in
      let _ = Printf.fprintf ch4 "%s" s in
      let _ =
        Printf.fprintf ch2
          "trans23 success-------------------------------------\n\n"
      in
      ()
    | Failed (s, _) -> epr "%s\n" s
  with
  | Failure s -> epr "Failure: %s" s

let _ =
  if Array.length Sys.argv < 1 then
    epr "input file expected@."
  else
    run Sys.argv.(1) "log.clc" "c/prelude.h" "c/main.c"
