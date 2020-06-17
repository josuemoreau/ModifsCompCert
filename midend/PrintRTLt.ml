(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTLt

(* Printing of RTL code *)

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let print_instruction = PrintRTL.print_instruction

let print_function pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Stdlib.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction pp) instrs;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: RTLt.program) =
  List.iter (print_globdef pp) prog.prog_defs


let destination : string option ref = ref None
let destination_drtlnorm : string option ref = ref None

let print_if dest prog =
  match !dest with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program oc prog;
      close_out oc
