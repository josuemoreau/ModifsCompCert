
(** Pretty-printers for SSA code *)

open Printf
open Camlcoq
open Datatypes

open Maps
open AST

open SSA

open PrintAST

let source : Syntax.program option ref = ref None

let set_source b = source := Some b

let reg pp r =
    fprintf pp "%%v%d" (P.to_int r)

let typ pp = function
  | Tint    -> fprintf pp "i32"
  | Tfloat  -> fprintf pp "double"
  | Tlong   -> fprintf pp "i64"
  | Tsingle -> fprintf pp "float"
  | Tany32  -> fprintf pp "ptr"
  | Tany64  -> fprintf pp "ptr"

let ret_typ pp = function
  | Tret t -> typ pp t
  | Tint8signed    -> fprintf pp "signext i8"
  | Tint8unsigned  -> fprintf pp "zeroext i8"
  | Tint16signed   -> fprintf pp "signext i16"
  | Tint16unsigned -> fprintf pp "zeroext i16"
  | Tvoid -> fprintf pp "void"

let b_typ pp =
  function
  | Types.Tvoid -> fprintf pp "void"
  | Types.Tbool -> fprintf pp "i32"
  | Types.Tint (_, _) -> fprintf pp "i32"
  | Types.Tint64 _ -> fprintf pp "i64"
  | Types.Tfloat Types.F32 -> fprintf pp "float"
  | Types.Tfloat Types.F64 -> fprintf pp "double"
  | Types.Tarr _ -> fprintf pp "ptr"

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let rec typed_regs pp = function
  | [], [] -> ()
  | [r], [t] -> fprintf pp "%a %a" typ t reg r
  | r::rl, t::tl -> fprintf pp "%a %a, %a" typ t reg r typed_regs (rl, tl)
  | _ -> assert false

let rec b_typed_regs pp = function
  | [], [] -> ()
  | [r], [t] -> fprintf pp "%a %a" b_typ t reg r
  | r::rl, t::tl -> fprintf pp "%a %a, %a" b_typ t reg r b_typed_regs (rl, tl)
  | _ -> assert false

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let rec print_phi_args_aux reg pp = function
  | [] -> ()
  | x::q -> fprintf pp ", [%a, ]%a" reg x (print_phi_args_aux reg) q

let print_phi_args reg pp = function
  | [] -> ()
  | x::q -> fprintf pp "[%a, ]%a" reg x (print_phi_args_aux reg) q

let print_phi reg phi (pc : P.t) pp =
  match PTree.get pc phi with
  | None -> ()
  | Some phi_asgnts ->
      List.iter (fun (SSA.Iphi (args,res)) ->
	  fprintf pp "\t%a = phi %a\n"
            reg res (print_phi_args reg) args)
	phi_asgnts

let cmp_name signed =
  let open Integers in
  function
  | Ceq -> "eq"
  | Cne -> "ne"
  | Clt -> if signed then "slt" else "ult"
  | Cle -> if signed then "sle" else "ule"
  | Cgt -> if signed then "sgt" else "ugt"
  | Cge -> if signed then "sge" else "uge"

let fcmp_name negated =
  let open Integers in
  function
  | Ceq -> if negated then "une" else "oeq"
  | Cne -> if negated then "oeq" else "une"
  | Clt -> if negated then "uge" else "olt"
  | Cle -> if negated then "ult" else "ole"
  | Cgt -> if negated then "ule" else "ogt"
  | Cge -> if negated then "ult" else "oge"

let print_condition pp =
  let open Op in
  function
  | Ccomp c, [r1;r2] ->
      fprintf pp "icmp %s i32 %a, %a" (cmp_name true c) reg r1 reg r2
  | Ccompu c, [r1;r2] ->
      fprintf pp "icmp %s i32 %a, %a" (cmp_name false c) reg r1 reg r2
  | Ccompimm(c, n), [r1] ->
      fprintf pp "icmp %s i32 %a, %ld" (cmp_name true c) reg r1 (camlint_of_coqint n)
  | Ccompuimm(c, n), [r1] ->
      fprintf pp "icmp %s i32 %a, %lu" (cmp_name false c) reg r1 (camlint_of_coqint n)
  | Ccompl c, [r1;r2] ->
      fprintf pp "icmp %s i64 %a, %a" (cmp_name true c) reg r1 reg r2
  | Ccomplu c, [r1;r2] ->
      fprintf pp "icmp %s i64 %a, %a" (cmp_name false c) reg r1 reg r2
  | Ccomplimm(c, n), [r1] ->
      fprintf pp "icmp %s i64 %a, %Ld" (cmp_name true c) reg r1 (camlint64_of_coqint n)
  | Ccompluimm(c, n), [r1] ->
      fprintf pp "icmp %s i64 %a, %Lu" (cmp_name false c) reg r1 (camlint64_of_coqint n)
  | Ccompf c, [r1;r2] ->
      fprintf pp "fcmp %s double %a, %a" (fcmp_name false c) reg r1 reg r2
  | Cnotcompf c, [r1;r2] ->
      fprintf pp "fcmp %s double %a, %a" (fcmp_name true c) reg r1 reg r2
  | Ccompfs c, [r1;r2] ->
      fprintf pp "fcmp %s float %a, %a" (fcmp_name false c) reg r1 reg r2
  | Cnotcompfs c, [r1;r2] ->
      fprintf pp "fcmp %s float %a, %a" (fcmp_name true c) reg r1 reg r2
  | (Cmaskzero n, [r1]) ->
      fprintf pp "%a & 0x%lx == 0" reg r1 (camlint_of_coqint n)
  | (Cmasknotzero n, [r1]) ->
      fprintf pp "%a & 0x%lx != 0" reg r1 (camlint_of_coqint n)
  | _ ->
      fprintf pp "<bad condition>"

let print_addressing reg pp =
  let open Op in
  function
  | Aindexed n, [r1] ->
      fprintf pp "%a + %s" reg r1 (Z.to_string n)
  | Aindexed2 n, [r1; r2] ->
      fprintf pp "%a + %a + %s" reg r1 reg r2 (Z.to_string n)
  | Ascaled(sc,n), [r1] ->
      fprintf pp "%a * %s + %s" reg r1 (Z.to_string sc) (Z.to_string n)
  | Aindexed2scaled(sc, n), [r1; r2] ->
      fprintf pp "%a + %a * %s + %s" reg r1 reg r2 (Z.to_string sc) (Z.to_string n)
  | Aglobal(id, ofs), [] -> fprintf pp "%s + %s" (extern_atom id) (Z.to_string ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %s + %a" (extern_atom id) (Z.to_string ofs) reg r1
  | Abasedscaled(sc,id, ofs), [r1] -> fprintf pp "%s + %s + %a * %ld" (extern_atom id) (Z.to_string ofs) reg r1 (camlint_of_coqint sc)
  | Ainstack ofs, [] -> fprintf pp "stack(%s)" (Z.to_string ofs)
  | _ -> fprintf pp "<bad addressing>"

let print_operation reg pp =
  let open Op in
  function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Olongconst n, [] -> fprintf pp "%LdL" (camlint64_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%.15F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%.15Ff" (camlfloat_of_coqfloat32 n)
  | Oindirectsymbol id, [] -> fprintf pp "&%s" (extern_atom id)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast8unsigned, [r1] -> fprintf pp "int8unsigned(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Ocast16unsigned, [r1] -> fprintf pp "int16unsigned(%a)" reg r1
  | Oneg, [r1] -> fprintf pp "sub i32 0, %a" reg r1
  | Osub, [r1;r2] -> fprintf pp "sub i32 %a, %a" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "mul i32 %a, %a" reg r1 reg r2
  | Omulimm n, [r1] -> fprintf pp "mul i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Omulhs, [r1;r2] -> fprintf pp "mulhs(%a,%a)" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "mulhu(%a,%a)" reg r1 reg r2
  | Odiv, [r1;r2] -> fprintf pp "sdiv i32 %a, %a" reg r1 reg r2
  | Odivu, [r1;r2] -> fprintf pp "udiv i32 %a, %a" reg r1 reg r2
  | Omod, [r1;r2] -> fprintf pp "srem i32 %a, %a" reg r1 reg r2
  | Omodu, [r1;r2] -> fprintf pp "urem i32 %a, %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "and i32 %a, %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "and i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "or i32 %a, %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "or i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "xor i32 %a, %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "xor i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Onot, [r1] -> fprintf pp "xor i32 %a, -1" reg r1
  | Oshl, [r1;r2] -> fprintf pp "shl i32 %a, %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "shl i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "ashr i32 %a, %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "ashr i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "lshr i32 %a, %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "lshr i32 %a, %ld" reg r1 (camlint_of_coqint n)
  | Ororimm n, [r1] -> fprintf pp "%a ror %ld" reg r1 (camlint_of_coqint n)
  | Oshldimm n, [r1;r2] -> fprintf pp "(%a, %a) << %ld" reg r1 reg r2 (camlint_of_coqint n)
  | Olea addr, args -> print_addressing reg pp (addr, args)
  | Omakelong, [r1;r2] -> fprintf pp "makelong(%a,%a)" reg r1 reg r2
  | Olowlong, [r1] -> fprintf pp "lowlong(%a)" reg r1
  | Ohighlong, [r1] -> fprintf pp "highlong(%a)" reg r1
  | Ocast32signed, [r1] -> fprintf pp "long32signed(%a)" reg r1
  | Ocast32unsigned, [r1] -> fprintf pp "long32unsigned(%a)" reg r1
  | Onegl, [r1] -> fprintf pp "sub i64 0, %a" reg r1
  | Osubl, [r1;r2] -> fprintf pp "sub i64 %a, %a" reg r1 reg r2
  | Omull, [r1;r2] -> fprintf pp "mul i64 %a, %a" reg r1 reg r2
  | Omullimm n, [r1] -> fprintf pp "mul i64 %a, %Ld" reg r1 (camlint64_of_coqint n)
  | Omullhs, [r1;r2] -> fprintf pp "mullhs(%a,%a)" reg r1 reg r2
  | Omullhu, [r1;r2] -> fprintf pp "mullhu(%a,%a)" reg r1 reg r2
  | Odivl, [r1;r2] -> fprintf pp "sdiv i64 %a, %a" reg r1 reg r2
  | Odivlu, [r1;r2] -> fprintf pp "udiv i64 %a, %a" reg r1 reg r2
  | Omodl, [r1;r2] -> fprintf pp "srem i64 %a, %a" reg r1 reg r2
  | Omodlu, [r1;r2] -> fprintf pp "urem i64 %a, %a" reg r1 reg r2
  | Oandl, [r1;r2] -> fprintf pp "and i64 %a, %a" reg r1 reg r2
  | Oandlimm n, [r1] -> fprintf pp "and i64 %a, %Ld" reg r1 (camlint64_of_coqint n)
  | Oorl, [r1;r2] -> fprintf pp "or i64 %a, %a" reg r1 reg r2
  | Oorlimm n, [r1] ->  fprintf pp "or i64 %a, %Ld" reg r1 (camlint64_of_coqint n)
  | Oxorl, [r1;r2] -> fprintf pp "xor i64 %a, %a" reg r1 reg r2
  | Oxorlimm n, [r1] -> fprintf pp "xor i64 %a, %Ld" reg r1 (camlint64_of_coqint n)
  | Onotl, [r1] -> fprintf pp "xor i64 %a, -1" reg r1
  | Oshll, [r1;r2] -> fprintf pp "shl i64 %a, %a" reg r1 reg r2
  | Oshllimm n, [r1] -> fprintf pp "shl i64 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oshrl, [r1;r2] -> fprintf pp "ashr i64 %a, %a" reg r1 reg r2
  | Oshrlimm n, [r1] -> fprintf pp "ashr i64 %a, %ld" reg r1 (camlint_of_coqint n)
  | Oshrxlimm n, [r1] -> fprintf pp "%a >>lx %ld" reg r1 (camlint_of_coqint n)
  | Oshrlu, [r1;r2] -> fprintf pp "lshr i64 %a, %a" reg r1 reg r2
  | Oshrluimm n, [r1] -> fprintf pp "lshr i64 %a, %ld" reg r1 (camlint_of_coqint n)
  | Ororlimm n, [r1] -> fprintf pp "%a rorl %ld" reg r1 (camlint_of_coqint n)
  | Oleal addr, args -> print_addressing reg pp (addr, args)
  | Onegf, [r1] -> fprintf pp "fneg double %a" reg r1
  | Oabsf, [r1] -> fprintf pp "double call @llvm.fabs.f64(double %a)" reg r1
  | Oaddf, [r1;r2] -> fprintf pp "fadd double %a, %a" reg r1 reg r2
  | Osubf, [r1;r2] -> fprintf pp "fsub double %a, %a" reg r1 reg r2
  | Omulf, [r1;r2] -> fprintf pp "fmul double %a, %a" reg r1 reg r2
  | Odivf, [r1;r2] -> fprintf pp "fdiv double %a, %a" reg r1 reg r2
  | Omaxf, [r1;r2] -> fprintf pp "max(%a, %a)" reg r1 reg r2
  | Ominf, [r1;r2] -> fprintf pp "min(%a, %a)" reg r1 reg r2
  | Onegfs, [r1] -> fprintf pp "fneg float %a" reg r1
  | Oabsfs, [r1] -> fprintf pp "float call @llvm.fabs.f32(float %a)" reg r1
  | Oaddfs, [r1;r2] -> fprintf pp "fadd float %a, %a" reg r1 reg r2
  | Osubfs, [r1;r2] -> fprintf pp "fsub float %a, %a" reg r1 reg r2
  | Omulfs, [r1;r2] -> fprintf pp "fmul float %a, %a" reg r1 reg r2
  | Odivfs, [r1;r2] -> fprintf pp "fdiv float %a, %a" reg r1 reg r2
  | Osingleoffloat, [r1] -> fprintf pp "singleoffloat(%a)" reg r1
  | Ofloatofsingle, [r1] -> fprintf pp "floatofsingle(%a)" reg r1
  | Ointoffloat, [r1] -> fprintf pp "intoffloat(%a)" reg r1
  | Ofloatofint, [r1] -> fprintf pp "floatofint(%a)" reg r1
  | Ointofsingle, [r1] -> fprintf pp "intofsingle(%a)" reg r1
  | Osingleofint, [r1] -> fprintf pp "singleofint(%a)" reg r1
  | Olongoffloat, [r1] -> fprintf pp "longoffloat(%a)" reg r1
  | Ofloatoflong, [r1] -> fprintf pp "floatoflong(%a)" reg r1
  | Olongofsingle, [r1] -> fprintf pp "longofsingle(%a)" reg r1
  | Osingleoflong, [r1] -> fprintf pp "singleoflong(%a)" reg r1
  | Ocmp c, args -> print_condition pp (c, args)
  | Osel (c, ty), r1::r2::args ->
      fprintf pp "%a ?%s %a : %a"
         print_condition (c, args)
         (PrintAST.name_of_type ty) reg r1 reg r2
  | _ -> fprintf pp "<bad operator>"

let trivial_op =
  let open Op in
  function
  | Omove -> true
  | Ointconst _ -> true
  | Olongconst _ -> true
  | Ofloatconst _ -> true
  | Osingleconst _ -> true
  | _ -> false

let print_instruction reg phi pp starts skips (pc, pc_pos, i) =
  let print_succ s =
    let s = P.to_int s in
    if Hashtbl.mem starts s then
      let s =
        try Hashtbl.find skips s
        with Not_found -> s in
      fprintf pp "\tbr label %%l%d\n" s in
  if Hashtbl.mem starts pc then
    fprintf pp "l%d:\n" pc;
  print_phi reg phi pc_pos pp;
  match i with
  | Inop s ->
      print_succ s
  | Iop (o, _, _, s) when trivial_op o ->
      print_succ s
  | Iop (op, args, res, s) ->
      fprintf pp "\t%a = %a\n" reg res (print_operation reg) (op, args);
      print_succ s
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "\t%a = %s[%a]\n"
        reg dst (name_of_chunk chunk)
        (PrintOp.print_addressing reg) (addr, args);
      print_succ s
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "\t%s[%a] = %a\n"
        (name_of_chunk chunk)
        (PrintOp.print_addressing reg) (addr, args)
        reg src;
      print_succ s
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "\t%a = call @%a(%a)\n"
        reg res ros fn regs args;
      print_succ s
  | Itailcall(sg, fn, args) ->
      (*fprintf pp "\ttailcall %a(%a)\n"
        ros fn regs args*)
      assert false
  | Ibuiltin(ef, args, res, s) ->
      fprintf pp "\t%a = call @%s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args;
      print_succ s
  | Icond(cond, args, s1, s2) ->
      fprintf pp "\t%%t%d = %a\n"
        pc print_condition (cond, args);
      fprintf pp "\tbr i1 %%t%d, label %%l%d, label %%l%d\n"
        pc (P.to_int s1) (P.to_int s2)
  | Ijumptable(arg, tbl) ->
      (*let tbl = Array.of_list tbl in
      fprintf pp "\tjumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\t\tcase %d: goto l%d\n" i (P.to_int tbl.(i))
      done*)
      assert false
  | Ireturn None ->
      fprintf pp "\tret void\n"
  | Ireturn (Some arg) ->
      fprintf pp "\tret %a\n" reg arg

type moved = Register of int | Constant of string

let scan_instr phi add_br add_nop add_trv (pc, pc_pos, i) =
  let add_br' s =
    let s = P.to_int s in
    if s <> pc - 1 then add_br s in
  match i with
  | Inop s ->
      add_br' s;
      begin match PTree.get pc_pos phi with
      | None -> add_nop pc (P.to_int s)
      | Some _ -> ()
      end
  | Iop(op, args, res, s) ->
      add_br' s;
      let v =
        let open Op in
        match op with
        | Omove -> Some (Register (P.to_int (List.hd args)))
        | Ointconst n -> Some (Constant (sprintf "%ld" (camlint_of_coqint n)))
        | Olongconst n -> Some (Constant (sprintf "%Ld" (camlint64_of_coqint n)))
        | Ofloatconst n -> Some (Constant (sprintf "%h" (camlfloat_of_coqfloat n)))
        | Osingleconst n -> Some (Constant (sprintf "%h" (camlfloat_of_coqfloat32 n)))
        | _ -> None in
      begin match v with
      | Some v ->
          add_trv (P.to_int res) v;
          begin match PTree.get pc_pos phi with
          | None -> add_nop pc (P.to_int s)
          | Some _ -> ()
          end
      | None -> ()
      end
  | Iload(chunk, addr, args, dst, s) -> add_br' s
  | Istore(chunk, addr, args, src, s) -> add_br' s
  | Icall(sg, fn, args, res, s) -> add_br' s
  | Itailcall(sg, fn, args) -> ()
  | Ibuiltin(ef, args, res, s) -> add_br' s
  | Icond(cond, args, s1, s2) ->
      add_br (P.to_int s1);
      add_br (P.to_int s2)
  | Ijumptable(arg, tbl) ->
      assert false
  | Ireturn None -> ()
  | Ireturn (Some arg) -> ()

let print_function pp id f =
  begin match !source with
  | Some { Syntax.prog_defs = defs } ->
      begin match List.assoc_opt id defs with
      | Some (Syntax.Internal def) ->
          fprintf pp "define %a @%s(%a) {\n"
            b_typ def.Syntax.fn_sig.Types.sig_res
            (extern_atom id)
            b_typed_regs (f.fn_params, def.Syntax.fn_sig.Types.sig_args)
      | _ -> assert false
      end
  | None ->
      fprintf pp "define %a @%s(%a) {\n"
        ret_typ f.fn_sig.sig_res
        (extern_atom id)
        typed_regs (f.fn_params, f.fn_sig.sig_args)
  end;
  let instrs =
    List.sort
      (fun (pc1, _, _) (pc2, _, _) -> Stdlib.compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, pc, i))
        (PTree.elements f.fn_code)) in
  let starts = Hashtbl.create 17 in
  let skips = Hashtbl.create 17 in
  let vals = Hashtbl.create 17 in
  List.iter
    (scan_instr f.fn_phicode
       (fun pc -> Hashtbl.replace starts pc ())
       (fun pc pc' -> Hashtbl.add skips pc pc')
       (fun r v -> Hashtbl.add vals r v)
    ) instrs;
  let pc1 = P.to_int f.fn_entrypoint in
  fprintf pp "entry:\n\tbr label %%l%d\n" pc1;
  Hashtbl.replace starts pc1 ();
  let vreg pp r =
    let rec aux pp r =
      match Hashtbl.find_opt vals r with
      | Some (Register r) -> aux pp r
      | Some (Constant s) -> fprintf pp "%s" s
      | None -> fprintf pp "%%v%d" r in
    aux pp (P.to_int r) in
  List.iter (print_instruction vreg f.fn_phicode pp starts skips) instrs;
  fprintf pp "}\n\n"

let rec print_pp_list pp = function
    [] -> ()
  | x::q -> fprintf pp "%3ld " (P.to_int32 x) ; () ;  print_pp_list pp q ; ()

let rec print_stdout_list = function
    [] -> ()
  | x::q -> printf "%3ld " (P.to_int32 x) ; () ;  print_stdout_list q ; ()

let print_error pp msg =
  let print_one_error = function
    | Errors.MSG s -> fprintf pp ">>>> %s@ " (Camlcoq.camlstring_of_coqstring s)
    | Errors.CTX i -> fprintf pp ">>>> %s@ " (Camlcoq.extern_atom i)
    | _ -> assert false
  in
    fun l ->
      List.iter print_one_error msg;
      print_pp_list pp l ; fprintf pp "@\n " ; ()

let print_error_stdout msg =
  let print_one_error = function
    | Errors.MSG s -> printf ">>>> %s\n" (Camlcoq.camlstring_of_coqstring s)
    | Errors.CTX i -> printf ">>>> %s\n" (Camlcoq.extern_atom i)
    | _ -> assert false
  in
    List.iter print_one_error msg

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: SSA.program) =
  List.iter (print_globdef pp) prog.prog_defs

let print_if optdest passno prog =
  match !optdest with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc

let destination_ssa : string option ref = ref None
let print_ssa = print_if destination_ssa
