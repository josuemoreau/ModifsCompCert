(** Specification of the RTLdpar transformation *)
Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import RTLpar.
Require Import RTL.
Require Import SSA.
Require Import CSSApar.
Require Import SSAutils.
Require Import RTLdpar.
Require Import Kildall.
Require Import Utils.
Require Import Permutation. 
Require Import Bijection.
Require Import DLib.

(** * Checking that the bijection can be applied *)
Inductive is_valid (size: nat) : SSA.instruction ->  Prop := 
| valid_inop : forall s, is_valid size (Inop s)
| valid_iop : forall op args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Iop op args dst s)
| valid_iload : forall ch ad args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Iload ch ad args dst s)
| valid_istore : forall ch ad args src s, 
  (forall r, In r (src::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Istore ch ad args src s)
| valid_icall : forall sig id args dst s, 
  (forall r, In r (dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icall sig (inr reg id) args dst s)
| valid_icall' : forall sig rfun args dst s, 
  (forall r, In r (rfun::dst::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icall sig (inl ident rfun) args dst s)
| valid_itailcall : forall sig id args, 
  (forall r, In r args -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Itailcall sig (inr reg id) args)
| valid_itailcall' : forall sig rfun args, 
  (forall r, In r (rfun::args) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Itailcall sig (inl ident rfun) args)
| valid_ibuiltin : forall ef args dst s, 
  (forall r, In r ((params_of_builtin_res dst)++(params_of_builtin_args args)) -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Ibuiltin ef args dst s)
| valid_icond : forall cond args ifso ifnot, 
  (forall r, In r args -> Bij.valid_index size (snd r) = true) ->
  is_valid size (Icond cond args ifso ifnot) 
| valid_ijump : forall arg tbl, 
  Bij.valid_index size (snd arg) = true -> 
  is_valid size (Ijumptable arg tbl)
| valid_return : forall r, 
  Bij.valid_index size (snd r) = true ->
  is_valid size (Ireturn (Some r))
| valid_return' : is_valid size (Ireturn None).

Definition is_valid_parc (size: nat) (dst: reg) (src: reg) : Prop := 
  (Bij.valid_index size (snd dst) = true) /\ (Bij.valid_index size (snd src) = true).

(** * Specification of RTLdpar *)

Inductive is_jp (jp: node) (code: code) : Prop :=
 | ijp_intro: forall l, 
                (make_predecessors code successors_instr) ! jp = Some l -> 
                length l > 1 ->
                is_jp jp code.

Inductive reach_moves (size : nat) (code : RTL.code) :
                      node -> node -> list (reg * reg) -> list node -> Prop := 
| reach_moves_nil : forall from to, 
                      code ! from = Some (RTL.Inop to) ->
                      reach_moves size code from to nil (from::nil)
| reach_moves_cons : forall from succ to src dst mvs l,
  code ! from = Some (RTL.Iop Omove ((Bij.pamr size src)::nil) (Bij.pamr size dst) succ) ->
  reach_moves size code succ to mvs l ->
  reach_moves size code from to ((src,dst)::mvs) (from::l).

Lemma reach_moves_last_inop : forall size code l from to mvs,
  reach_moves size code from to mvs l ->
  exists last l', (rev l) = last::l' /\ code ! last = Some (RTL.Inop to).
Proof.
  induction l ; intros; invh reach_moves ; go.
  exploit IHl; eauto; intros; try invh and.
  repeat (repeat invh ex ; repeat invh and); subst.
  simpl. rewrite H0. go.
Qed.

Inductive rtldpar_spec (size : nat) (tmp: reg) (code1: code) (pcode1: parcopycode) 
          (code2: RTL.code) (R: node -> node) (pc: node): Prop :=
| dspec_noblock : forall succ,
  code1 ! pc = Some (Inop succ) ->
  (pcode1 ! pc = None) ->
  ~ is_jp succ code1 ->
  code2 ! pc = Some (RTL.Inop succ) ->
  R pc = pc ->

  rtldpar_spec size tmp code1 pcode1 code2 R pc

| dspec_block_pre : forall fresh succ parcb lnew mvs,
  code1 ! pc = Some (Inop succ) ->
  ~ is_jp pc code1 ->
  pcode1 ! pc = Some parcb ->

  code2 ! pc = Some (RTL.Inop fresh) ->
  mvs = (seq_parmoves tmp (parcb_to_moves parcb)) ->
  (forall src dst, In (src,dst) (parcb_to_moves parcb) -> Bij.valid_index size (snd src) = true) ->
  (forall src dst, In (src,dst) (parcb_to_moves parcb) -> Bij.valid_index size (snd dst) = true) ->

  reach_moves size code2 fresh succ mvs lnew ->

  R pc = pc ->

  rtldpar_spec size tmp code1 pcode1 code2 R pc

| dspec_block_jp : forall fresh succ parcb lnew mvs rpc,
  code1 ! pc = Some (Inop succ) ->
  is_jp pc code1 ->
  pcode1 ! pc = Some parcb ->
  
  code2 ! pc = Some (RTL.Inop fresh) ->
  mvs = (seq_parmoves tmp (parcb_to_moves parcb)) ->
  (forall src dst, In (src,dst) (parcb_to_moves parcb) -> Bij.valid_index size (snd src) = true) ->
  (forall src dst, In (src,dst) (parcb_to_moves parcb) -> Bij.valid_index size (snd dst) = true) ->

  reach_moves size code2 fresh succ mvs (rev (rpc::lnew)) ->

  (R pc) = rpc ->

  code2 ! (R pc) = Some (RTL.Inop succ) ->
  
  rtldpar_spec size tmp code1 pcode1 code2 R pc

| dspec_copy : forall ins ins', 
  code1 ! pc = Some ins -> 
  (is_valid size ins) ->
  (forall succ, ins <> Inop succ) ->
  (map_pamr size ins) = Errors.OK ins' ->
  code2 ! pc = Some ins' ->
  R pc = pc ->
  rtldpar_spec size tmp code1 pcode1 code2 R pc.  

Definition map_pc (pnum: PTree.t node) (pc: node) : node :=
  match pnum!pc with
  | Some pc' => pc'
  | None => 1%positive (* impossible case, never exercised *)
  end.

Inductive transl_function_spec: RTLpar.function -> RTL.function -> (node -> node) -> Prop :=
| transl_function_spec_intro: forall f tf preds init max pl s incr 
  (PREDS: preds = (make_predecessors (RTLpar.fn_code f) successors_instr))
  (PARAMS: forall p, In p (RTLpar.fn_params f) -> Bij.valid_index (RTLpar.fn_max_indice f) (snd p) = true)
  (VALIDFRESH: Bij.valid_index (RTLpar.fn_max_indice f) (snd (fresh_init f)) = true)
  (INITS: (init,max,pl) = init_state f)
  (MFOLD: mfold_unit (copy_wwo_add (fresh_init f) (RTLpar.fn_max_indice f) 
                                   preds (RTLpar.fn_code f) (RTLpar.fn_parcopycode f) max) 
                     (sort_pp pl) init = OK tt s incr)
  (DPARSPEC: forall pc ins, (RTLpar.fn_code f) ! pc = Some ins -> 
                            rtldpar_spec (RTLpar.fn_max_indice f) (fresh_init f)
                                         (RTLpar.fn_code f)
                                         (RTLpar.fn_parcopycode f) 
                                         (RTL.fn_code tf) 
                                         (map_pc (st_renum s)) pc),
  transl_function_spec f tf (map_pc (st_renum s)).