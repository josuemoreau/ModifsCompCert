(** Specification of the SSA validator, in terms of a type
    system. Auxiliary definitions may be found in
    the [Utilsvalidproof] file. *)

Require Import Coq.Unicode.Utf8.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTLt.
Require Import Kildall.
Require Import KildallComp.
Require Import Conventions.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import Utilsvalidproof.
Require Import LightLive.
Require Import Utils.
Require Import Classical.
Require Import Path.
Require Import Bijection.

(** * Typing phi-blocks *)
Section WT_PHI.
Variable funct: SSA.function.
Variable size: nat.

Inductive wt_phid (block:phiblock) (γ1 γ2: Registers.reg -> index) (live:Regset.t) : Prop :=
  | wt_phid_intro : forall
    (ASSIG: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) ->  γ2 r = i)
    (VALIDI: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) ->  Bij.valid_index size i = true)
    (VALIDR: forall ri, assigned ri block -> Bij.valid_reg_ssa size ri = true)
    (LIVE: forall ri r i, assigned ri block -> Bij.rmap size ri = (r,i) -> Regset.In r live )
    (NASSIG:forall r, 
      (forall ri i, Bij.rmap size ri = (r,i) -> not (assigned ri block)) -> 
      (γ2 r = γ1 r) \/ ~ (Regset.In r live)), 
    wt_phid block γ1 γ2 live.

Inductive phiu (r: Registers.reg) : list reg -> (list (Registers.reg -> index)) -> Prop :=
| phiu_nil : phiu r nil nil
| phiu_cons: forall arg g args gl i
  (PHIU: phiu r args gl)  
  (RMAP: Bij.rmap size arg = (r,i))
  (VALIDI: Bij.valid_index size i = true)
  (VALIDR: Bij.valid_reg_ssa size arg = true)
  (GARG: g r = i), 
    phiu r (arg::args) (g::gl).  

Lemma phiu_nth : forall r k args gammas ri g,
  phiu r args gammas -> 
  nth_error args k = Some ri ->
  nth_error gammas k = Some g ->
  Bij.valid_reg_ssa size ri = true /\ exists i, Bij.rmap size ri = (r,i) /\ g r = i /\ Bij.valid_index size i = true.
Proof.
  induction k; intros.
  inv H; simpl in *; inv H0. inv H1 ; eauto.
  destruct args ; simpl in * ; inv H0.
  destruct gammas ; simpl in * ; inv H1.
  inv H ; eauto.
Qed.

Inductive wt_phiu (preds: list node) (block:phiblock) (Γ: tgamma) :=
| wt_phiu_intro: forall
    (USES: (forall args dst r i, In (Iphi args dst) block ->
                                 Bij.rmap size dst = (r,i) -> phiu r args (map Γ preds))), 
    wt_phiu preds block Γ.

End WT_PHI.  

(** * Typing edges *)
Section WT_EDGE.
Variable funct: SSA.function.
Variable size: nat.

Inductive wt_edge (live: Regset.t) : tgamma -> node -> node -> Prop :=
| wt_edge_not_jp:  forall (Γ:tgamma) (i j :node) (ins: instruction)
      (EDGE: is_edge funct i j)
      (INS: (fn_code funct)!i = Some ins)
      (NOPHI: (fn_phicode funct)!j = None)
      (EIDX: wt_eidx size (Γ (fn_entrypoint funct)) ins)
      (WTI: wt_instr size (Γ i) ins (Γ j)), 
      (wt_edge live Γ i j)
| wt_edge_jp: forall (Γ:tgamma) (i j:node) (predsj: list node) (ins: instruction) (block: phiblock) (dft: positive)
      (EDGE: is_edge funct i j)
      (INS:  (fn_code funct)!i = Some ins)
      (PHI:  (fn_phicode funct)!j = Some block)
      (PREDS: predsj = (make_predecessors (fn_code funct) successors_instr)!!!j)
      (EIDX: wt_eidx size (Γ (fn_entrypoint funct)) ins)
      (PEIDX: wt_ephi size (Γ (fn_entrypoint funct)) block)
      (WTPHID: wt_phid size block (Γ i) (Γ j) live)
      (WTPHID: wt_phiu size predsj block Γ),
      (wt_edge live Γ i j).
  
End WT_EDGE.

Arguments Lout [A].

(** * Well-typed functions *)
Inductive wt_function (size: nat) (f: RTLt.function) (tf: function) (live: PMap.t Regset.t) (Γ:tgamma): Prop :=
| wt_fun_intro : forall
    (WTE: forall i j, is_edge tf i j -> wt_edge tf size (Lin f j (Lout live)) Γ i j)
    (WTO: forall i, is_out_node tf i -> wt_out size tf Γ i), 
    wt_function size f tf live Γ.

(** * Overall specification of a validated function *)
Definition normalised_function (f : RTLt.function) : Prop :=
  check_function_inv f (make_predecessors (RTLt.fn_code f) RTLt.successors_instr) = true.

Definition check_function_spec (size: nat) (f: RTLt.function) (live: PMap.t Regset.t) (tf: SSA.function) Γ :=
  (structural_checks_spec size f tf)
  /\ (wf_init size tf Γ)
  /\ (wt_function size f tf live Γ)
  /\ (wf_live f (Lout live)).
