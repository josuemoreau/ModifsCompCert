Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSApar.
Require Import CSSApargenproof.
Require RTLpar.
Require Import RTLpargensimpl.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import Events.
Require CSSAlive.
Require Import CSSAval.
Require Import CSSAninterf.
Require Import CSSAutils.
Require Import Classical.
Require Import CSSApardef.
Require CSSAliverange.

(*
  (pred)  u_k = a_k
          ...
          
  (pc)    u_0 = phi(...,u_k,...)
          ...

          a_0 = u_0
          ...

         use     def
  --------------------
  a_k    pred    <
  u_k    pred    pred
  u_0    pc      pc
  a_0    >=      pc

*)
Lemma compute_phi_classes_other_aux :
  forall args (r dst : reg) classes,
  classes !2 r = None ->
  ~ In r args ->
  (fold_right
    (fun arg acc =>
      P2Tree.set arg dst acc)
    classes args) !2 r = None.
Proof.
  induction args; simpl; auto; intros.
  rewrite P2Tree.gso.
  eapply IHargs; eauto. intuition eauto.
Qed.

Lemma compute_phi_classes_other :
  forall args r dst classes,
  classes !2 r = None ->
  ~ In r args ->
  (compute_phi_classes (Iphi args dst) classes) !2 r = None.
Proof.
  unfold compute_phi_classes.
  intros.
  rewrite <- fold_left_rev_right.
  eapply compute_phi_classes_other_aux; eauto.
  unfold not; intros.
  contradict H0.
  apply in_rev; auto.
Qed.

Lemma compute_phib_classes_other_aux :
  forall phib r classes,
  classes !2 r = None ->
  (forall args dst,
    In (Iphi args dst) phib ->
    ~ In r args) ->
  (fold_right
    (fun phi acc => compute_phi_classes phi acc)
    classes phib) !2 r = None.
Proof.
  induction phib; simpl; auto; intros.
  destruct a.
  eapply compute_phi_classes_other; eauto.
Qed.

Lemma compute_phib_classes_other :
  forall phib r classes,
  classes !2 r = None ->
  (forall args dst,
    In (Iphi args dst) phib ->
    ~ In r args) ->
  (compute_phib_classes phib classes) !2 r = None.
Proof.
  unfold compute_phib_classes.
  intros.
  rewrite <- fold_left_rev_right.
  eapply compute_phib_classes_other_aux; eauto.
  unfold not; intros.
  contradict H2.
  eapply H0 with (dst := dst); eauto.
  apply in_rev; auto.
Qed.

Lemma compute_phicode_classes_other_aux :
  forall (elems : list (node * phiblock)) classes r,
  classes !2 r = None ->
  (forall pc phib,
    In (pc, phib) elems ->
    (forall args dst,
      In (Iphi args dst) phib ->
      ~ In r args)) ->
  (fold_right
    (fun pcphib acc =>
          compute_phib_classes (snd pcphib) acc)
    classes elems) !2 r = None.
Proof.
  induction elems; simpl; auto; intros.
  eapply compute_phib_classes_other; eauto.
  intros.
  destruct a; simpl in *.
  eapply H0; eauto.
Qed.

Lemma nodups_in_preds :
  forall l f preds pc,
  wf_cssa_function f ->
  preds = make_predecessors (fn_code f) successors_instr ->
  (fn_phicode f) ! pc <> None ->
  preds ! pc = Some (l : list node) ->
  ~ In pc l ->
  NoDup (pc :: l).
Proof.
  intros.
  constructor; auto.
  assert(EQ: preds !!! pc = l).
  unfold successors_list; go.
  rewrite <- EQ.
  rewrite H0.
  unfold make_predecessors.
  rewrite PTree.fold_spec.
  rewrite <- List.fold_left_rev_right.
  apply nodups_in_preds_aux; intros.
  { rewrite <- in_rev in H4.
    destruct pcins.
    simpl in *.
    assert ((fn_code f) ! p = Some i).
    apply PTree.elements_complete. auto.
    assert (JP: join_point pc f).
    induction H. apply fn_phicode_inv. auto.
    assert (Insuccs: In pc (succs f p)).
    unfold successors.
    unfold successors_list. flatten.
    { rewrite PTree.gmap1 in Eq.
      rewrite H6 in Eq.
      simpl in *. go. }
    { rewrite PTree.gmap1 in Eq.
      rewrite H6 in Eq.
      simpl in *. congruence. }
    assert ((fn_code f) ! p = Some (Inop pc)).
    induction H.
    apply fn_normalized; auto.
    assert(RW: i = Inop pc).
    congruence.
    rewrite RW. auto.
  }
  { unfold successors_list. flatten ; auto.
    assert((PTree.empty (list positive)) ! pc = None).
    apply PTree.gempty. congruence. }
  { rewrite map_rev.
    cut (NoDup (rev (rev (map fst
      (PTree.elements (fn_code f))))));
      intros.
    apply nodups_rev.
    auto.
    rewrite rev_involutive.
    assert (list_norepet
      (map fst (PTree.elements (fn_code f)))).
    apply PTree.elements_keys_norepet.
    apply list_norepet_NoDup; auto. }
  { unfold successors_list; flatten.
    assert ((PTree.empty (list positive)) ! pc = None).
    apply PTree.gempty. congruence.
    constructor. }
Qed.

Lemma compute_phicode_classes_other :
  forall f r,
  wf_cssa_function f ->
  (forall pc, ~ use_phicode f r pc) ->
  (compute_phicode_classes f) !2 r = None.
Proof.
  intros f r WF Hnotuse.
  unfold compute_phicode_classes.
  rewrite PTree.fold_spec.
  rewrite <- fold_left_rev_right.
  eapply compute_phicode_classes_other_aux; eauto.
  + apply P2Tree.gempty.
  + intros.
    unfold not; intros.
    rewrite <- in_rev in H; auto.
    exploit PTree.elements_complete; eauto.
    intros.
    exploit in_nth_error_some; eauto.
    intros Hexists.
    destruct Hexists as [k nth].
    induction WF.
    unfold block_nb_args in fn_wf_block.
    assert(Hpred: exists pred,
      nth_error ((get_preds f) !!! pc) k = Some pred).
    eapply nth_error_some_same_length; eauto.
    symmetry.
    eapply fn_wf_block; eauto.
    destruct Hpred as [pred nthpred].
    exploit (Hnotuse pred); eauto. 
    eapply upc_intro with (pc := pc); eauto.
    assert(Hhaspreds: (get_preds f) ! pc = Some (get_preds f) !!! pc).
    {
      unfold successors_list.
      flatten; auto.
      unfold successors_list in nthpred.
      flatten nthpred.
      destruct k; simpl in *;
      unfold error in nthpred; go.
    }
    eapply CSSApargenproof.index_pred_from_nth; eauto.
    eapply nodups_in_preds with (f := f)
      (preds := get_preds f); go.
    {
      unfold not; intros Hin.
      unfold successors_list in Hin.
      flatten Hin; go.
      assert(Hjp: join_point pc f).
      eapply fn_phicode_inv; congruence.
      exploit (fn_inop_in_jp pc); go.
      intros Hinop.
      destruct Hinop as [succ Hinop].
      unfold node in *.
      exploit fn_normalized_jp; go.
      go. go.
    }
Qed.

Lemma compute_regrepr_affects_only_phi_resources :
  forall f r regrepr,
  wf_cssa_function f ->
  compute_regrepr f = Errors.OK regrepr ->
  (forall pc, ~ use_phicode f r pc) ->
  regrepr r = r.
Proof.
  intros f r regrepr WF Hregrepr Hnotuse.
  unfold compute_regrepr in Hregrepr.
  flatten Hregrepr.
  erewrite compute_phicode_classes_other; eauto.
Qed.

Lemma compute_regrepr_for_phi_resources :
  forall f regrepr phib pc r dst args,
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  In r (dst :: args) ->
  regrepr r = dst.
Proof.
  intros until args.
  intros Hregrepr Hphib Hphi Hinr.
  unfold compute_regrepr in Hregrepr.
  flatten Hregrepr.
  unfold check_cssa_coalescing_in_phicode in Eq.
  unfold check_cssa_coalescing_in_phib in Eq.
  unfold check_phi_ressources_coalescing in Eq.
  rewrite forallb_forall in Eq.
  specialize (Eq phib).
  exploit Eq; eauto.
  exploit PTree.elements_correct; eauto. intros.
  eapply In_Insnd_phib; eauto.
  intros Hcssaphi.
  rewrite forallb_forall in Hcssaphi.
  specialize (Hcssaphi (Iphi args dst)).
  exploit Hcssaphi; eauto.
  intros Hcssaarg.
  rewrite forallb_forall in Hcssaarg.
  case_eq (p2eq r dst); intros. rewrite e in *.
  exploit (Hcssaarg dst); eauto.
  intros Eqrdst.
  destruct p2eq in Eqrdst; go. flatten e0.
  exploit (Hcssaarg r); eauto. inv Hinr; auto. congruence.
  intros Eqrdst.
  destruct p2eq in Eqrdst; go.
Qed.

Lemma compute_regrepr_init :
  forall f regrepr phib pc r r' dst args,
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  In r (dst :: args) ->
  In r' (dst :: args) ->
  regrepr r = regrepr r'.
Proof.
  intros.
  assert(regrepr r = dst).
  eapply compute_regrepr_for_phi_resources; eauto.
  assert(regrepr r' = dst).
  eapply compute_regrepr_for_phi_resources; eauto.
  congruence.
Qed.

Lemma compute_regrepr_if_eq :
  forall f regrepr phib pc r r' dst args,
  wf_cssa_function f ->
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  In r (dst :: args) ->
  regrepr r = regrepr r' ->
  In r' (dst :: args).
Proof.
  intros until args.
  intros WF Hregrepr Hphib Hinphib Hinr Heqregreprs.
  assert(Huser: (forall pc, ~ use_phicode f r' pc)
   \/ (~ forall pc, ~ use_phicode f r' pc)).
  apply classic.
  destruct Huser.
  + assert(regrepr r' = r')
     by (eapply compute_regrepr_affects_only_phi_resources; eauto).
    assert(regrepr r = dst).
    eapply compute_regrepr_for_phi_resources; eauto.
    assert(r' = dst). go. go.
  + exploit not_all_not_ex; eauto.
    intros Hexists.
    destruct Hexists as [n Husephi].
    inv Husephi.
    assert(regrepr r' = dst0).
    eapply compute_regrepr_for_phi_resources; eauto.
    assert(regrepr r = dst).
    eapply compute_regrepr_for_phi_resources with (phib := phib); eauto.
    assert(RW: dst0 = dst) by go.
    rewrite RW in *.
    assert(def f dst pc) by go.
    assert(def f dst pc0) by go.
    assert(EQpcs: pc0 = pc).
    eapply def_def_eq; eauto.
    rewrite EQpcs in *.
    assert(args0 = args).
    induction WF. inv fn_cssa.
    destruct H5.
    specialize (H0 pc phib).
    eapply H0; eauto.
    go. go.
Qed.

Definition wf_cssa_liverange (f : function) : Prop :=
  forall r1 r2 pc resources,
  CSSAliverange.phi_resources f pc resources ->
  In r1 resources ->
  In r2 resources ->
  r1 = r2 \/ ninterlive_spec f r1 r2.

Lemma compute_regrepr_correct :
  forall f r r' regrepr,
  wf_cssa_function f ->
  wf_cssa_liverange f ->
  compute_regrepr f = Errors.OK regrepr ->
  regrepr r = regrepr r' ->
  r <> r' ->
  (exists d1, def f r d1) ->
  (exists d2, def f r' d2) ->
  ninterlive_spec f r r'.
Proof.
  intros f r r' regrepr WF Hcssaliverange Hregrepr Heq Hneq Hd1 Hd2.
  assert(Huser: (forall pc, ~ use_phicode f r pc)
   \/ (~ forall pc, ~ use_phicode f r pc)).
  apply classic.
  assert(Huser': (forall pc, ~ use_phicode f r' pc)
   \/ (~ forall pc, ~ use_phicode f r' pc)).
  apply classic.
  destruct Huser; destruct Huser'.
  + assert(regrepr r = r).
    eapply compute_regrepr_affects_only_phi_resources; eauto.
    assert(regrepr r' = r').
    eapply compute_regrepr_affects_only_phi_resources; eauto.
    congruence.
  + assert(Hregrepr_r: regrepr r = r).
    eapply compute_regrepr_affects_only_phi_resources; eauto.
    exploit not_all_not_ex; eauto.
    intros Hexists.
    destruct Hexists as [n Huse].
    inv Huse.
    assert(Hregrepr_r': regrepr r' = dst).
    eapply compute_regrepr_for_phi_resources; eauto.
    assert(EQ: dst = r) by go.
    rewrite EQ in *.
    assert(CSSAliverange.phi_resources f pc (r :: args)).
    go.
    assert(In r (r :: args)) by go.
    assert(In r' (r :: args)).
    constructor 2.
    eapply nth_error_some_in; eauto.
    unfold wf_cssa_liverange in Hcssaliverange.
    assert(r = r' \/ ninterlive_spec f r r').
    eapply Hcssaliverange; eauto.
    tauto.
  + assert(Hregrepr_r': regrepr r' = r').
    eapply compute_regrepr_affects_only_phi_resources; eauto.
    exploit not_all_not_ex; eauto.
    intros Hexists.
    destruct Hexists as [n Huse].
    inv Huse.
    assert(Hregrepr_r: regrepr r = dst).
    eapply compute_regrepr_for_phi_resources; eauto.
    assert(EQ: dst = r') by go.
    rewrite EQ in *.
    assert(CSSAliverange.phi_resources f pc (r' :: args)).
    go.
    assert(In r' (r' :: args)) by go.
    assert(In r (r' :: args)).
    constructor 2.
    eapply nth_error_some_in; eauto.
    unfold wf_cssa_liverange in Hcssaliverange.
    assert(r = r' \/ ninterlive_spec f r r').
    eapply Hcssaliverange; eauto.
    tauto.
  + exploit not_all_not_ex; eauto.
    intros Hexists.
    destruct Hexists as [n Huse].
    clear H0.
    exploit not_all_not_ex; eauto.
    intros Hexists'.
    destruct Hexists' as [n' Huse'].
    clear H.
    inv Huse.
    inv Huse'.
    assert(Hregrepr_r: regrepr r = dst0).
    eapply compute_regrepr_for_phi_resources; eauto.
    assert(Hregrepr_r': regrepr r' = dst).
    eapply compute_regrepr_for_phi_resources
      with (phib := phib); eauto.
    assert(EQ: dst0 = dst) by go. rewrite EQ in *.
    assert(EQpcs: pc0 = pc).
    {
      assert(assigned_phi_spec (fn_phicode f) pc dst) by go.
      assert(assigned_phi_spec (fn_phicode f) pc0 dst) by go.
      induction WF.
      inv fn_cssa.
      specialize (H1 (regrepr r) pc0 pc).
      intuition.
    }
    rewrite EQpcs in *.
    assert(EQphibs: phib0 = phib) by go.
    rewrite EQphibs in *.
    induction WF.
    inv fn_cssa.
    destruct H0.
    specialize (H0 pc phib).
    exploit H0; eauto.
    intros Hnodup.
    assert(EQargs: args0 = args).
    eapply Hnodup; eauto.
    rewrite EQargs in *.
    assert(CSSAliverange.phi_resources f pc
      ((regrepr r) :: args)).
    go.
    assert(In r' ((regrepr r) :: args)) by go.
    assert(In r ((regrepr r) :: args)) by go.
    unfold wf_cssa_liverange in Hcssaliverange.
    assert(r = r' \/ ninterlive_spec f r r').
    eapply Hcssaliverange; eauto.
    tauto.
Qed.

Lemma cssalive_path_to_def :
  forall f,
  wf_cssa_function f ->
  forall l pc pc',
  CSSApath f (PState pc) l (PState pc') ->
  forall r d,
  cssalive_spec f r pc' ->
  def f r d ->
  ~ In d l ->
  cssalive_spec f r pc.
Proof.
  intros f WF.
  induction l; intros.
  + inv H. auto.
  + inv H.
    assert(Hnotin: ~ In d l) by go.
    assert(Hneq: d <> a) by go.
    inv STEP.
    - assert(cssalive_spec f r pc'0).
      apply IHl with (pc' := pc') (d := d); eauto.
      constructor 2 with (pc' := pc'0). auto.
      unfold not; intros.
      assert(d = a) by (eapply def_def_eq; eauto). congruence.
      auto.
    - assert(l = nil).
      eapply path_from_ret_nil; eauto.
      rewrite H in *.
      inv PATH.
Qed.

Lemma shorten_path :
  forall f p pc pc',
  CSSApath f (PState pc) p (PState pc') ->
  forall pc'',
  In pc'' p ->
  exists p',
    CSSApath f (PState pc'') (pc'' :: p') (PState pc') /\
    ~ In pc'' p'.
Proof.
 intros f p pc pc' H. induction H; intros.
 + inv H.
 + simpl in *.
   assert(Hinnotin: In pc'' t \/ ~ In pc'' t) by apply classic.
   destruct Hinnotin.
   - destruct s2. inv STEP.
     eapply IHpath; eauto.
     exploit path_from_ret_nil; eauto.
     intros Hnil. rewrite Hnil in *.
     inv H1.
   - destruct H0; try congruence.
     rewrite H0 in *.
     exists t.
     split; auto.
     econstructor; eauto.
     inv STEP; auto;
     constructor; auto.
Qed.

(** Transformation stuff *)
Inductive transl_function_spec:
  CSSApar.function -> RTLpar.function -> Prop :=
| transl_function_spec_intro:
    forall f tf regrepr
    (RegRepr: compute_regrepr f = Errors.OK regrepr)
    (codeNone: forall pc,
      (fn_code f) ! pc = None ->
      (RTLpar.fn_code tf) ! pc = None)
    (codeSome: forall pc ins,
      (fn_code f) ! pc = Some ins ->
      (RTLpar.fn_code tf) ! pc =
        Some (transl_instruction regrepr ins))
    (parcbNone: forall pc,
      (fn_parcopycode f) ! pc = None ->
      (RTLpar.fn_parcopycode tf) ! pc = None)
    (parcbSome: forall pc parcb,
      (fn_parcopycode f) ! pc = Some parcb ->
      (RTLpar.fn_parcopycode tf) ! pc =
        Some (transl_parcb regrepr parcb)),
    transl_function_spec f tf.

Inductive tr_function: CSSApar.function -> RTLpar.function -> Prop :=
| tr_function_intro:
    forall f regrepr (Regrepr: compute_regrepr f = Errors.OK regrepr),
    tr_function
      f
      (RTLpar.mkfunction
        f.(fn_sig)
        (map regrepr f.(fn_params))
        f.(fn_stacksize)
        (transl_code regrepr f.(fn_code))
        (transl_parcopycode regrepr f.(fn_parcopycode))
        f.(fn_max_indice)
        f.(fn_entrypoint)).

(** transformation *)

Lemma transl_function_charact:
  forall f tf,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros.
  unfold transl_function in H0.
  flatten H0.
  apply tr_function_intro. auto.
Qed.

Lemma transl_function_correct :
  forall f tf,
  tr_function f tf ->
  transl_function_spec f tf.
Proof.
  intros.
  inv H.
  apply transl_function_spec_intro with (regrepr := regrepr);
    auto; simpl; intros;
    try unfold transl_code;
    try unfold transl_parcopycode;
    try (rewrite PTree.gmap1; unfold option_map; flatten; go);
    try (unfold parcopycode_cleanup;
      rewrite PTree.gmap1; unfold option_map; flatten; go);
    try (rewrite PTree.gmap1 in Eq; unfold option_map in Eq;
      flatten Eq; go).
Qed.

Definition transl_fundef :=
  transf_partial_fundef transl_function.

(** match_states *)

(* Il va falloir plusieurs propriétés côté source.

   Il faut avoir la propriété qui dit que si deux
   variables ont même SSA valeur, alors si un point
   pc est atteint où elles sont toutes les deux vivantes,
   alors en ce point les regsets doivent matcher.

   Pour la liveness, il faudra utiliser que si une variable
   n'est pas vivante en un point, elle n'est pas utilisée
   en ce point.
*)

Inductive lazydef
    (f : function) (r : reg) (pc : node) : Prop :=
| lazydef_phi:
    assigned_phi_spec (fn_phicode f) pc r ->
    lazydef f r pc
| lazydef_parcb':
    assigned_parcopy_spec (fn_parcopycode f) pc r ->
    join_point pc f ->
    lazydef f r pc.

Inductive match_regset (f : CSSApar.function) (pc : node) :
    SSA.regset -> SSA.regset -> Prop :=
| mrg_intro :
    forall rs rs' regrepr
      (RegRepr: compute_regrepr f = Errors.OK regrepr),
    (forall r,
      (cssalive_spec f r pc /\ ~ lazydef f r pc)
      \/ lazydef f r pc ->
      rs #2 r = rs' #2 (regrepr r)) ->
    match_regset f pc rs rs'.

Inductive match_stackframes :
    list CSSApar.stackframe -> list RTLpar.stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons:
    forall res f sp pc rs rs' s tf ts regrepr
      (STACK : match_stackframes s ts )
      (SPEC: transl_function f = Errors.OK tf)
      (WFF: wf_cssa_function f)
      (WFlive: wf_cssa_liverange f)
      (RegRepr: compute_regrepr f = Errors.OK regrepr)
      (MRs: forall r,
        (cssalive_spec f r pc /\ ~ lazydef f r pc /\ r <> res)
        \/ lazydef f r pc ->
        rs #2 r = rs' #2 (regrepr r))
      (Hnotlive: forall r,
        regrepr r = regrepr res ->
        r <> res ->
        ~ cssalive_spec f r pc)
      (Hnotlazydef: forall r, ~ lazydef f r pc),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (RTLpar.Stackframe (regrepr res) tf sp pc rs' :: ts).

Hint Constructors match_stackframes.

Set Implicit Arguments.

Section PRESERVATION.

(** Well-formed CSSA function definitions *)
Inductive wf_cssa_liverange_fundef: fundef -> Prop :=
  | wf_cssa_liverange_fundef_external: forall ef,
      wf_cssa_liverange_fundef (External ef)
  | wf_cssa_liverange_function_internal: forall f,
      wf_cssa_liverange f ->
      wf_cssa_liverange_fundef (Internal f).

(** Well-formed CSSA programs *)
Definition wf_cssa_liverange_program (p: program) : Prop :=
  forall f id, In (id, Gfun f) (prog_defs p) -> wf_cssa_liverange_fundef f.

Variable prog: CSSApar.program.
Variable tprog: RTLpar.program.
Hypothesis TRANSF_PROG: transl_program prog = Errors.OK tprog.
Hypothesis WF_PROG : wf_cssa_program prog.
Hypothesis WFlive_PROG : wf_cssa_liverange_program prog.

Inductive match_states: CSSApar.state -> RTLpar.state -> Prop :=
| match_states_intro:
    forall s ts sp pc rs rs' m f tf
      (SPEC: transl_function f = Errors.OK tf)
      (STACK: match_stackframes s ts)
      (WFF: wf_cssa_function f)
      (WFlive: wf_cssa_liverange f)
      (MREG: match_regset f pc rs rs'),
    match_states
      (State s f sp pc rs m)
      (RTLpar.State ts tf sp pc rs' m)
| match_states_call:
    forall s ts f tf args m
      (SPEC: transl_fundef f = Errors.OK tf)
      (STACK: match_stackframes s ts)
      (WFF: wf_cssa_fundef f)
      (WFlive: wf_cssa_liverange_fundef f),
    match_states
      (Callstate s f args m)
      (RTLpar.Callstate ts tf args m)
| match_states_return:
    forall s ts v m
      (STACK: match_stackframes s ts ),
    match_states
      (Returnstate s v m)
      (RTLpar.Returnstate ts v m).

Hint Constructors match_states.

Definition transl_program (p: CSSApar.program) :
    Errors.res RTLpar.program :=
  transform_partial_program transl_fundef p.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(* NOTE: important *)
Lemma parcb_transl_other :
  forall parcb f r rs' regrepr,
  compute_regrepr f = Errors.OK regrepr ->
  (forall src dst,
    In (Iparcopy src dst) parcb ->
    (regrepr r) <> (regrepr dst) \/
    regrepr r = regrepr dst /\
    rs' #2 (regrepr r) =
      rs' #2 (regrepr src)) ->
  (parcopy_store 
    (transl_parcb regrepr parcb) rs')
  #2 (regrepr r) =
    rs' #2 (regrepr r).
Proof.
  induction parcb; auto.
  intros f r rs' regrepr Hregrepr Hprops.
  simpl in *.
  destruct a.
  case_eq (p2eq (regrepr r)
    (regrepr r1)); intros.
  + rewrite e in *.
    rewrite P2Map.gss; eauto.
    exploit (Hprops r0 r1). go.
    intros Hprop.
    destruct Hprop; go.
    destruct H0; go.
  + rewrite P2Map.gso; eauto.
Qed.

(* NOTE: important *)
Lemma parcb_transl_store_in :
  forall parcb f rs' r src regrepr,
  In (Iparcopy src r) parcb ->
  NoDup (map parc_dst parcb) ->
  (forall src' dst,
    In (Iparcopy src' dst) parcb ->
    (regrepr r) <> (regrepr dst) \/
    rs' #2 (regrepr src') =
      rs' #2 (regrepr src)) ->
  compute_regrepr f = Errors.OK regrepr ->
  (parcopy_store 
    (transl_parcb regrepr parcb) rs')
    #2 (regrepr r)
    = rs' #2 (regrepr src).
Proof.
  induction parcb;
  intros f rs' r src regrepr Hin HNoDup Hprops Hregrepr;
  simpl in *.
  + contradiction.
  + destruct a.
    destruct Hin.
    - assert (EQ1: r1 = r) by congruence.
      assert (EQ2: r0 = src) by congruence.
      rewrite EQ1, EQ2 in *.
      rewrite P2Map.gss.
      auto.
    - inv HNoDup.
      case_eq (p2eq (regrepr r1) (regrepr r));
        intros; simpl.
      { rewrite e in *.
        rewrite P2Map.gss.
        exploit (Hprops r0 r1); auto; intros.
        destruct H1; congruence. }
      { rewrite P2Map.gso; eauto. }
Qed.

(* 
   blocs de copies parallèles:
    - c'est la première occurence d'une copie qui l'emporte
    - dans cssa il n'y a qu'une seule définition, donc
      c'est facile
    - dans rtlpar, suite au coalescing, on peut avoir
      deux fois
        u = ...
        ...
        u = ...
      où le premier u provient de r1, et le deuxième de r2.
      celui qui l'emporte est le premier, mais si on a eu
      coalescing comme ça, c'est que les valeurs des trucs
      qu'on donne sont les mêmes, c'est à dire
        regrepr r1 = regrepr r2 = regrepr "trucs de droite".
*)

Lemma no_successive_jp :
  forall f pc pc',
  wf_cssa_function f ->
  join_point pc f ->
  join_point pc' f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  False.
Proof.
  intros until pc'.
  intros WF jp_pc jp_pc' Hinop.
  induction WF.
  assert((fn_phicode f) ! pc = None).
  assert(HInpreds: In pc (get_preds f) !!! pc').
  apply make_predecessors_correct_1
    with (instr := Inop pc').
  auto. go.
  unfold successors_list in HInpreds.
  flatten HInpreds.
  apply fn_normalized_jp with (pc := pc')
    (preds := (get_preds f) !!! pc'); try congruence.
  apply fn_phicode_inv; auto.
  unfold successors_list. flatten.
  unfold successors_list. flatten.
  auto.
  inv HInpreds.
  assert((fn_phicode f) ! pc <> None).
  apply fn_phicode_inv; auto.
  congruence.
Qed.

(** ** Simulation lemmas *)
Lemma not_lazydef_in_pred :
  forall f pc pc' phib r,
  wf_cssa_function f ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  ~ lazydef f r pc.
Proof.
  intros until r.
  intros WF Hphib Hinop.
  unfold not; intros Hlazy.
  assert ((fn_phicode f) ! pc = None).
  eapply jp_not_preceded_by_jp; eauto. go.
  inv Hlazy.
  inv H0. go.
  inv H0.
  induction WF.
  assert ((fn_phicode f) ! pc <> None).
  apply fn_phicode_inv; auto.
  congruence.
Qed.

Lemma not_use_and_def_in_jppred :
  forall f pc parcb pc' phib r src,
  wf_cssa_function f ->
  (fn_parcopycode f) ! pc = Some parcb ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  In (Iparcopy src r) parcb ->
  ~ def f src pc.
Proof.
  intros until src.
  intros WF Hparcb Hphib Hinop HIn.
  unfold not; intros.
  inv H.
  + assert ((fn_parcopycode f) ! (fn_entrypoint f) = None).
    induction WF; go. congruence.
  + inv H0; go.
  + inv H0.
    assert(WFaux: wf_cssa_function f) by auto.
    induction WF.
    assert(Hjp: join_point pc f).
    apply fn_phicode_inv.
    congruence.
    apply no_successive_jp with (f := f) (pc := pc) (pc' := pc').
    auto. auto.
    apply fn_phicode_inv. congruence.
    auto.
  + assert (use_parcopycode f src pc).
    go.
    induction WF.
    assert (~ assigned_parcopy_spec (fn_parcopycode f) pc src).
    go. congruence.
Qed.

Lemma parcb_src_live :
  forall f pc pc' phib parcb src r,
  wf_cssa_function f ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_parcopycode f) ! pc = Some parcb ->
  In (Iparcopy src r) parcb ->
  cssalive_spec f src pc.
Proof.
    constructor; go.
    unfold not; intros Hdef.
    inv Hdef.
    + assert((fn_parcopycode f) ! (fn_entrypoint f) = None).
      eapply fn_no_parcb_at_entry; eauto. 
      congruence.
    + inv H4; go. 
    + inv H4; go.
      assert(In pc ((get_preds f) !!! pc' )).
      apply make_predecessors_correct_1
        with (instr := Inop pc'); go.
      assert((fn_phicode f) ! pc = None).
      apply fn_normalized_jp with (pc := pc')
        (preds := (get_preds f) !!! pc'); go.
      unfold successors_list in *. flatten.
      inv H4. go.
    + contradict H4.
      apply fn_strict_use_parcb; auto.
      go.
Qed.

Ltac eqregreprs regrepr0 regrepr :=
    assert(EQREGREPRS: regrepr0 = regrepr) by congruence;
    rewrite EQREGREPRS in *.

(* Simulation of parcopyblock in predecessor of joinpoint *)
Lemma simul_parcb :
  forall r f parcb' phib parcb
    rs rs' regrepr pc pc' d,
  wf_cssa_function f ->
  wf_cssa_liverange f ->
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  match_regset f pc rs rs' ->
  def f r d ->
  (cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/ assigned_parcopy_spec (fn_parcopycode f) pc r ->
  (parcopy_store parcb rs) !!2 r =
    (parcopy_store (transl_parcb regrepr parcb) rs')
      !!2 (regrepr r).
Proof.
  intros until d.
  intros WF Hwfcssalive Regrepr Hphib Hinop
    Hparcb Hparcb' MR HDEF H.
  destruct H.
  + destruct H.
    rewrite parcb_other; go.
    assert (Hlive: cssalive_spec f r pc).
    {
      constructor 2 with (pc' := pc'); go.
      unfold not; intros.
      inv H1; auto.
      induction WF; go.
      inv H2; congruence.
      inv H2.
      induction WF.
      destruct H3 as [args HIn].
      assert(join_point pc f).
      apply fn_phicode_inv; congruence.
      assert(join_point pc' f).
      apply fn_phicode_inv; congruence.
      apply no_successive_jp
        with (f := f) (pc := pc) (pc' := pc'); eauto.
      constructor; eauto.
    }
    assert(Hdotranslparcb:
      (parcopy_store (transl_parcb regrepr parcb) rs')
        !!2 (regrepr r)
      = rs' !!2 (regrepr r)).
    {
      apply parcb_transl_other with (f := f); auto; intros.
      case_eq (p2eq (regrepr r) (regrepr dst));
        auto; intros.
      rewrite <- e in *. right.
      exploit compute_regrepr_correct; eauto.
      assert(assigned_parcopy_spec (fn_parcopycode f) pc dst) by go.
      go.
      { exists pc. go. }
      intros Hninterf.
      inv Hninterf.
      assert (Hdefdst: def f dst pc) by go.
      assert (Eq: d2 = pc).
      eapply def_def_eq; eauto.
      rewrite Eq in *.
      assert (cssaliveout_spec f r pc).
      apply correspondance_outin with pc'; go.
      congruence.
    }
    rewrite Hdotranslparcb.
    inv MR; go.
    eqregreprs regrepr0 regrepr.
    apply H1.
    left. split.
    go.
    eapply not_lazydef_in_pred; eauto.
    (* not assigned *)
    intros.
    unfold not in *; intros.
    apply H0; go.
  + inv H.
    assert (Heqparcbs: parcb0 = parcb).
    congruence. rewrite Heqparcbs in *.
    destruct H1 as [src Hin].
    rewrite parcb_store_in with (src := src); eauto.
    rewrite parcb_transl_store_in with (f := f) (src := src); eauto.
    inv MR.
    eqregreprs regrepr0 regrepr.
    apply H.
    assert (Hnotlivesrc: cssalive_spec f src pc).
    constructor; go.
    eapply not_use_and_def_in_jppred; eauto.
    left; split; go.
    eapply not_lazydef_in_pred; eauto.
    eapply nodup_in_parcb_dst; eauto.
    {
      intros.
      case_eq (p2eq (regrepr r) (regrepr dst));
        auto; intros.
      right.
      case_eq(p2eq r dst); intros.
      rewrite e in *.
      {
        induction WF. 
        induction fn_cssa.
        destruct H0 as [Hnodupphib Hnodupparcb].
        specialize (Hnodupparcb pc parcb).
        exploit Hnodupparcb; eauto.
        intros.
        destruct H0 as [Hnodup Heqsrcs].
        replace src with src'; auto.
        go.
      }
      exploit compute_regrepr_correct; eauto.
      { exists pc. go. }
      intros Hninterf.
      inv Hninterf.
      assert (Hdefdst: def f dst pc) by go.
      assert (Eq: d2 = pc).
      eapply def_def_eq; eauto.
      assert (Eq2: d1 = pc).
      eapply def_def_eq; eauto.
      go.
      congruence.
    }
    eapply nodup_in_parcb_dst; eauto.
Qed.

Lemma In_transl_parcb_exists_parcinparcb :
  forall parcb regrepr src dst,
  In (Iparcopy src dst) (transl_parcb regrepr parcb) ->
  exists src' arg',
  In (Iparcopy src' arg') parcb /\ regrepr arg' = dst.
Proof.
  induction parcb; intros; simpl in *.
  + contradiction.
  + flatten H.
    destruct H.
    exists r. exists r0. intuition congruence.
    exploit (IHparcb regrepr src dst); eauto.
    intros Hin.
    destruct Hin as [src' Hin].
    destruct Hin as [arg' Hin].
    intuition eauto.
Qed.

Lemma in_successors_if_succofpred :
  forall f pc l n i,
  (fn_code f) ! n = Some i ->
  (make_predecessors (fn_code f) successors_instr) 
    ! pc = Some l ->
  In n l ->
  In pc ((successors f) !!! n).
Proof.
  intros.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map.
  rewrite H.
  apply make_predecessors_correct2
    with (code := (fn_code f)) (n0 := n).
  auto.
  assert((make_predecessors (fn_code f) successors_instr)
    !!! pc = l).
  unfold successors_list. flatten.
  unfold make_preds.
  rewrite H2. auto.
Qed.

Lemma nth_error_ifnodups :
  forall l k k' (pc pc' : node),
  nth_error l k = Some pc ->
  nth_error l k' = Some pc' ->
  NoDup l ->
  k <> k' ->
  pc <> pc'.
Proof.
  induction l; intros.
  + destruct k; simpl in *; unfold error in *. congruence. congruence.
  + destruct k; destruct k'; simpl in *; unfold error in *;
      unfold value in *; simpl in *. congruence.
    - unfold not; intros Heq.
      rewrite Heq in *.
      assert(In pc' l).
      eapply nth_error_some_in; eauto.
      inv H1. congruence.
    - unfold not; intros Heq.
      rewrite Heq in *.
      assert(In pc' l).
      eapply nth_error_some_in; eauto.
      inv H1; congruence.
    - inv H1; go.
Qed.

Lemma liveinout_jp :
  forall f pc r,
  wf_cssa_function f ->
  join_point pc f ->
  cssalive_spec f r pc ->
  cssaliveout_spec f r pc.
Proof.
  intros f pc r WF Hjp Hlive.
  assert (exists succ, (fn_code f) ! pc = Some (Inop succ)).
  {
    induction WF. apply fn_inop_in_jp.
    rewrite fn_phicode_inv in Hjp. auto.
  }
  destruct H as [succ Hinop].
  inv Hlive.
  inv H0.
  + inv H1; go.
  + assert(join_point succ f).
    inv H1.
    assert(is_edge f pc pc0).
    eapply pred_is_edge_help; eauto.
    inv H0.
    assert(EQ: instr = Inop succ) by congruence.
    rewrite EQ in *.
    simpl in *.
    destruct H2; try contradiction.
    rewrite <- H0 in *.
    induction WF; apply fn_phicode_inv; congruence.
    induction WF; intuition.
  + induction WF.
    intuition.
  + eapply correspondance_outin; eauto.
  + eapply correspondance_outin; eauto.
Qed.


(* Simulation of parcopyblock and phiblock *)
Lemma simul_parcbphib :
  forall r f parcb' phib k parcb
    rs rs' regrepr pc pc' d,
  wf_cssa_function f ->
  wf_cssa_liverange f ->
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  index_pred (get_preds f) pc pc' = Some k ->
  (cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r /\
      ~ assigned_phi_spec (fn_phicode f) pc' r)
    \/ assigned_parcopy_spec (fn_parcopycode f) pc r
    \/ assigned_phi_spec (fn_phicode f) pc' r ->
  match_regset f pc rs rs' ->
  def f r d ->
  (phi_store k phib
    (parcopy_store parcb rs)) !!2 r =
  (parcopy_store (transl_parcb regrepr parcb) rs') !!2 (regrepr r).
Proof.
  intros until d.
  intros WF Hcssalive Hregrepr Hphib Hinop Hparcb Hparcb' Hindex
    Hprops MR Hdef.
  case_eq (In_dst_phib r phib);
    intros.
  + (* r in phib *)
    exploit In_dst_phib_true; eauto; intros.
    destruct H0 as [args Hin].
    assert (Harg: exists arg, nth_error args k = Some arg).
    eapply fn_phiargs; eauto.
    destruct Harg as [arg Hnth].
    assert (regrepr arg = regrepr r).
    { eapply compute_regrepr_init; eauto.  }
    rewrite <- H0. 
    erewrite phi_store_in; eauto.
    assert(USE: use f arg pc) by go.
    exploit exists_def; eauto; intros DEF;
      destruct DEF as [argdef DEF].
    case_eq(peq argdef pc); intros.
    rewrite e in *.
    eapply simul_parcb; eauto.
    {
      induction WF. right; auto.
      inv DEF; go.
      inv H2; go.
      inv H2.
      exfalso.
      eapply no_successive_jp; eauto. go.
      apply fn_phicode_inv; go.
      apply fn_phicode_inv; go.
    }
    assert(Hdom: dom f argdef pc).
    { induction WF. eapply fn_strict; eauto. }
    assert(Hsdom: sdom f argdef pc).
    constructor; auto.
    assert(Hnotin: forall src,
      ~ In (Iparcopy src (regrepr arg)) (transl_parcb regrepr parcb)).
    {
      intros. unfold not; intros.
      assert(Hexists: exists src' arg',
        In (Iparcopy src' arg') parcb /\
        regrepr arg' = regrepr arg).
      eapply In_transl_parcb_exists_parcinparcb; eauto.
      destruct Hexists as [src' Hexists].
      destruct Hexists as [arg' Hineq].
      destruct Hineq as [Hinparcb Heq].
      assert(Hdefarg': def f arg' pc) by go.
      assert(Hneq: arg' <> arg).
      {
        unfold not; intros Heqargs. rewrite Heqargs in *.
        assert(def f arg pc). go.
        assert(argdef = pc) by (eapply def_def_eq; eauto).
        congruence.
      }
      assert(Hinargs: In arg' args).
      {
        assert(Hinrargs: In arg' (r :: args)).
        eapply compute_regrepr_if_eq; go.
        assert(Hneqarg'r: arg' <> r).
        unfold not; intros Heqarg'r.
        rewrite Heqarg'r in *.
        assert(assigned_parcopy_spec (fn_parcopycode f) pc r).
        go.
        assert(assigned_phi_spec (fn_phicode f) pc' r).
        go.
        induction WF. induction fn_cssa.
        specialize (H r pc pc').
        intuition congruence.
        inv Hinrargs; go.
      }
      exploit (in_nth_error_some reg args arg'); eauto.
      intros Hexistsk.
      destruct Hexistsk as [k0 Hnthk0].
      assert(Hneqks: k <> k0). congruence.
      assert(Hexistspred:
        exists pred, nth_error ((get_preds f) !!! pc') k0 = Some pred).
      {
         induction WF. 
         unfold block_nb_args in fn_wf_block.
         exploit fn_wf_block; eauto. 
         intros.
         eapply nth_error_some_same_length; eauto.
      }
      destruct Hexistspred as [pred Hnthpred].
      assert(Hneqpreds: pred <> pc).
      {
        assert(NoDup (pc' :: (get_preds f) !!! pc')).
        eapply nodups_in_preds; eauto. go.
        
        assert(HInpreds: In pc (get_preds f) !!! pc').
        apply make_predecessors_correct_1
          with (instr := Inop pc'); go.
        unfold successors_list.
        flatten; go. unfold successors_list in HInpreds.
        flatten HInpreds; go.
        unfold not; intros Hinpc'.
        assert(Hjp: join_point pc' f).
        { apply fn_phicode_inv; go. }
        apply no_successive_jp
          with (f := f) (pc := pc') (pc' := pc'); eauto.
        {
          induction WF.
          exploit (fn_inop_in_jp pc'); eauto. go.
          intros Hexists.
          destruct Hexists as [succ Hinopsucc].
          exploit in_successors_if_succofpred; eauto.
          unfold successors_list.
          flatten; go. unfold successors_list in Hinpc'.
          flatten Hinpc'; go.
        }
        unfold not; intros Heqpredpc.
        rewrite Heqpredpc in *.
        exploit index_pred_some_nth; eauto.
        intros Hnthkpc.
        assert(pc <> pc).
        apply nth_error_ifnodups
          with (l := (get_preds f) !!! pc')
          (k := k) (k' := k0); eauto.
        inv H3; go.
        go.
      }
      assert(Huse: use f arg' pred).
      assert(Husephi: use_phicode f arg' pred).
      apply upc_intro
        with (pc := pc') (k := k0) (args := args)
        (dst := r) (phib := phib); go.
      eapply CSSApargenproof.index_pred_from_nth; eauto.
      eapply nodups_in_preds with (f := f)
        (preds := get_preds f); go.
      {
        unfold successors_list.
        flatten; go.
        exploit nth_error_some_in; eauto.
        intros. unfold successors_list in H3.
        flatten H3. inv H3.
      }
      {
        unfold not; intros Hin'.
        unfold successors_list in Hin'.
        flatten Hin'; go.
        assert(Hjp: join_point pc' f).
        eapply fn_phicode_inv; congruence.
        induction WF.
        exploit (fn_inop_in_jp pc'); go.
        intros Hinopsucc.
        destruct Hinop as [succ Hinopsucc].
        unfold node in *.
        exploit fn_normalized_jp; go.
        go. go.
      }
      {
        unfold successors_list.
        flatten; go.
        exploit nth_error_some_in; eauto.
        intros. unfold successors_list in H3.
        flatten H3. inv H3.
      }
      constructor 2; go.
      assert(Hlive: cssalive_spec f arg' pred).
      {
        constructor.
        unfold not; intros Hdefarg'pred.
        assert(pred = pc).
        eapply def_def_eq; eauto. congruence.
        go.
      }
      assert(Hdompcpred: dom f pc pred).
      { induction WF.
        eapply fn_strict; eauto. }
      inv Hdompcpred. congruence.
      assert(Hpath: exists p,
        CSSApath f (PState (entry f)) p (PState pred)).
      eapply reached_path; eauto.
      destruct Hpath as [p Hpath].
      assert(Hpath': exists p',
        CSSApath f (PState pc) (pc :: p') (PState pred)
        /\ ~ In pc p').
      eapply shorten_path; eauto.
      destruct Hpath' as [p' Hpath'].
      destruct Hpath' as [Hpath' Hnotin].
      inv Hpath'. 
      destruct s2.
      - inv STEP. inv STEP0.
        rewrite Hinop in HCFG_ins.
        assert(Hins: ins = Inop pc') by congruence.
        rewrite Hins in *.
        simpl in *.
        destruct HCFG_in; auto.
        rewrite H4 in *.
        exploit cssalive_path_to_def; eauto.
        intros Hlivepc0.
        assert(Hliveout: cssaliveout_spec f arg' pc0).
        eapply liveinout_jp; eauto. apply fn_phicode_inv; go.
        unfold wf_cssa_liverange in Hcssalive.
        assert(Hninterlive: r = arg' \/ ninterlive_spec f r arg').
        apply Hcssalive with (pc := pc0)
          (resources := r :: args); eauto.
        go.
        destruct Hninterlive.
        + rewrite H5 in *.
          assert(Heqpcs: pc = pc0).
          eapply def_def_eq; eauto.
          rewrite Heqpcs in *.
          eapply no_successive_jp; eauto;
          apply fn_phicode_inv; go.
        + inv H5.
          assert(Heqpcs: d1 = pc0).
          eapply def_def_eq; eauto.
          rewrite Heqpcs in *.
          congruence.
      - inv STEP. unfold exit in NOSTEP. flatten NOSTEP.
    }
    rewrite parcb_other.
    rewrite parcb_other.
    inv MR.
    eqregreprs regrepr0 regrepr.
    eapply H2; go.
    left. split; auto.
    constructor; go. unfold not; intros.
    assert(pc = argdef).
    eapply def_def_eq; eauto. congruence.
    unfold not; intros.
    assert(def f arg pc).
    inv H3; go.
    assert(pc = argdef).
    eapply def_def_eq; eauto. congruence.
    intros.
    unfold not; intros Heq.
    rewrite Heq in Hnotin. specialize (Hnotin src). auto.
    intros.
    unfold not; intros.
    assert(def f arg pc).
    go.
    assert(pc = argdef).
    eapply def_def_eq; eauto. congruence.
  + (* r not in phib *)
    assert (Hnotin: forall args, ~ In (Iphi args r) phib).
    apply In_dst_phib_false; auto.
    rewrite <- phi_store_other.
    eapply simul_parcb; go.
    destruct Hprops as [Hprops | Hprops].
    left. destruct Hprops as [MR1 [MR2 MR3]]. split; go.
    right. destruct Hprops. auto.
    inv H0. destruct H2 as [args Hin].
    assert(EQ: phiinstr = phib) by congruence.
    rewrite EQ in *.
    assert(Hnotinphib: ~ In (Iphi args r) phib).
    apply In_dst_phib_false; auto.
    congruence.
    intros. unfold not; intros.
    assert (~ In (Iphi args dst) phib).
    rewrite H1 in *. apply Hnotin.
    auto.
Qed.

Lemma invariant_props_used_in_parcb' :
  forall f pc pc' phib parcb' src r,
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  In (Iparcopy src r) parcb' -> 
  cssalive_spec f src pc' /\
  ~ assigned_parcopy_spec (fn_parcopycode f) pc src /\
  ~ assigned_phi_spec (fn_phicode f) pc' src \/
  assigned_parcopy_spec (fn_parcopycode f) pc src \/
  assigned_phi_spec (fn_phicode f) pc' src.
Proof.
  intros until r.
  intros WF Hinop Hphib Hparcb' Hin.
  assert(Hphi: assigned_phi_spec (fn_phicode f) pc' src
    \/ ~ assigned_phi_spec (fn_phicode f) pc' src).
  apply classic.
  destruct Hphi. tauto.
  assert(Hparc: assigned_parcopy_spec (fn_parcopycode f) pc src
    \/ ~ assigned_parcopy_spec (fn_parcopycode f) pc src).
  apply classic.
  destruct Hparc. tauto.
  left. split; auto.
  constructor.
  {
    unfold not; intros.
    inv H1; go.
    + assert(Hcfg: cfg f pc (fn_entrypoint f)) by go.
      go. induction WF. contradict Hcfg. apply fn_entry_pred.
    + induction WF.
      exploit (fn_inop_in_jp pc'); go.
      intros Hinoppc'.
      destruct Hinoppc' as [succ Hinoppc'].
      inv H2; go.
    + induction WF.
      contradict H2.
      apply fn_strict_use_parcb. go.
  }
  go.
Qed.

Ltac do_not_jp_pred pc_2 pc'_2 :=
    eapply no_successive_jp with (pc := pc_2) (pc' := pc'_2); eauto;
      rewrite fn_phicode_inv; try congruence.

(* Simulation of chain parcb-phib-parcb' *)
Lemma simul_parcbphibparcb' :
  forall r f parcb' phib k parcb
    rs rs' regrepr pc pc' d,
  wf_cssa_function f ->
  wf_cssa_liverange f ->
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  index_pred (get_preds f) pc pc' = Some k ->
  match_regset f pc rs rs' ->
  ((cssalive_spec f r pc' /\ ~ lazydef f r pc'
      /\ ~ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/
    (cssalive_spec f r pc' /\ ~ lazydef f r pc'
      /\ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/ lazydef f r pc') ->
  def f r d ->
  (parcopy_store parcb'
    (phi_store k phib
      (parcopy_store parcb rs)))
  !!2 r =
  (parcopy_store (transl_parcb regrepr parcb')
    (parcopy_store (transl_parcb regrepr parcb)
      rs'))
  !!2 (regrepr r).
Proof.
  intros until d.
  intros WF Hwfcssalive Hregrepr Hphib Hinop Hparcb Hparcb' Hindex
    MR Hprops Hdef.
  case_eq (In_dst_parcb r parcb');
    intros.
  + (* r is in parcb' *)
    exploit In_dst_parcb_true; eauto; intros.
    destruct H0 as [src Hin].
    assert(USE: use f src pc') by go.
    exploit exists_def; eauto; intros DEF;
      destruct DEF as [srcdef DEF].
    rewrite parcb_store_in with (src := src); eauto.
    rewrite parcb_transl_store_in with (f := f) (src := src); eauto.
    eapply simul_parcbphib; go.
    eapply invariant_props_used_in_parcb'; eauto.
    eapply nodup_in_parcb_dst; eauto.
    {
      intros.
      assert(USE': use f src' pc') by go.
      exploit exists_def; eauto; intros DEF';
      destruct DEF' as [src'def DEF'].
      case_eq (p2eq (regrepr r) (regrepr dst)); auto; intros.
      right.
      case_eq(p2eq r dst); intros.
      rewrite e in *.
      {
        induction WF. 
        induction fn_cssa.
        destruct H0 as [Hnodupphib Hnodupparcb].
        specialize (Hnodupparcb pc' parcb').
        exploit Hnodupparcb; eauto.
        intros.
        destruct H0 as [Hnodup Heqsrcs].
        replace src with src'; auto.
        go.
      }
      exploit compute_regrepr_correct; go.
      intros Hninterf.
      inv Hninterf.
      assert (Eq: d2 = pc').
      eapply def_def_eq; go.
      assert (Eq2: d1 = pc').
      eapply def_def_eq; go.
      congruence.
    }
    eapply nodup_in_parcb_dst; eauto.
  + (* r is not in parcb' *)
    assert (Hnotin: forall src, ~ In (Iparcopy src r) parcb').
    apply In_dst_parcb_false; auto.
    assert(Hassigned_r:
      cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc' r /\
      ~ assigned_phi_spec (fn_phicode f) pc' r \/
      assigned_parcopy_spec (fn_parcopycode f) pc r \/
      assigned_phi_spec (fn_phicode f) pc' r).
    {
        decompose [or] Hprops.
        decompose [and] H0.
        left. repeat split; go.
        unfold not; intros. assert (lazydef f r pc').
        constructor 2; auto. rewrite fn_phicode_inv; go. contradiction.
        unfold not; intros. assert (lazydef f r pc').
        go. congruence.
        decompose [and] H1.
        right. left. auto.
        assert (~ assigned_parcopy_spec (fn_parcopycode f) pc' r).
        unfold not; intros.
        inv H0. destruct H3.
        replace parcb0 with parcb' in *.
        assert (~ In (Iparcopy x r) parcb').
        apply In_dst_parcb_false; auto. congruence. go.
        right. right.
        inv H1; go.
    }
    case_eq (In_dst_parcb (regrepr r)
      (transl_parcb regrepr parcb'));
      intros.
    - (* [regrepr r] in transl(parcb') *)
      assert (Hintransl: exists src, In (Iparcopy src (regrepr r)) 
        (transl_parcb regrepr parcb')).
      apply In_dst_parcb_true; auto.
      destruct Hintransl as [src Hintransl].
      rewrite parcb_transl_other with (f := f); go.
      rewrite parcb_other; go.
      eapply simul_parcbphib; eauto.
        tauto.
      unfold not in *; intros.
      eapply Hnotin; go.
      {
        intros.
        assert(USE0: use f src0 pc') by go.
        exploit exists_def; eauto; intros DEF0;
        destruct DEF0 as [src0def DEF0].
        case_eq (p2eq (regrepr r) (regrepr dst)); auto; intros.
        right.
        exploit compute_regrepr_correct; go.
        assert(Hnotinparcb': forall src, ~ In (Iparcopy src r) parcb').
        eapply In_dst_parcb_false; eauto.
        specialize (Hnotinparcb' src0).
        unfold not; intros. go.
        intros Hninterf.
        inv Hninterf.
        assert(Hdefdst: def f dst pc'). constructor 4; go.
        assert(EQ: d2 = pc').
        eapply def_def_eq; go.
        rewrite EQ in *.
        assert (cssalive_spec f r pc').
        { 
          decompose [or] Hprops; go.
          decompose [and] H8; go.
          decompose [and] H9; go.
          assert(def f r pc').
          inv H9; go.
          assert(d1 = pc').
          eapply def_def_eq; go. congruence.
        }
        assert (cssaliveout_spec f r pc').
        apply liveinout_jp; auto.
        induction WF. apply fn_phicode_inv. congruence.
        congruence.
      }
    - (* [regrepr r] not in transl(parcb') *)
      rewrite parcb_other.
      rewrite parcb_other.
      eapply simul_parcbphib; eauto.
      tauto.
      intros.
      assert (Hnotintransl: forall src,
        ~ In (Iparcopy src (regrepr r))
        (transl_parcb regrepr parcb')).
      apply In_dst_parcb_false; auto.
      unfold not in *; intros.
      eapply Hnotintransl; go.
      unfold not in *; intros.
      eapply Hnotin; go.
Qed.

(* Misc lemmas *)
Lemma registers_equal :
  forall args (rs rs' : SSA.regset) regrepr,
  (forall r, In r args ->
    rs !!2 r = rs' !!2 (regrepr r)) ->
  rs ##2 args = rs' ##2 (map regrepr args).
Proof.
  induction args; intros.
  go.
  simpl.
  rewrite <- IHargs with (rs := rs).
  rewrite H. auto. constructor; auto.
  intros. auto.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transl_function f = Errors.OK tf ->
  fn_stacksize f = RTLpar.fn_stacksize tf.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; go.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transl_fundef.
  exact TRANSF_PROG.
Qed.

Lemma function_ptr_translated:
  forall (b: Values.block) (f: CSSApar.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_ptr_transf_partial transl_fundef).
  exact TRANSF_PROG.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
    wf_cssa_fundef f ->
    transl_fundef f = Errors.OK tf ->
    RTLpar.funsig tf = CSSApar.funsig f.
Proof.
  intros f tf. intros.
  case_eq f; intros.
  - rewrite H1 in H0.
    simpl in *. Errors.monadInv H0.
    eapply transl_function_charact in EQ ; eauto.
    simpl in *.
    inv EQ.
    inv H. auto.
    inv H. auto.
  - rewrite H1 in H0. go.
Qed.

Ltac split_but_remember := 
    match goal with
    | [ H: _ |- ?A /\ ?B ] => assert(Hstep: A)
    end.

Lemma predecessors_preserved :
  forall f tf,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  make_predecessors (RTLpar.fn_code tf) successors_instr
    = make_predecessors (fn_code f) successors_instr.
Proof.
    intros.
    exploit transl_function_correct; eauto.
    apply transl_function_charact; eauto. intros SPEC.
    inv SPEC.
    eapply same_successors_same_predecessors; eauto.
    intros.
    repeat rewrite PTree.gmap1.
    unfold option_map; flatten.
    assert((RTLpar.fn_code tf) ! i
      = Some (transl_instruction regrepr i1)).
    auto.
    assert (RW: i0 = transl_instruction regrepr i1)
      by congruence.
    rewrite RW.
    destruct i1; simpl; flatten; auto.
    assert((RTLpar.fn_code tf) ! i = None).
    apply codeNone; auto.
    congruence.
    assert((RTLpar.fn_code tf) ! i =
      Some (transl_instruction regrepr i0)).
    auto.
    congruence.
Qed.

Lemma jp_preserved_1 :
  forall f tf jp,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  join_point jp f ->
  RTLpar.join_point jp tf.
Proof.
  intros. 
  inv H1.
  apply RTLpar.jp_cons with (l := l).
  exploit transl_function_correct; eauto.
  apply transl_function_charact; eauto. intros SPEC.
  inv SPEC.
  exploit predecessors_preserved; eauto.
  go. auto.
Qed.

Lemma jp_preserved_2 :
  forall f tf jp,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  RTLpar.join_point jp tf ->
  join_point jp f.
Proof.
  intros.
  inv H1.
  apply jp_cons with (l := l).
  exploit transl_function_correct; eauto.
  apply transl_function_charact; eauto. intros SPEC.
  inv SPEC.
  exploit predecessors_preserved; eauto.
  go. auto.
Qed.

Lemma lazydef_spec :
  forall f pc r,
  lazydef f r pc \/ ~ lazydef f r pc.
Proof.
  intros.
  apply classic.
Qed.

Lemma live_implies_use :
  forall f pc r,
  wf_cssa_function f ->
  cssalive_spec f r pc ->
  exists pc', use f r pc'.
Proof.
  intros f pc r WF Hlive.
  induction Hlive; go.
Qed.

Lemma not_parcb_def_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ assigned_parcopy_spec (fn_parcopycode f) pc r.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hassign.
  inv Hassign.
  assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
  eapply parcb_inop; eauto. go.
  destruct Hinop; congruence.
Qed.

Lemma not_phi_def_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ assigned_phi_spec (fn_phicode f) pc r.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hassign.
  inv Hassign.
  assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
  eapply fn_inop_in_jp; go.
  destruct Hinop; go.
Qed.

Lemma not_lazydef_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ lazydef f r pc.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hlazy.
  inv Hlazy.
  + contradict H.
    apply not_phi_def_outside_inop; go.
  + contradict H.
    apply not_parcb_def_outside_inop; go.
Qed.

Lemma not_lazydef_outside_jp :
  forall f pc r,
  wf_cssa_function f ->
  ~ join_point pc f ->
  ~ lazydef f r pc.
Proof.
  intros f pc r WF Hnojp.
  unfold not; intros Hlazy.
  inv Hlazy; auto.
  inv H.
  induction WF.
  rewrite fn_phicode_inv in Hnojp.
  intuition congruence.
Qed.

Lemma use_usecode_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  use_code f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  inv Huse.
  + auto.
  + inv H.
    assert((fn_code f) ! pc = Some (Inop pc0)).
    apply fn_normalized; go.
    apply fn_phicode_inv; go.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    assert(Hedge: cfg f pc pc0).
    {
      exploit pred_is_edge_help; go.
      intros. inv H. go.
    }
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go. go.
  + inv H.
    assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
    eapply parcb_inop; eauto. go.
    destruct Hinop. congruence.
Qed.

Lemma not_lazydef_after_noinop :
  forall f pc pc' r,
  wf_cssa_function f ->
  cfg f pc pc' ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ lazydef f r pc'.
Proof.
  intros f pc pc' r WF Hedge Hnotinop.
  unfold not; intros Hlazy.
  inv Hlazy.
  + inv H.
    assert(Hinop: (fn_code f) ! pc = Some (Inop pc')).
    induction WF.
    apply fn_normalized.
    apply fn_phicode_inv. congruence.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go.  go.
  + assert(Hinop: (fn_code f) ! pc = Some (Inop pc')).
    apply fn_normalized; go.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go. go.
Qed.

Lemma live_in_pred_if_notdefined :
  forall f r pc pc',
  wf_cssa_function f ->
  ~ def f r pc ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  cfg f pc pc' ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  cssalive_spec f r pc.
Proof.
  intros f r pc pc' WF Hnotdef Hnotinop Hedge Hprops.
  destruct Hprops as [Hlive | Hlazy].
  + constructor 2 with (pc' := pc').
    go.
    unfold not; intros Hdef.
    inv Hdef; go.
    tauto.
  + contradict Hlazy.
    eapply not_lazydef_after_noinop; go.
Qed.

Lemma live_at_notinop_if_used :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  cssalive_spec f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  constructor.
  unfold not; intros Hdef.
  inv Hdef.
  + induction WF.
    destruct fn_entry; go.
  + assert(Husecode: use_code f r pc).
    apply use_usecode_outside_inop; auto.
    eapply fn_use_def_code; eauto.
  + contradict H.
    apply not_phi_def_outside_inop; go.
  + contradict H.
    apply not_parcb_def_outside_inop; go.
  + auto.
Qed.

Lemma not_usedanddef_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  ~ def f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  unfold not; intros.
  inv H.
  + assert(Hinop: exists s,
      (fn_code f) ! (fn_entrypoint f) = Some (Inop s)).
    induction WF.
    apply fn_entry. destruct Hinop; congruence.
  + assert(Husecode: use_code f r pc).
    apply use_usecode_outside_inop; auto.
    eapply fn_use_def_code; eauto.
  + contradict H0.
    apply not_phi_def_outside_inop; go.
  + contradict H0.
    apply not_parcb_def_outside_inop; go.
Qed.

Lemma absurd_notinop_at_entry :
  forall f,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! (fn_entrypoint f) <> Some (Inop s)) ->
  False.
Proof.
  intros.
  assert(Hinop:
    exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s)).
  induction H; go.
  destruct Hinop; go.
Qed.

Lemma ninterlive_outside_inop :
  forall f r dst pc pc',
  wf_cssa_function f ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  ninterlive_spec f r dst ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  def f dst pc ->
  cfg f pc pc' ->
  r <> dst ->
  False.
Proof.
  intros until pc'.
  intros WF Hprops Hninterlive Hnotinop Hdefdst Hedge Hneq.
  inv Hninterlive.
  assert(EQ: d2 = pc).
  eapply def_def_eq; eauto.
  rewrite EQ in *.
  assert(cssalive_spec f r pc').
  {
    destruct Hprops as [Hlive | Hlazy].
    destruct Hlive. auto.
    contradict Hlazy.
    apply not_lazydef_after_noinop with (pc := pc); go.
  }
  assert(cssaliveout_spec f r pc).
  eapply correspondance_outin; eauto. go.
Qed.

Lemma live_props_outside_inop :
  forall f r pc' pc,
  wf_cssa_function f ->
  cfg f pc pc' ->
  ~ assigned_code_spec (fn_code f) pc r ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  cssalive_spec f r pc.
Proof.
  intros until pc.
  intros WF Hedge Hnotassign Hprops Hnotinop.
  apply live_in_pred_if_notdefined with (pc' := pc'); go.
  destruct Hprops as [Hlive | Hlazy].
  - unfold not; intros Hdef.
    inv Hdef; go.
    apply absurd_notinop_at_entry with (f := f); go.
    contradict H.
    apply not_phi_def_outside_inop; go.
    contradict H.
    apply not_parcb_def_outside_inop; go.
  - contradict Hlazy.
    eapply not_lazydef_after_noinop; go.
Qed.

Lemma functions_translated:
  forall (v: val) (f: CSSApar.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  apply (Genv.find_funct_transf_partial transl_fundef).
  exact TRANSF_PROG.
Qed.

Lemma spec_ros_r_find_function:
  forall rs rs' f r regrepr,
  rs #2 r = rs' #2 (regrepr r) ->
  CSSApar.find_function ge (inl _ r) rs = Some f ->
  exists tf,
    RTLpar.find_function tge (inl _ (regrepr r)) rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  eapply functions_translated; eauto. inv H0.
  rewrite <- H; auto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs rs' f id,
  CSSApar.find_function ge (inr _ id) rs = Some f ->
  exists tf,
     RTLpar.find_function tge (inr _ id) rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  simpl in *.
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma match_regset_args :
  forall args regrepr rs (rs' : SSA.regset),
  (forall r, In r args ->
    rs #2 r = rs' #2 (regrepr r)) ->
  rs ##2 args = rs' ##2 (map regrepr args).
Proof.
  induction args; go.
  intros.
  simpl.
  erewrite IHargs; eauto.
  rewrite H. auto. auto.
Qed.

Lemma not_used_at_entry :
  forall f r,
  wf_cssa_function f ->
  ~ use f r (fn_entrypoint f).
Proof.
  intros; unfold not; intros.
  inv H0.
  + exploit fn_entry; eauto; intros.
    destruct H0.
    inv H1; go.
  + inv H1.
    assert(HInpreds: In (fn_entrypoint f) (get_preds f) !!! pc).
    apply make_predecessors_correct_1
      with (instr := Inop pc).
    exploit fn_entry; eauto. intros.
    exploit pred_is_edge_help; eauto; intros.
    exploit is_edge_insuccs; eauto; intros.
    destruct H0. destruct H2. destruct H2.
    unfold successors in H2.
    rewrite PTree.gmap1 in H2.
    unfold option_map in H2.
    rewrite H0 in H2. simpl in H2.
    assert(EQ: x0 = x :: nil) by congruence.
    rewrite EQ in *.
    inv H3; auto. contradiction.
    simpl; auto.
    eapply parcbSome; eauto.
    eapply fn_no_parcb_at_entry; eauto.
  + inv H1.
    assert((fn_parcopycode f) ! (fn_entrypoint f) = None).
    eapply fn_no_parcb_at_entry; eauto.
    congruence.
Qed.

Lemma no_jp_after_entry :
  forall f pc,
  wf_cssa_function f ->
  (fn_phicode f) ! pc <> None ->
  cfg f (fn_entrypoint f) pc ->
  False.
Proof.
  intros f pc WF Hphibnotnone Hcfg.
  assert(HInpreds: In (fn_entrypoint f) (get_preds f) !!! pc).
  invh cfg; go.
  { apply make_predecessors_correct_1
      with (instr := Inop pc).
    exploit fn_entry; eauto. intros.
    destruct H.
    rewrite H in HCFG_ins.
    assert(Hins: Inop x = ins) by congruence.
    rewrite <- Hins in HCFG_in.
    simpl in *. destruct HCFG_in; try congruence. contradiction.
    simpl; auto. }
  case_eq ((fn_phicode f) ! pc); intros; try congruence.
  exploit parcbSome; eauto.
  eapply fn_no_parcb_at_entry; eauto.
Qed.

Lemma live_at_entry_def_aux:
  forall f r pc',
  wf_cssa_function f ->
  cfg f (fn_entrypoint f) pc' ->
  cssalive_spec f r pc' ->
  def f r (fn_entrypoint f).
Proof.
  intros f r pc' WF Hcfg Hlive.
  exploit CSSAlive.live_cssadom; eauto.
  constructor. auto.
  intros.
  destruct H; auto.
  + inv H.
    - inv H1.
      inv DOM; try congruence.
      specialize (PATH (fn_entrypoint f :: nil)).
      exploit PATH.
      go. intros Hin. inv Hin; try congruence. contradiction.
    - exfalso. eapply no_jp_after_entry; eauto.
      inv H0; congruence.
    - exfalso. eapply no_jp_after_entry; eauto.
      rewrite fn_phicode_inv in H1; auto.
  + rewrite H in *.
    contradict Hcfg.
    apply fn_entry_pred; auto.
Qed.

Lemma live_at_entry_def :
  forall f r,
  wf_cssa_function f ->
  cssalive_spec f r (fn_entrypoint f) ->
  def f r (fn_entrypoint f).
Proof.
  intros.
  induction H0.
  + contradict H1.
    apply not_used_at_entry; auto.
  + eapply live_at_entry_def_aux; eauto.
  + eapply live_at_entry_def_aux; eauto.
Qed.

Lemma init_regs_match :
  forall params f r d args regrepr,
  wf_cssa_function f ->
  wf_cssa_liverange f ->
  cssalive_spec f r (fn_entrypoint f) ->
  (forall r', In r' params -> In r' (fn_params f)) ->
  compute_regrepr f = Errors.OK regrepr ->
  def f r d ->
  (init_regs args params) !!2 r =
    (init_regs args (map regrepr params))
      !!2 (regrepr r).
Proof.
  induction params;
  intros until regrepr;
    intros WF Hwfcssalive Hlive Hparams Hregrepr Hdef; simpl.
  rewrite P2Map.gi.
  rewrite P2Map.gi.
  auto.
  flatten; go.
  rewrite P2Map.gi.
  rewrite P2Map.gi.
  auto.
  case_eq (p2eq a r); intros.
  + rewrite e in *. repeat rewrite P2Map.gss. auto.
  + rewrite P2Map.gsspec.
    rewrite P2Map.gsspec.
    flatten; auto.
    exploit compute_regrepr_correct; eauto; intros Hninterf.
    inv Hninterf.
    { assert(Hrdef: def f r (fn_entrypoint f)).
      apply live_at_entry_def; auto.
      assert(Heq: d1 = (fn_entrypoint f)).
      eapply def_def_eq; eauto.
      assert(Hdefa: def f a (fn_entrypoint f)).
      eauto.
      assert(Heq2: d2 = (fn_entrypoint f)).
      eapply def_def_eq; eauto.
      congruence. }
    eauto.
Qed.

Lemma liveorlazydef_exists_def:
  forall f r pc,
  wf_cssa_function f ->
  cssalive_spec f r pc /\ ~ lazydef f r pc \/ lazydef f r pc ->
  exists d, def f r d.
Proof.
  intros f r pc WH Hrprops.
  destruct Hrprops as [Hrprops | Hrprops]; auto.
  destruct Hrprops.
  exploit live_implies_use; eauto; intros Huse.
  destruct Huse as [u Huse].
  exploit exists_def; eauto.
  inv Hrprops; go.
Qed.

Lemma live_exists_def:
  forall f r pc,
  wf_cssa_function f ->
  cssalive_spec f r pc ->
  exists d, def f r d.
Proof.
  intros f r pc WF Hlive.
  exploit live_implies_use; eauto; intros Huse.
  destruct Huse as [u Huse].
  exploit exists_def; eauto.
Qed.

Lemma transl_step_correct:
  forall s1 t s2,
  step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2',
  RTLpar.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS; auto;
  match goal with
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [RTLpar.Returnstate ?ts ?vres ?m]] => idtac
    | _ =>
      (exploit transl_function_charact; eauto; intros;
       exploit transl_function_correct; eauto; intros)
  end;
  match goal with
    | [SPEC: transl_function_spec ?f ?tf |- _ ] =>
      inv SPEC
    | _ => try (generalize (wf_cssa f) ; intros HWF)
  end.
  (* inop without block *)
  { exists (RTLpar.State ts tf sp pc' rs' m). split; auto.
    econstructor 1 ; eauto.
    - replace (Inop pc') with
        (transl_instruction regrepr (Inop pc')); auto.
    - intro Hcont. eelim H0; eauto using jp_preserved_2. 
    - econstructor; eauto.
      econstructor; eauto; intros.
      inv MREG.
      destruct H2.
      destruct H2 as [Hlive Hlazy].
      eqregreprs regrepr0 regrepr.
      apply H3.
      generalize lazydef_spec; intros Hlazyspecg.
      assert(Hlazyspec: lazydef f r pc \/ ~ lazydef f r pc)
        by eauto.
      destruct Hlazyspec. auto. left.
      split; auto.
      case_eq (peq (fn_entrypoint f) pc).
      {
        intros. rewrite e in *.
        constructor 3 with (pc' := pc'); go.
      }
      (* constructor 1. *)
      constructor 2 with (pc' := pc').
      go.
      {
        unfold not; intros Hdef.
        inv Hdef; go.
        inv H5; go.
        assert(lazydef f r pc).
        go. congruence.
        assert(lazydef f r pc).
        constructor 2.
        auto.
        inv H5.
        induction WFF; eauto. (* use of parcbjp *)
        go.
      }
      go.
      inv H2; go.
      induction WFF. rewrite fn_phicode_inv in H0.
      inv H4; go. rewrite H2 in H0.
      assert (Some phiinstr <> None) by congruence.
      assert (~ (Some phiinstr <> None)) by auto.
      contradiction.
  }
  { (* inop with block *)
    exists (RTLpar.State ts tf sp pc'
      (parcopy_store (transl_parcb regrepr parcb')
        (parcopy_store (transl_parcb regrepr parcb) rs')) m).
    split_but_remember.
    {
      apply RTLpar.exec_Inop_jp ; auto.
      replace (Inop pc') with
        (transl_instruction regrepr (Inop pc')); auto.
      {
        eapply jp_preserved_1; eauto. 
      }
    }      
    split; auto.
    econstructor; eauto.
    econstructor; eauto.
    intros r Hrprops.
    exploit liveorlazydef_exists_def; eauto; intros DEF.
    destruct DEF as [d DEF].
    apply simul_parcbphibparcb'
      with (f := f) (pc := pc) (pc' := pc')
        (d := d); eauto.
    tauto.
  }
  { (* Iop *)
    exists (RTLpar.State ts tf sp pc'
      (rs'#2 (regrepr res) <- v) m).
    split_but_remember.
    { 
      apply RTLpar.exec_Iop with (op := op)
        (args := map regrepr args).
      exploit codeSome; go.
      inv MREG.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_operation_preserved; eauto.
      eapply symbols_preserved.
      intros.
      eqregreprs regrepr0 regrepr.
      apply H2.
      (* properties of [r] *)
      left. split; auto.
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    constructor; eauto.
    econstructor; eauto. intros.
    econstructor; eauto. intros.
    rewrite P2Map.gsspec.
    rewrite P2Map.gsspec.
    inv MREG.
    flatten.
    {
      exploit liveorlazydef_exists_def; eauto; intros DEF.
      eqregreprs regrepr0 regrepr.
      exploit compute_regrepr_correct; eauto; intros Hninterf.
      inv Hninterf.
      assert(def f res pc) by go.
      assert(EQ: d2 = pc).
      eapply def_def_eq; eauto.
      rewrite EQ in *.
      exfalso. eapply ninterlive_outside_inop; go.
      go.
    }
    eqregreprs regrepr0 regrepr.
    apply H3. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Iload *)
    exists (RTLpar.State ts tf sp pc'
      (rs' #2 (regrepr dst) <- v) m).
    split_but_remember.
    { 
      apply RTLpar.exec_Iload
        with (chunk := chunk) (addr := addr)
          (args := map regrepr args)
        (a := a).
      rewrite codeSome with (ins := (Iload chunk addr args dst pc'));
        go.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H4.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
      (* memory *)
      go.
    }
    constructor; eauto.
    econstructor; eauto; intros.
    econstructor; eauto; intros.
    rewrite P2Map.gsspec.
    rewrite P2Map.gsspec.
    inv MREG.
    flatten.
    {
      eqregreprs regrepr0 regrepr.
      exploit liveorlazydef_exists_def; eauto; intros DEF.
      exploit compute_regrepr_correct; eauto; intros Hninterf.
      inv Hninterf.
      assert(def f dst pc) by go.
      assert(EQ: d2 = pc).
      eapply def_def_eq; eauto.
      rewrite EQ in *.
      exfalso. eapply ninterlive_outside_inop; go.
      go.
    }
    eqregreprs regrepr0 regrepr.
    apply H4. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Istore *)
    exists (RTLpar.State ts tf sp pc' rs' m').
    split_but_remember.
    { apply RTLpar.exec_Istore with (chunk := chunk)
        (addr := addr)
        (args := map regrepr args)
        (src := regrepr src)
        (a := a).
      rewrite codeSome with
        (ins := (Istore chunk addr args src pc'));
        go.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H4. left.
      (* properties of [r] *)
      split; auto.
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      rewrite <- H3.
      go.
      left. split.
      + constructor.
        unfold not; intros Hdef.
        inv Hdef; go.
        apply absurd_notinop_at_entry with (f := f); go.
        induction WFF.
        inv H4; go.
        contradict H4.
        apply not_phi_def_outside_inop; go.
        contradict H4.
        apply not_parcb_def_outside_inop; go.
        go.
      + apply not_lazydef_outside_inop; go.
    }
    constructor; eauto.
    constructor; eauto.
    econstructor; eauto.
    intros.
    inv MREG.
    eqregreprs regrepr0 regrepr.
    apply H4. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Icall *)
    assert (WFfd: wf_cssa_fundef fd).
    {
      unfold wf_ssa_program in WF_PROG.
      assert (ID: exists id,
        In (id, Gfun fd) (prog_defs prog)).
      unfold find_function in H0.
      unfold Genv.find_funct in H0.
      flatten H0;
        apply Genv.find_funct_ptr_inversion
          with (b := b); auto.
      destruct ID as [id Infd].
      apply WF_PROG with id.
      auto.
    }
    assert (WFlivefd: wf_cssa_liverange_fundef fd).
    {
      unfold wf_cssa_liverange_program in WFlive_PROG.
      assert (ID: exists id,
        In (id, Gfun fd) (prog_defs prog)).
      unfold find_function in H0.
      unfold Genv.find_funct in H0.
      flatten H0;
        apply Genv.find_funct_ptr_inversion
          with (b := b); auto.
      destruct ID as [id Infd].
      apply WFlive_PROG with id.
      auto.
    }
    assert(RW: rs ##2 args = rs' ##2 (map regrepr args)).
    {
      apply match_regset_args.
      intros r Hin.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H2.
      left. split.
      eapply live_at_notinop_if_used; eauto.
      go. apply u_code.
      destruct ros.
      apply UIcall with (sig := (funsig fd))
        (r := r0) (args := args) (dst := res) (s := pc').
      go. go. go.
      apply not_lazydef_outside_inop; go.
    }
    destruct ros.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge
          (inl _ (regrepr r)) rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      {
        apply spec_ros_r_find_function
          with (rs := rs); auto.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H2. left.
        split.
        - eapply live_at_notinop_if_used; eauto.
          go. go.
        - apply not_lazydef_outside_inop; go.
      }
      destruct Htfd as [tfd Hfind].
      exists (RTLpar.Callstate
        (RTLpar.Stackframe (regrepr res) tf sp pc' rs' :: ts)
        tfd (rs' ##2 (map regrepr args)) m).
      split_but_remember.
      - apply RTLpar.exec_Icall with (sig := RTLpar.funsig tfd)
          (ros := inl (regrepr r)).
        rewrite codeSome with
          (ins := (Icall (funsig fd) (inl r) args res pc'));
          go.
        simpl.
        rewrite sig_fundef_translated with (f := fd); go.
        tauto. tauto. auto.
      - split; auto.  
        rewrite <- RW.
        apply match_states_call.
        destruct Hfind. auto.
        econstructor; go.
        intros r0 Hprops.
        {
          assert(cssalive_spec f r0 pc).
          apply live_in_pred_if_notdefined with (pc' := pc'); go.
          {
            destruct Hprops as [Hlive | Hlazy].
            +
              decompose [and] Hlive.
              unfold not; intros Hdef.
              inv Hdef; go.
              apply absurd_notinop_at_entry with (f := f); go.
              induction WFF.
              inv H3; go.
              contradict H3.
              apply not_phi_def_outside_inop; go.
              contradict H3.
              apply not_parcb_def_outside_inop; go.
            + contradict Hlazy.
              apply not_lazydef_after_noinop with (pc := pc); go.
          }
          tauto.
          inv MREG.
          eqregreprs regrepr0 regrepr.
          apply H3. tauto.
        }
        intros.
        {
          unfold not; intros Hlive.
          assert(Hlivepc: cssalive_spec f r0 pc). 
          {
            econstructor 2; go.
            unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H4; go.
            contradict H4.
            apply not_phi_def_outside_inop; go.
            contradict H4.
            apply not_parcb_def_outside_inop; go.
          }
          exploit live_exists_def; eauto; intros Hdef.
          destruct Hdef as [d Hdef].
          exploit compute_regrepr_correct; eauto; intros Hninterf.
          inv Hninterf.
          assert(cssaliveout_spec f r0 pc).
          apply correspondance_outin with (pc' := pc'); eauto. go.
          assert(d2 = pc).
          eapply def_def_eq; eauto.
          congruence.
        }
        intros.
        apply not_lazydef_after_noinop with (pc := pc); go.
        go. 
        go.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (inr i) rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_id_find_function
        with (rs := rs); auto.
      destruct Htfd as [tfd Htfd].
      exists(RTLpar.Callstate
        (RTLpar.Stackframe (regrepr res) tf sp pc' rs' :: ts)
        tfd (rs' ##2 (map regrepr args)) m).
      split_but_remember.
      - apply RTLpar.exec_Icall
          with (sig := RTLpar.funsig tfd) (ros := inr i).
        rewrite codeSome with
          (ins := (Icall (funsig fd) (inr i) args res pc'));
          go.
        simpl.
        rewrite sig_fundef_translated with (f := fd); go.
        tauto. tauto. auto.
      - split; auto.
        rewrite <- RW.
        apply match_states_call.
        destruct Htfd. auto.
        econstructor; go.
        intros r0 Hprops.
        {
          assert(cssalive_spec f r0 pc).
          apply live_in_pred_if_notdefined with (pc' := pc'); go.
          {
            destruct Hprops as [Hlive | Hlazy].
            +
              decompose [and] Hlive.
              unfold not; intros Hdef.
              inv Hdef; go.
              apply absurd_notinop_at_entry with (f := f); go.
              induction WFF.
              inv H3; go.
              contradict H3.
              apply not_phi_def_outside_inop; go.
              contradict H3.
              apply not_parcb_def_outside_inop; go.
            + contradict Hlazy.
              apply not_lazydef_after_noinop with (pc := pc); go.
          }
          tauto.
          inv MREG.
          eqregreprs regrepr0 regrepr.
          apply H3. tauto.
        }
        intros.
        {
          unfold not; intros Hlive.
          assert(Hlivepc: cssalive_spec f r pc). 
          {
            econstructor 2; go.
            unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H4; go.
            contradict H4.
            apply not_phi_def_outside_inop; go.
            contradict H4.
            apply not_parcb_def_outside_inop; go.
          }
          exploit live_exists_def; eauto; intros Hdef.
          destruct Hdef as [d Hdef].
          exploit compute_regrepr_correct; eauto; intros Hninterf.
          inv Hninterf.
          assert(cssaliveout_spec f r pc).
          apply correspondance_outin with (pc' := pc'); eauto. go.
          assert(d2 = pc).
          eapply def_def_eq; eauto.
          congruence.
        }
        intros.
        apply not_lazydef_after_noinop with (pc := pc); go.
        go. go.
   }
   { (* Itailcall *)
     assert (WFfd: wf_cssa_fundef fd).
     {
       unfold wf_ssa_program in WF_PROG.
       assert (ID: exists id,
         In (id, Gfun fd) (prog_defs prog)).
       unfold find_function in H0.
       unfold Genv.find_funct in H0.
       flatten H0;
         apply Genv.find_funct_ptr_inversion
           with (b := b); auto.
       destruct ID as [id Infd].
       apply WF_PROG with id.
       auto.
     }
     assert (WFlivefd: wf_cssa_liverange_fundef fd).
     {
       unfold wf_cssa_liverange_program in WFlive_PROG.
       assert (ID: exists id,
         In (id, Gfun fd) (prog_defs prog)).
       unfold find_function in H0.
       unfold Genv.find_funct in H0.
       flatten H0;
         apply Genv.find_funct_ptr_inversion
           with (b := b); auto.
       destruct ID as [id Infd].
       apply WFlive_PROG with id.
       auto.
     }
     assert(RW: rs ##2 args = rs' ##2 (map regrepr args)).
     {
       apply match_regset_args.
       intros r Hin.
       inv MREG.
       eqregreprs regrepr0 regrepr.
       apply H3.
       left. split.
       eapply live_at_notinop_if_used; eauto.
       go. apply u_code.
       destruct ros.
       apply UItailcall with (sig := (funsig fd))
         (r := r0) (args := args).
       go. go. go.
       apply not_lazydef_outside_inop; go.
     }
     destruct ros.
     + assert(Htfd: exists tfd,
         RTLpar.find_function tge
          (inl _ (regrepr r)) rs' = Some tfd
         /\ transl_fundef fd = Errors.OK tfd).
       {
         apply spec_ros_r_find_function
           with (rs := rs); auto.
         inv MREG.
         eqregreprs regrepr0 regrepr.
         apply H3. left.
         split.
         - eapply live_at_notinop_if_used; eauto.
           go. go.
         - apply not_lazydef_outside_inop; go.
       }
       destruct Htfd as [tfd Hfind].
       exists (RTLpar.Callstate
         ts tfd (rs' ##2 (map regrepr args)) m').
       split_but_remember.
       - apply RTLpar.exec_Itailcall with (sig := RTLpar.funsig tfd)
           (ros := inl (regrepr r)).
         rewrite codeSome with
           (ins := (Itailcall (funsig fd) (inl r) args));
           go.
         simpl.
         rewrite sig_fundef_translated with (f := fd); go.
         tauto. tauto. auto.
         rewrite <- stacksize_preserved with (f := f); auto.
       - split; auto.  
         rewrite <- RW.
         apply match_states_call.
         destruct Hfind. auto.
         go. go. go.
     + assert(Htfd: exists tfd,
         RTLpar.find_function tge (inr i) rs' = Some tfd
         /\ transl_fundef fd = Errors.OK tfd).
       apply spec_ros_id_find_function
         with (rs := rs); auto.
       destruct Htfd as [tfd Htfd].
       exists(RTLpar.Callstate
         ts tfd (rs' ##2 (map regrepr args)) m').
       split_but_remember.
       - apply RTLpar.exec_Itailcall
           with (sig := RTLpar.funsig tfd) (ros := inr i).
         rewrite codeSome with
           (ins := (Itailcall (funsig fd) (inr i) args));
           go.
         simpl.
         rewrite sig_fundef_translated with (f := fd); go.
         tauto. tauto. auto.
         rewrite <- stacksize_preserved with (f := f); auto.
       - split; auto.
         rewrite <- RW.
         apply match_states_call.
         destruct Htfd. auto.
         go. go. go.
  }
  { (* Ibuiltin *)
    exists (RTLpar.State ts tf sp pc' (rs'#2 (regrepr res) <- v) m'). 
    split_but_remember.
    { apply RTLpar.exec_Ibuiltin with (ef := ef)
        (args := map regrepr args).
      rewrite codeSome with
        (ins := (Ibuiltin ef args res pc'));
        go.
      rewrite <- registers_equal with (rs := rs).
      eapply external_call_symbols_preserved; eauto.
      eapply symbols_preserved.
      eapply Genv.find_var_info_transf_partial; eauto.
      intros.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    split; auto.
    constructor; eauto.
    econstructor; eauto; intros.
    inv MREG.
    rewrite P2Map.gsspec.
    rewrite P2Map.gsspec.
    flatten.
    {
      eqregreprs regrepr0 regrepr.
      exploit liveorlazydef_exists_def; eauto; intros DEF.
      exploit compute_regrepr_correct; eauto; intros Hninterf.
      inv Hninterf.
      assert(def f res pc) by go.
      assert(EQ: d2 = pc).
      eapply def_def_eq; eauto.
      rewrite EQ in *.
      exfalso. eapply ninterlive_outside_inop; go.
      go.
    }
    eqregreprs regrepr0 regrepr.
    apply H3. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* ifso *)
    exists (RTLpar.State ts tf sp ifso rs' m).
    split_but_remember.
    { apply RTLpar.exec_Icond_true
        with (cond := cond) (args := map regrepr args)
        (ifnot := ifnot).
      rewrite codeSome with
        (ins := (Icond cond args ifso ifnot));
        go.
      rewrite <- registers_equal with (rs := rs).
      eauto.
      intros.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    + constructor; eauto.
      constructor; eauto.
      econstructor; eauto.
      intros.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3. left.
      split.
      - apply live_props_outside_inop with (pc' := ifso); go.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
  }
  { (* ifnot *)
    exists (RTLpar.State ts tf sp ifnot rs' m).
    split_but_remember.
    { apply RTLpar.exec_Icond_false
        with (cond := cond) (args := map regrepr args)
        (ifso := ifso).
      rewrite codeSome with
        (ins := (Icond cond args ifso ifnot));
        go.
      rewrite <- registers_equal with (rs := rs).
      eauto.
      intros.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    + constructor; eauto.
      constructor; eauto.
      econstructor; eauto.
      intros.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3. left.
      split.
      - apply live_props_outside_inop with (pc' := ifnot); go.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
  }
  { (* ijumptable *)
    exists (RTLpar.State ts tf sp pc' rs' m).
    split_but_remember.
    { apply RTLpar.exec_Ijumptable with (arg := regrepr arg)
        (tbl := tbl) (n := n).
      rewrite codeSome with
        (ins := Ijumptable arg tbl);
        go.
      rewrite <- H0.
      symmetry.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
      auto.
    }
    + constructor; eauto.
      constructor; eauto. intros.
      econstructor; eauto. intros r Hprops.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H3. left.
      split.
      - apply live_props_outside_inop with (pc' := pc'); go.
        econstructor; eauto. simpl.
        eapply list_nth_z_in; eauto.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
  }
  { (* ireturn *)
    destruct or.
    {
      exists (RTLpar.Returnstate ts
        (regmap2_optget (Some (regrepr r)) Vundef rs') m').
      split_but_remember.
      { apply RTLpar.exec_Ireturn.
        rewrite codeSome with
          (ins := Ireturn (Some r));
          go.
        erewrite <- stacksize_preserved; eauto. }
      split; auto.
      simpl.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      rewrite <- H2.
      apply match_states_return; go.
      left. split.
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    exists (RTLpar.Returnstate ts (regmap2_optget None Vundef rs') m').
    split; eauto.
    apply RTLpar.exec_Ireturn.
    rewrite codeSome with
      (ins := Ireturn None);
      go.
    erewrite <- stacksize_preserved; eauto.
  }
  { (* internal *)
    destruct tf as [tf | tf].
    exists (RTLpar.State ts tf (Vptr stk Int.zero)
      tf.(RTLpar.fn_entrypoint)
      (init_regs args (RTLpar.fn_params tf)) m').
    split_but_remember.
    { eapply RTLpar.exec_function_internal.
      erewrite <- stacksize_preserved; eauto.
      simpl in SPEC.
      unfold Errors.bind in SPEC.
      flatten SPEC. }
    split; auto.
    + simpl in *.
      unfold Errors.bind in SPEC.
      flatten SPEC. simpl in *.
      replace (RTLpar.fn_entrypoint tf) with (fn_entrypoint f).
      apply match_states_intro.
      go. go. induction WFF. auto.
      induction WFlive. go.
      {
        unfold transl_function in Eq.
        flatten Eq; go.
        econstructor; eauto.
        intros.
        exploit liveorlazydef_exists_def; eauto;
          induction WFF; auto; intros DEF.
        destruct DEF as [d DEF].
        apply init_regs_match with (f := f) (d := d); auto.
        induction WFlive. go.
        destruct H0; try tauto.
        contradict H0.
        apply not_lazydef_outside_jp.
        auto.
        unfold not; intros.
        apply fn_phicode_inv in H0; auto.
        case_eq((fn_phicode f) ! (fn_entrypoint f)); intros.
        assert(Hparcb: (fn_parcopycode f) ! (fn_entrypoint f) <> None).
        apply parcb'Some with (phib := p); eauto.
        contradict Hparcb.
        apply fn_no_parcb_at_entry with (f := f); auto.
        congruence.
      }
      unfold transl_function in Eq.
      flatten Eq. simpl. auto.
    + simpl in SPEC.
      unfold Errors.bind in SPEC.
      flatten SPEC.
  }
  { (* external *)
    inv SPEC.
    exists (RTLpar.Returnstate ts res m').
    split.
    + eapply RTLpar.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
      eapply symbols_preserved.
      eapply Genv.find_var_info_transf_partial; eauto.
    + econstructor; eauto.
  }
  { (* return state *)
    inv STACK.  
    exists (RTLpar.State ts0 tf sp pc
      (rs' #2 (regrepr res) <- vres) m).
    split.
    + eapply RTLpar.exec_return.
    + econstructor; eauto.
      econstructor; eauto; intros.
      rewrite P2Map.gsspec.
      rewrite P2Map.gsspec.
      flatten.
      assert(~ cssalive_spec f r pc) by eauto.
      destruct H. tauto. contradict H. eauto.
      apply MRs. tauto.
  }
Qed.
  
Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
    exists st2, RTLpar.initial_state tprog st2
      /\ match_states st1 st2.
Proof.
  intros.
  inv H.
  exploit function_ptr_translated; eauto.
  intros [tf [Hfind Htrans]].
  exists (RTLpar.Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply Genv.init_mem_transf_partial; eauto.
  rewrite symbols_preserved.
  rewrite (transform_partial_program_main _ _ TRANSF_PROG).  auto.
  rewrite <- H3. apply sig_fundef_translated; auto.
  unfold wf_cssa_program in WF_PROG.
  assert (ID: exists id, In (id, Gfun f) (prog_defs prog)).
  eapply Genv.find_funct_ptr_inversion; eauto.
  destruct ID as [id InId].
  apply WF_PROG with (id := id). eauto.
  eapply match_states_call; eauto.
  eapply Genv.find_funct_ptr_prop; eauto.
  eapply Genv.find_funct_ptr_prop; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2
  -> final_state st1 r
  -> RTLpar.final_state st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACK.
  constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (CSSApar.semantics prog) (RTLpar.semantics tprog).
Proof.
  eapply forward_simulation_step with (match_states := match_states).
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transl_step_correct. 
Qed.

End PRESERVATION.


Section WF.

Variable prog: CSSApar.program.
Variable tprog: RTLpar.program.
Hypothesis TRANSF_PROG: transl_program prog = Errors.OK tprog.
Hypothesis WF_TRANSF: wf_cssa_program prog. 

Lemma transl_function_inops : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc s, 
    (fn_code f) ! pc = Some (Inop s) <->
    (RTLpar.fn_code tf) ! pc = Some (Inop s).
Proof.
  unfold transl_function ; intros f tf TRANS pc s.
  flatten TRANS; simpl.
  unfold transl_code. rewrite PTree.gmap1.
  unfold option_map. 
  split.
  - intros INOP. rewrite INOP; auto.
  - flatten ; destruct i ; go ; try solve [simpl ; flatten].
Qed.

Lemma transl_function_ins : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc ins, 
    (fn_code f) ! pc = Some ins ->
    exists ins', (RTLpar.fn_code tf) ! pc = Some ins'.
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl.
  unfold transl_code. rewrite PTree.gmap1.
  unfold option_map. rewrite INS; auto.
  destruct ins ; go.
Qed.

Lemma transl_function_ins_2 : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc ins, 
    (RTLpar.fn_code tf) ! pc = Some ins ->
    exists ins', (fn_code f) ! pc = Some ins'. 
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl in *.
  unfold transl_code in *. rewrite PTree.gmap1 in *.
  unfold option_map in *. flatten INS ; eauto. 
Qed.

Lemma transl_function_parcb_2 : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc p, 
    (RTLpar.fn_parcopycode tf) ! pc = Some p ->
    exists p, (fn_parcopycode f) ! pc = Some p. 
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl in *.
  unfold transl_parcopycode in *. 
  repeat rewrite PTree.gmap1 in *.
  unfold option_map in *. flatten INS ; eauto. 
Qed.

Lemma entry_point_preserved : 
  forall f tf,
  transl_function f = OK tf -> 
  RTLpar.fn_entrypoint tf = fn_entrypoint f.
Proof.
  unfold transl_function ; intros f tf TRANS.
  flatten TRANS; go.
Qed.

Lemma successors_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc ins ins' pc', 
    (fn_code f) ! pc = Some ins ->
    (RTLpar.fn_code tf) ! pc = Some ins' ->
    (In pc' (successors_instr ins) <->
     In pc' (successors_instr ins')).
Proof.
  unfold transl_function ; intros f tf TRANS pc ins ins' pc' CODE TCODE.
  flatten TRANS; simpl in *; go.  
  unfold transl_code in *. rewrite PTree.gmap1 in *.
  unfold option_map in *. rewrite CODE in *.
  destruct ins ; go;
  try solve [destruct s0 ; go];
  destruct o ; go.
Qed.

Lemma successors_preserved_2 : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', In pc' (successors f) !!! pc <->
                 In pc' (RTLpar.successors tf) !!! pc.
Proof.
  intros f tf TRANS pc pc'.
  unfold successors, RTLpar.successors.
  unfold successors_list; simpl.
  repeat rewrite PTree.gmap1 in *.
  unfold option_map.
  flatten; simpl;  go ; flatten Eq0; eauto using successors_preserved ; eauto.
  - split; intuition; exploit transl_function_ins ; eauto.
    intros [ins' Hins']; congruence.
  - split; intuition; exploit transl_function_ins_2 ; eauto.
    intros [ins' Hins']; congruence.
Qed.

Lemma cfg_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', cfg f pc pc' <-> RTLpar.cfg tf pc pc'.
Proof.
  intros f tf TRANS pc pc'.
  split; intros.
  - invh cfg. 
    exploit transl_function_ins; eauto. 
    intros [ins' Hins']. 
    econstructor; eauto using successors_preserved. 
    eapply successors_preserved with (ins:= ins) ; go.
  - invh RTLpar.cfg. 
    exploit transl_function_ins_2; eauto. 
    intros [ins' Hins']. 
    econstructor; eauto using successors_preserved. 
    eapply successors_preserved with (ins:= ins') ; go.
Qed.

Lemma is_wf_function : forall f tf, 
  wf_cssa_function f ->                         
  transl_function f = Errors.OK tf -> 
  RTLpar.wf_function tf. 
Proof.
  intros. constructor.

  - exploit fn_entry; eauto. intros [s Hins].
    erewrite entry_point_preserved; eauto.
    rewrite transl_function_inops in Hins ; eauto. 

  - intros pc Hcont.
    invh RTLpar.cfg.
    unfold transl_function in *.
    flatten TRANS; simpl in *.
    unfold transl_code in *. rewrite PTree.gmap1 in HCFG_ins.
    unfold option_map in *. flatten HCFG_ins. 
    destruct i ; eelim fn_entry_pred; go; 
    try solve [simpl in *; flatten HCFG_ins; subst; eelim fn_entry_pred; go].

  - intros jp pc JP SUCC.
    erewrite <- successors_preserved_2 in SUCC; eauto.
    exploit fn_normalized ; eauto using jp_preserved_2.
    rewrite transl_function_inops; eauto.
    
  - intros pc pc' JP CFG JPCONT.
    eapply jp_preserved_2 in JP ; eauto. 
    eapply jp_preserved_2 in JPCONT ; eauto. 
    eelim wf_cssa_jp_not_jp with (pc:= pc) (pc':= pc') ; eauto.
    eapply cfg_preserved; eauto.

  - intros pc pc' parcb CODE TPARC NJP.
    eapply jp_preserved_1 ; eauto.
    rewrite <- transl_function_inops in *; eauto.
    exploit transl_function_parcb_2; eauto. intros [p Hp].
    eapply fn_parcbjp with (pc':= pc'); 
      eauto using jp_preserved_1.

  - intros pc PARC.
    destruct ((RTLpar.fn_parcopycode tf) ! pc) eqn: EQ; try congruence.
    exploit transl_function_parcb_2; go. intros [p' Hp'].
    exploit (CSSApar.parcb_inop f H pc)  ; eauto; go. intros [s Hpc].
    rewrite transl_function_inops in Hpc; eauto.

  - intros pc pc' instr CODE SUCC.
    exploit transl_function_ins_2; eauto. intros [ins' CODE'].
    rewrite <- successors_preserved with (ins':= instr) in SUCC; eauto.
    exploit fn_code_closed; eauto. intros [instr' CODESUCC].
    exploit transl_function_ins; eauto.

Grab Existential Variables.
go. go. go. go.
go. go. go. go.
go. go. go. 
Qed.

Theorem is_wf_program : RTLpar.wf_program tprog.
Proof.
 unfold RTLpar.wf_program. intros.
 destruct f; constructor.
 exploit transform_partial_program_function; eauto.
 intros [f0 [Hin Htrans]].
 destruct f0; inv Htrans. 
 destruct f0; simpl in *; auto.
 eapply is_wf_function  
     with (f:= CSSApar.mkfunction fn_sig fn_params 
                                  fn_stacksize fn_code fn_phicode fn_parcopycode
                                  fn_max_indice fn_entrypoint); eauto.
 exploit WF_TRANSF; eauto. 
 intros FUNDEF; inv FUNDEF; auto.
 unfold Errors.bind in H1.
 flatten H1.
Qed.
 
End WF.
