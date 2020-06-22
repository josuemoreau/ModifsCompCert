(** The specification of the validation algorithm, given in terms of
the type system in [SSAvalid] is proved to preserve the semantics of program. *) 

Require Import Coq.Unicode.Utf8.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Classical.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Integers.
Require Import RTL RTLt.
Require Import Kildall.
Require Import KildallComp.
Require Import Conventions.
Require Import Utils.
Require Import RTLutils.
Require Import Path.
Require RTLdfs.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import SSAvalidspec.
Require Import SSAvalidator_proof.  
Require Import Utilsvalidproof.
Require Import LightLive.

(** * Some hints and tactics *)
Ltac elimAndb :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      elim (andb_prop _ _ H); clear H; intros; elimAndb
  | _ =>
      idtac
  end.

Ltac conv := simpl erase_reg in *.

Hint Constructors rtl_cfg: core.
Hint Constructors use_rtl_code: core.
Hint Constructors wf_live: core.
Hint Constructors RTLutils.assigned_code_spec: core.
Hint Constructors SSA.assigned_code_spec: core.
Hint Extern 4 (In _ (RTLt.successors_instr _)) => simpl RTLt.successors_instr: core.
Hint Extern 4 (In _ (SSA.successors_instr _)) => simpl SSA.successors_instr: core.

Ltac well_typed :=
  match goal with
    | [ Hwt : wt_instr _ _ _ |- _ ] => inv Hwt
  end.


(** * Generated SSA functions are well typed, and well formed *)
Section FUNC.

Variable f: RTLt.function.
Variable tf: SSA.function.
Notation size := (fn_max_indice tf).

Hypothesis HWF_DFS : RTLdfs.wf_dfs_function f.
Hypothesis TRANSF_OK : SSAvalid.transf_function f = OK tf.

Lemma WELL_TYPED : 
  exists live, 
    (let '(size,def,def_phi) := extern_gen_ssa f (fun pc => Lin f pc (Lout live)) in
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf)
    /\ wf_live f (Lout live).
Proof.
  intros. 
  unfold transf_function in  TRANSF_OK. 
  monadInv TRANSF_OK.
  exists x.
  destruct (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) as [[size def] def_phi]. 
  split ; auto.
  unfold get_option in EQ.
  case_eq (LightLive.analyze f) ; intros ; rewrite H in * ; inv EQ.
  exploit live_wf_live ; eauto.
Qed.  

Lemma STRUCT : structural_checks_spec f tf.
Proof.
  intros.
  unfold transf_function in  TRANSF_OK.
  monadInv TRANSF_OK.
  destruct (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) as [[size def] def_phi]. 
  exploit typecheck_function_size; eauto. intros Heq. inv Heq.
  eapply typecheck_function_correct_structural_checks  ; eauto.
Qed.

Lemma HWF : wf_ssa_function tf.
Proof.
  eapply transf_function_wf_ssa_function ; eauto.
Qed.

End FUNC.

(** * Semantics preservation *)
Require Import Linking.
Section PRESERVATION.

  Definition match_prog (p: RTLt.program) (tp: SSA.program) :=
  match_program (fun cu f tf => transf_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transf_program p = OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.
    
  Variable prog: RTLt.program.
  Variable tprog: SSA.program.
  
  Hypothesis TRANSL_PROG: match_prog prog tprog.
  Hypothesis WF_DFS_PROG: RTLdfs.wf_dfs_program prog.

  Let ge : RTLt.genv := Genv.globalenv prog.
  Let tge : SSA.genv := Genv.globalenv tprog.

  Import RTLdfsproof.
  
  Lemma transf_function_correct_aux:
    forall f tf, 
      (normalised_function f) ->
       RTLdfs.wf_dfs_function f ->
      transf_function f = OK tf ->
      exists live, exists Γ,  
        (wf_live f (Lout live))
        /\ (wf_init tf Γ) 
        /\ (wt_function  f tf live Γ).
  Proof.
    intros.
    unfold transf_function in H0. monadInv H1.
    case_eq (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) ;
      intros [size def] def_phi Hssa ; rewrite Hssa in *.
    exploit typecheck_function_size ; eauto ; intros Hsize ; inv Hsize.
    exploit typecheck_function_correct; eauto.
    eapply RTLdfs.fn_dfs_comp ; eauto.
    eapply RTLdfs.fn_dfs_norep ; eauto.
    intros [G [WFIG WTFG]].
    exists x; exists G.
    split; [idtac | split ;intuition].
    exploit live_wf_live; eauto.
    unfold get_option in EQ; inv EQ.
    destruct (analyze f) eqn: HEQ; allinv.
    inv H2; auto. congruence.
  Qed.
  
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    apply (Genv.find_symbol_transf_partial TRANSL_PROG). 
  Qed.

  Lemma match_prog_wf_ssa : wf_ssa_program tprog.
  Proof.
    red. intros.
    red in  WF_DFS_PROG.
    inv TRANSL_PROG.
    intuition. revert H0 H WF_DFS_PROG.
    induction 1; intros.
    - inv H.
    - inv H1.      
      + inv H. inv H4.
        { destruct f1 ; simpl in * ; try constructor; auto.
          * monadInv H7.
            constructor.
            eapply HWF; eauto.
            destruct a1, g.
            exploit (WF_DFS_PROG (Internal f0) i); eauto.
            simpl in * ; eauto.
            left. inv H; simpl in *; auto. 
            intros. inv H1; auto.
            simpl in *. inv H.
          * monadInv H7.
            constructor.
        }
      + eapply IHlist_forall2; eauto.
  Qed.
  
  Lemma function_ptr_translated:
    forall (b: block) (f: RTLt.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_ptr_transf_partial TRANSL_PROG).
  Qed.

  Lemma functions_translated:
    forall (v: val) (f: RTLt.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_transf_partial TRANSL_PROG). 
  Qed.

  Lemma sig_function_translated:
  forall f tf,
    transf_function f = OK tf ->
    SSA.fn_sig tf = RTLt.fn_sig f.
  Proof.
    intros.
    monadInv H.
    case_eq (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) ; intros [size def] def_phi Hssa ; rewrite Hssa in *.    
    unfold typecheck_function in EQ0. 
    destruct check_function_inv.
    destruct fold_left.
    destruct p as [[G newcode] juncpoints].
    monadInv EQ0.
    destruct compute_test_dom.
    destruct check_unique_def; simpl in EQ2; try congruence. 
    destruct check_code_at_phipoints; simpl in EQ2; try congruence. 
    inv EQ2; auto.
    congruence.
    congruence.
    congruence.
  Qed.
  
  Lemma sig_fundef_translated:
    forall f tf,
      transf_fundef f = OK tf ->
      SSA.funsig tf = RTLt.funsig f.
  Proof.
    intros.
    destruct f. 
    - monadInv H.
      simpl. eapply sig_function_translated; eauto.
    - monadInv H ; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof.
    apply (Genv.senv_transf_partial TRANSL_PROG).
  Qed.

  Lemma spec_ros_r_find_function:
    forall rs rs' f r r',
      rs#r = rs'#2 r' ->
      RTLt.find_function ge (inl _ r) rs = Some f ->
      exists tf,
        SSA.find_function tge (inl _ r') rs' = Some tf
        /\ transf_fundef f = OK tf.
  Proof.
    intros.
    eapply functions_translated; eauto.
    rewrite <- H0. symmetry. simpl.
    rewrite <- H. auto.
  Qed.
  
  Lemma spec_ros_id_find_function:
    forall rs rs' f id,
      RTLt.find_function ge (inr _ id) rs = Some f ->
      exists tf,
        SSA.find_function tge (inr _ id) rs' = Some tf
        /\ transf_fundef f = OK tf.
  Proof.
    intros.
    simpl in *.
    case_eq (Genv.find_symbol ge id) ; intros.
    rewrite H0 in H.
    rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
    exploit function_ptr_translated; eauto.
    rewrite H0 in H ; inv H.
  Qed.
    
  Lemma spec_ros_find_function:
    forall rs rs' f ros ros',
      check_ros_spec ros ros' ->
      (forall r r', ros = (inl ident r) -> ros' = (inl ident r') -> rs#r = rs'#2 r') ->
      RTLt.find_function ge ros rs = Some f ->
      exists tf,
        SSA.find_function tge ros' rs' = Some tf
        /\ transf_fundef f = OK tf.
  Proof.
    intros.
    case_eq ros; intros; rewrite H2 in *; try inv H.
    eapply spec_ros_r_find_function; eauto.
    eapply spec_ros_id_find_function with (rs:= rs); eauto.
  Qed.

  Lemma instr_at:
    forall f tf pc rinstr Γ live,
      check_function_spec f live tf Γ  ->
      (RTLt.fn_code f)!pc = Some rinstr ->
      exists pinstr, 
        (SSA.fn_code tf)!pc = Some pinstr /\
        check_instrs_spec tf rinstr pinstr.
  Proof.
    intros. inv H. 
    destruct H1 as [Hsig [Hstack [Herased [Hdef [Hphipar Hnodup]]]]].
    assert (Herased2:= erased_funct_erased_instr pc f tf rinstr Herased H0).
    destruct Herased2 as [pinstr [Htf Hrpinstr]].
    exists pinstr. split; eauto.
    rewrite Hrpinstr in *. 
    eapply check_instr_spec_erase; eauto.
  Qed.
    
  Ltac error pc :=
    (match goal with
       | [ H1: (fn_phicode _) ! pc = Some _,
         H2: ~ join_point pc _
         |- _ ] =>   elim H2 ; eapply phicode_joinpoint ; eauto
       | [ H1: (fn_phicode ?tf) ! pc = None ,
         H2: join_point pc _,
         HWF: wf_ssa_function ?tf
         |- _ ] =>   eelim (nophicode_nojoinpoint tf HWF pc); eauto
     end).

  Ltac error_struct tf pc pc' :=
    (match goal with
       | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _,
         HWF: wf_ssa_function ?tf
         |- _ ] =>
       let Hcont := fresh "Hcont" in
         (exploit (elim_structural tf HWF pc pc'); eauto ; intros Hcont ; inv Hcont)
     end).
  
  Ltac instr_succ pc pc' Hi :=
    match goal with
      | [ H1 : (fn_code ?tf) ! pc = Some _,
        HWF: wf_ssa_function ?tf
        |- _ ] =>
      assert (Hi : exists i, (fn_code tf) ! pc' = Some i) by
        (eapply (SSA.fn_code_closed tf HWF pc pc'); eauto;  (simpl; auto));
        destruct Hi as [instr' Hinstr'] ;
          destruct (join_point_exclusive tf HWF pc' instr' Hinstr'); (try (error pc'); try (error_struct tf pc pc'))
    end.

  (** ** Simulation relation *)

  (** Matching relation for stackframes *)
  Inductive match_stackframes : list RTLt.stackframe -> list SSA.stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil 
  | match_stackframes_cons: 
    forall res f sp pc rs s tf rs' ts Γ live
      (WF: wf_ssa_function tf),
      (match_stackframes s ts) ->
      (check_function_spec f live tf Γ) ->
      (wf_live f (Lout live)) ->
      (∀ j ins, (RTLt.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLt.fn_code f) ** ) (RTLt.fn_entrypoint f) j) ->
      (fn_phicode tf) ! pc = None ->
      get_index res = (Γ pc) (erase_reg res) ->
      (forall r, r <> (erase_reg res) ->
        Regset.In r (Lin f pc (Lout live)) ->
        rs#r = rs'#2 (r,Γ pc r)) ->
      match_stackframes 
      ((RTLt.Stackframe (erase_reg res) f sp pc rs) :: s)
      ((SSA.Stackframe res tf sp pc rs') :: ts).

  (** Agreement between values of registers wrt a register mapping *)
  Definition agree (β: Registers.reg -> index) (rs: RTLt.regset) (rps: SSA.regset) (live: Regset.t) : Prop :=
    forall r, Regset.In r live -> rs # r  = rps #2 (r, β r).
  
  Arguments Lout [A].
  Reserved Notation "s ≃ s'" (at level 40).
  
  (** Matching relation for states *)
  Inductive match_states : RTLt.state -> SSA.state -> Prop :=
  | match_states_reg: 
    forall s f sp pc rs m ts tf  rs'  Γ live
      (STACKS: match_stackframes s ts)
      (SPEC: check_function_spec f live tf Γ)
      (WFDFS: (∀ j ins, (RTLt.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLt.fn_code f) ** ) (RTLt.fn_entrypoint f) j))
      (WF: wf_ssa_function tf)
      (LIVE: wf_live f (Lout live))
      (AG: agree (Γ pc)  rs rs' (Lin f pc (Lout live))),
      (RTLt.State s f sp pc rs m) ≃ (SSA.State ts tf sp pc rs' m)
  | match_states_return: 
    forall s res m ts 
      (STACKS: match_stackframes s ts),
      (RTLt.Returnstate s res m) ≃ (SSA.Returnstate ts res m)
  | match_states_call:
    forall s f args m ts tf
      (STACKS: match_stackframes s ts)
      (WFDFS: RTLdfs.wf_dfs_fundef f)
      (TRANSF: transf_fundef f = OK tf),
      (RTLt.Callstate s f args m) ≃ (SSA.Callstate ts tf args m)
   where "s ≃ t" := (match_states s t).
  Hint Constructors match_states: core.  

  
  (** ** Auxiliary lemmas about [agree] preservation *)
  
Import DLib.  

  Lemma phistore_preserve_agree: 
    forall (tf: function) rs rs' k pc0 pc block G (v:positive) live f
      (LIVE: forall x, Regset.In x (Lin f pc (Lout live)) → Regset.In x (Lin f pc0 (Lout live)))
      (CFNS: check_phi_params_spec tf)
      (UDEF:  unique_def_spec tf)
      (NODUP: check_no_duplicates_spec tf )
      (PHI: (fn_phicode tf)! pc = Some block)
      (PRED: index_pred (make_predecessors (fn_code tf) successors_instr) pc0 pc = Some k)
      (AG: agree (G pc0) rs rs' (Lin f pc0 (Lout live)))
      (WTEDGE: wt_edge tf (Lin f pc (Lout live)) G pc0 pc),
      agree (G pc) rs (phi_store  k block rs') (Lin f pc (Lout live)).
  Proof.
  intros.
  unfold agree in *. intros x Hlive.
  generalize (erased_reg_assigned_dec x  block); intro Hx.
  destruct Hx as [Hx1 | Hx2 ]; invh wt_edge; allinv ; try congruence.  
  
  - (* there is a j st x_j is assigned in block *)
    inv Hx1. invh and. 
    inv H0.
    erewrite AG; eauto.
    destruct x0 as (xx & j).
    simpl in *.
    erewrite phi_store_copy with (args:= x); eauto.
    eapply check_udef_spec_no_dup; eauto.
    exploit check_udef_spec_no_dup; eauto. intros.    
    eapply UDEF; eauto. 
    split.
    + inv WTPHID; erewrite ASSIG; go. 
    + inv WTPHID0.
      exploit USES; eauto. intros PHIU.
      exploit CFNS ; eauto. intros NTH. 
      exploit @nth_okp_exists; eauto. intros [xarg Hxarg].
      exploit index_pred_some_nth; eauto. intros.
      exploit (@list_map_nth_some _ _ G); eauto. intros.
      eapply phiu_nth in PHIU ; eauto.
      destruct PHIU as (xargs & HEQ & HG). subst; auto. 

  - (* no x_j is assigned in the block *)
    erewrite phi_store_notin_preserved; eauto. 
    + rewrite (AG x); eauto.
      invh wt_phid.
      eelim (NASSIG x); go.
      intros; intro Hcont; eelim Hx2; go.
    + intros; intro Hcont; eelim Hx2; go.
Qed.
  
Lemma update_preserve_agree: forall rs rs' γi dst v r i live live' γ', 
  dst = (r,i) ->
  agree γi rs rs' live ->
  (forall x, Regset.In x live' -> (Regset.In x live) \/ x = r) ->
  γ' = (update γi r i) ->
  agree γ' (rs # r <- v) (rs' #2 dst <- v) live'.
Proof.
  intros.
  unfold agree in * ; intros.
  inv H2.
  destruct (peq r0 r).
  (* r' = r : same value ok *)
  rewrite e in *. 
  unfold update ; rewrite peq_true; auto. 
  subst.
  rewrite PMap.gss; try rewrite P2Map.gss; auto.
  (* r' <> r : update unchanged *)
  exploit H1 ; eauto. intros [Hcase1 | Hcase2].
  unfold update in *; rewrite peq_false in *; auto.
  rewrite PMap.gso; auto.    
  rewrite P2Map.gso; auto.    
  congruence.
  congruence.
Qed.

Lemma agree_preserve_arg : forall γ rs rs' arg live,
  Regset.In arg live ->
  agree γ rs rs' live ->
  rs # arg = rs' #2 (arg, γ arg).
Proof.
  intros.
  unfold agree in *.
  rewrite (H0 arg); eauto.
Qed.
  
Lemma agree_preserve_args : forall γ rs rs' args args'  live,
  (forall arg, In arg args -> Regset.In arg live) ->
  check_args_spec args args' ->
  (forall r i, In (r, i) args'  -> γ r = i) ->
  agree  γ rs rs' live ->
  rs ## args = rs' ##2 args'.
Proof.
  induction 2 ; auto.
  intros SPEC AG.
  simpl; rewrite IHcheck_args_spec; auto.
    
  case_eq arg; intros r i Heq;
    unfold erase_reg in * ; rewrite Heq in * ; simpl in *;
      cut (rs # r = rs'#2 arg). inv Heq.
  intros H4; rewrite H4 ; auto.
  subst; auto.
  exploit_dstr (SPEC  r i);  eauto. 
Qed.


Lemma agree_init_regs_gamma: forall tf Γ params args live,
  inclist params (fn_params tf) ->
  wf_init tf Γ ->
  agree (Γ (fn_entrypoint tf)) (RTLt.init_regs args (map erase_reg params)) (init_regs args params) live.
Proof.
  induction params; intros.
  (* nil *) simpl. unfold agree; intros. inv H0; allinv. rewrite P2Map.gi; rewrite PMap.gi; auto.
  (* a::l *)
  case_eq args; intros.
  (* args = nil *) simpl ; unfold agree; intros. rewrite PMap.gi; rewrite P2Map.gi; auto.
  (* args = v::l0 *)  
  case_eq a; intros.
  unfold agree; intros.
  set (mg := Γ (fn_entrypoint tf) r0) in *.
  simpl in |- * ; unfold erase_reg at 1 ; rewrite H2 in * ;  simpl in |- *.
  
  assert (Hsuff: inclist params (fn_params tf)) by (eapply inclist_indu ; eauto).
     
  assert (IHL := IHparams l live Hsuff H0).
  generalize H0 ; intros WFINIT.
  inv H0; allinv. 
  assert (Hina: In (r,p) (fn_params tf)). eapply inclist_cons_in; eauto.
  assert (ext_params tf (r, p)) by eauto.
  exploit (H4 (r, p)); eauto. intros. destruct H1. inv H1.
  destruct (peq x r0).
  (* r = r0 *) inv e. rewrite PMap.gss; rewrite P2Map.gss; auto.
  (* r <> r0 *)  rewrite PMap.gso; try rewrite P2Map.gso; auto. eapply IHparams ; eauto.
  congruence.
Qed.

Lemma wt_call_agree : forall f tf live pc fd fn' args'  s ts sp dst pc' x Γ rs rs' ros
  (WFLIVE: wf_live f (Lout live))
  (WF_SSA: wf_ssa_function tf)
  (WFDFS: (∀ j ins, (RTLt.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLt.fn_code f) ** ) (RTLt.fn_entrypoint f) j)),
  (RTLt.fn_code f) ! pc = Some (RTL.Icall (RTLt.funsig fd) ros (map erase_reg  args') (erase_reg dst) pc') ->
  (fn_code tf) ! pc = Some (Icall (RTLt.funsig fd) fn' args' dst pc') ->
  is_edge tf (pc) pc' ->
  index_pred  (make_predecessors (fn_code tf) successors_instr) pc pc' = Some x ->
  agree  (Γ pc) rs rs' (Lin f pc (Lout live)) ->
  unique_def_spec tf ->
  check_function_spec f live tf Γ ->
  wt_edge tf (Lin f pc' (Lout live)) Γ pc pc' ->
  match_stackframes s ts->
  match_stackframes (RTLt.Stackframe (erase_reg dst) f sp pc' rs :: s)
  (Stackframe dst tf sp  pc' rs' :: ts).
Proof.
  intros. generalize H6 ; intro HWTE.
  inv HWTE ; allinv ; (case_eq  dst; intros).

  - (* match stack frame 1 *)
  eapply match_stackframes_cons; eauto.
  well_typed; allinv ;  
  (unfold update in *; simpl; try rewrite peq_true; auto).
  inv H14 ; rewrite peq_true; auto.
  inv H14; rewrite peq_true; auto.
  
  unfold erase_reg; simpl in *. subst.
  intros.
  assert (HGEQ: Γ pc r0 = Γ pc' r0). 
  { well_typed; eauto;
    (unfold update in * ; rewrite peq_false in * ; simpl in *; auto).
  }
  exploit (wf_live_incl f (Lout live) WFLIVE pc pc') ; eauto.
  rewrite <- HGEQ.
  intuition. 
  
  eapply agree_preserve_arg with (γ := Γ pc) ; eauto.
  inv H11; allinv. go.
                                                     
  - (* match stack frame 2 : contradiction, cannot go to a join point with Icall *)
  assert (Hpc' : exists i, (fn_code tf)! pc' = Some i)
      by (eapply SSA.fn_code_closed; eauto).
  destruct Hpc' as (i & Hi).
  exploit SSAutils.fn_phicode_inv1; eauto.
  intros. 
  assert ((fn_code tf) ! pc = Some (Inop pc')).
  eapply fn_normalized with (pc:= pc) ; eauto.
  unfold successors_list, successors.
  rewrite PTree.gmap1.
  rewrite H0. simpl. auto.
  allinv.
Qed.

Create HintDb agree.
Create HintDb valagree.

Hint Resolve phistore_preserve_agree : agree.
Hint Resolve update_preserve_agree : agree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve agree_preserve_arg : valagree.
Hint Resolve agree_preserve_args : valagree.
Hint Resolve sig_fundef_translated : valagree.

Lemma agree_preserve_builtin_arg : forall sp m arg v rs,
    eval_builtin_arg ge (λ r : positive, rs # r) sp m arg v ->
    forall γ rs' arg' live,
      arg = (map_builtin_arg (λ a : reg, erase_reg a) arg') ->
      (forall arg, In arg (params_of_builtin_arg (map_builtin_arg (λ a : reg, erase_reg a) arg')) -> Regset.In arg live) ->
      (forall r i, In (r, i) (params_of_builtin_arg arg')  -> γ r = i) ->
      agree  γ rs rs' live ->
      eval_builtin_arg ge (λ r : P2Map.elt, rs' !!2 r) sp m arg' v.
Proof. 
  induction 1; intros; simpl in * ; eauto with barg;
    destruct arg';
    try solve [match goal with
                 id: _ = _ |- _ => inv id
               end; constructor; auto].
  - inv H. 
    destruct x0. simpl.
    rewrite (H2 r); eauto with valagree.
    erewrite H1 with (i:= p); eauto.
    constructor. 
    simpl; auto.
    eapply H0; simpl; eauto.
  - inv H1. constructor; eauto.
    + eapply IHeval_builtin_arg1; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
    + eapply IHeval_builtin_arg2; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.                  
  - inv H1.
    constructor; eauto.
    + eapply IHeval_builtin_arg1; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
    + eapply IHeval_builtin_arg2; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.                  
Qed.

Lemma agree_preserve_builtin_args : forall sp m  γ rs rs' args' vargs live,
    eval_builtin_args ge (λ r : positive, rs # r) sp m (map (map_builtin_arg (λ a : reg, erase_reg a)) args') vargs ->
    (forall arg, In arg (params_of_builtin_args (map (map_builtin_arg (λ a : reg, erase_reg a)) args')) -> Regset.In arg live) ->
    check_args_spec (params_of_builtin_args (map (map_builtin_arg (λ a : reg, erase_reg a)) args')) (params_of_builtin_args args') ->
    (forall r i, In (r, i) (params_of_builtin_args args')  -> γ r = i) ->
    agree  γ rs rs' live ->
    eval_builtin_args tge (λ r : P2Map.elt, rs' !!2 r) sp m args' vargs.
Proof.
  induction args' ; intros; eauto with barg.
  - simpl in *. invh eval_builtin_args. constructor.
  - simpl in *. invh eval_builtin_args. constructor.
    + eapply eval_builtin_arg_preserved with (ge1:= ge); eauto.
      * apply symbols_preserved.
      * eapply agree_preserve_builtin_arg; eauto.
        intros. eapply H0; eauto. simpl.
        apply in_or_app; eauto.
        intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
    + eapply IHargs'; eauto.
      * intros. eapply H0; eauto.
        apply in_or_app. right; auto.
      * revert H1. clear.
        generalize (params_of_builtin_args (map (map_builtin_arg (λ a0 : reg, erase_reg a0)) args')).
        generalize (params_of_builtin_args args').
        intros.
        eapply check_args_spec_erased_rwt_iff.
        eapply check_args_spec_erased_rwt_iff in H1.
        { rewrite map_app in H1.
          replace (params_of_builtin_arg (map_builtin_arg (λ a : reg, erase_reg a) a))
            with (map erase_reg (params_of_builtin_arg a)) in H1.
          - eapply app_inv_head; eauto.
          - clear H1. 
            induction a; simpl; intros; auto.
            + rewrite map_app.
              rewrite IHa1; eauto.
              rewrite IHa2; eauto.
            + rewrite map_app.
              rewrite IHa1; eauto.
              rewrite IHa2; eauto.
        }
      * intros. eapply H2; eauto.
        apply in_or_app. right; auto.
Qed.

(** ** The [match_state] is indeed a simulation relation *)
Lemma transf_initial_states:
  forall st1, RTLt.initial_state prog st1 ->
    exists st2, SSA.initial_state tprog st2 /\ st1 ≃ st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  econstructor; split.
  - econstructor.
    assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSL_PROG); eauto).
    + apply MEM ; auto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
  - eapply match_states_call  ; eauto.
    + constructor.
    + eapply Genv.find_funct_ptr_prop ; eauto.  
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  st1 ≃ st2 -> RTLt.final_state st1 r -> SSA.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Ltac exploit_hyps SPEC :=
  let Hspec' := fresh "Hspec'" in
  (exploit instr_at; eauto; intros Hinstr;
    destruct Hinstr as [pinstr [Hpinstr Hspec]];
      generalize Hspec; intro Hspec' ; inv Hspec';
        generalize SPEC; intro SPEC'; inv SPEC;
  (match goal with
     | [ H1 : wf_init _ _  /\ wt_function _ _ _ _ /\ _ |- _ ] => destruct H1 as [Hwfi [[Hwte Hwto] HWL]]
     | _ => idtac
   end);
  (match goal with
     | [ H1 : structural_checks_spec _ _ |- _ ] => destruct H1 as [SSIG [SSTACK [SERAS [SUDEF [SPHI SDUP]]]]]; auto
     | _ => idtac
   end)).

Ltac matches pc pc' :=
  (match goal with
     | [ H1: (fn_phicode _) ! pc = Some ?block,
       H2: (fn_phicode _) ! pc' = Some _,
       H3: index_pred _ ?i pc = Some ?k
       |- _ ] => idtac
     | [ H1: (fn_phicode _) ! pc' = Some _ |- _ ] => 
       (econstructor ; eauto)  ; eauto with agree
     |  [ H1: (fn_phicode _) ! pc' = None |- _ ] =>
       (try econstructor ; eauto ; (eauto ; eauto with agree));
       (eauto with agree) ; eauto with agree
   end);
  allinv ; eauto with agree.

Lemma regmap2_setres_noBR : forall T vres rs dst,
    (forall r, dst <> BR r) ->
    (regmap2_setres T dst vres rs) = rs.
Proof.
  induction dst ; intros ; simpl in * ; eauto.
  eelim H; eauto.
Qed.

Lemma regmap_setres_erase_noBR : forall T vres rs dst,
    (forall r, dst <> BR r) ->
    (@regmap_setres T (map_builtin_res erase_reg dst) vres rs) = rs.
Proof.
  induction dst ; intros ; simpl in * ; eauto.
  eelim H; eauto.
Qed.

Lemma transl_step_correct:
  forall s1 t s2, RTLt.step ge s1 t s2 ->
    forall s1', 
      s1 ≃ s1' ->
      exists s2',
        SSA.step tge s1' t s2' /\ s2 ≃ s2'.
Proof.
  induction 1; intros s1' MATCH;
    inv MATCH; auto;      
  try (try exploit_hyps SPEC;
  try (assert (Hedge : is_edge tf pc pc') by go;
    assert (Hwtedge : wt_edge tf (Lin f pc' (Lout live)) Γ pc pc') by eauto);
  (exploit is_edge_pred ; eauto ; intros [x H2] ) ;
  try (
    assert (Hedge0 : is_edge tf pc0 pc) by (eapply pred_is_edge; eauto);
      assert (Hwtedge0 : wt_edge tf (Lin f pc' (Lout live)) Γ pc0 pc) by (eauto)
  );
  try (case_eq ((fn_phicode tf)!pc'); intros) ;
  try destruct (join_point_exclusive tf HWF pc')); try (error pc'); try (error_struct tf pc pc');
  try (instr_succ pc pc' Hi ; try (error pc'); try (error_struct tf pc pc')).
  
  - (* nop *)
    (* 1 - from a state with phi-block at pc' : exec phiblock and then instr at pc' *)
    exists (State ts tf sp pc' (phi_store x p rs') m).
    split. constructor 2; auto. 
    inv Hwtedge; allinv. 
    econstructor ; eauto.  
    eapply phistore_preserve_agree  with (pc:= pc') (pc0:= pc) ; eauto. 
    intros. exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto.
    intuition. inv H5 ; allinv.  

  - (* 2 - from a state with no phi-block at pc' *)
    exists (State ts tf sp pc' rs' m).
    split.  constructor ; auto.
    inv Hwtedge; allinv. well_typed; allinv.
    matches pc pc'. 
    unfold agree in *; intros.
    exploit AG ; eauto. 
    intros. exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto. 
    intuition. inv H5 ; allinv. 

  - (* op *)
    exists (State ts tf sp pc' (rs'#2dst <- v) m).
    split. econstructor ; eauto.
    inv Hwtedge; allinv.
    well_typed.
    rewrite <- H0. replace (rs'##2args') with (rs##args); eauto with valagree.
    eapply agree_preserve_args; eauto.
    intros ; exploit (wf_live_use f (Lout live)) ; eauto.

    (inv Hwtedge; allinv; well_typed); matches pc pc'.

    eapply update_preserve_agree ; eauto. 
    intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
    right ; inv H8 ; allinv ; auto.

  - (* load *)
    exists (State ts tf sp pc' (rs'#2dst0 <- v) m).
    split. eapply exec_Iload; eauto.
    inv Hwtedge ; allinv ; well_typed ; rewrite <- H0; replace (rs'##2args') with (rs##args); eauto with valagree.
    eapply agree_preserve_args; eauto.
    intros ; exploit (wf_live_use f (Lout live)) ; eauto.
    inv Hwtedge; allinv; well_typed.
    matches pc pc'.
    eapply update_preserve_agree ; eauto.
    intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
    right ; inv H9 ; allinv ; auto.  
    
  - (* store *)
    exists (State ts tf sp pc' rs' m').
    split. eapply exec_Istore with (a:= a) ; eauto.
    inv Hwtedge ; allinv ; well_typed;
    rewrite <- H0; replace (rs'##2args') with (rs##args); eauto with valagree.
    eapply agree_preserve_args; eauto.
    intros;  eapply (wf_live_use f (Lout live)) ; eauto. 
    rewrite <- H1; inv Hwtedge ; allinv ; well_typed.
    replace (rs'!!2 src0) with (rs#(erase_reg src0)); eauto with valagree.
    unfold erase_reg ; simpl. destruct src0 ; simpl fst in *. 
    assert (Γ pc r = p). exploit H7 ; eauto. rewrite <- H5.
    eapply agree_preserve_arg ; eauto.
    eapply (wf_live_use f (Lout live)) ; eauto.
    
    inv Hwtedge; allinv; well_typed ;  matches pc pc'.
    unfold agree in *; intros. 
    intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
    eapply AG ; eauto. 
    inv H9 ; allinv.
     
  - (* call *)
    exploit (spec_ros_find_function rs rs' fd ros fn') ;eauto.
    intros. inv H4. inv H8. 
    inv Hwtedge; allinv; well_typed. 
    destruct r'. unfold erase_reg in * ; simpl in *.
    replace p with (Γ pc r0). eapply agree_preserve_arg; eauto. 
    eapply (wf_live_use f (Lout live)) ; eauto. 
    exploit H8 ; eauto.
   
    intros [tf' [Hfind Htrans]].
    exists (Callstate (Stackframe dst tf sp pc' rs':: ts)  tf' rs'##2args' m).
    split.
    econstructor ; eauto with valagree.
    replace (rs'##2args') with (rs##args).
    econstructor ; eauto. 
    replace args with (map erase_reg args') in *.
    eapply wt_call_agree; eauto. 
    eapply check_args_spec_erased_rwt ; eauto.
    destruct ros; simpl in H0.
    (eapply Genv.find_funct_prop ; eauto).
    destruct Genv.find_symbol in H0 ; try congruence.
    (eapply Genv.find_funct_ptr_prop ; eauto). 
  
    inv Hwtedge; allinv ; well_typed ; inversion Hspec ; eapply agree_preserve_args ; eauto.
    intros ; eapply (wf_live_use f (Lout live)) ; eauto. 
    destruct ros ; eauto.
    intros ; eapply (wf_live_use f (Lout live)) ; eauto. 
    destruct ros ; eauto.  

  - (* tailcall *)
  exploit_hyps SPEC.
  exploit (Hwto pc). econstructor; eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
  exploit (spec_ros_find_function  rs rs' fd ros fn') ;eauto.
  intros. inv H4. clear H5. inv H7.
  destruct r' ; unfold erase_reg in * ; simpl fst in *.
  well_typed.
  replace p with (Γ pc r).
  eapply agree_preserve_arg; eauto ; conv.
  eapply (wf_live_use f (Lout live)) ; eauto.
  exploit H5 ; eauto. 
  intros Htmp ; destruct Htmp as [tf' [Hfind Htrans]].
  
  exists (Callstate ts tf' rs'##2args' m').
  split.  econstructor; eauto with valagree.
  congruence.
  
  replace (rs'##2args') with (rs##args).
  econstructor; eauto.
  destruct ros; simpl in H0.
  (eapply Genv.find_funct_prop ; eauto).
  destruct Genv.find_symbol in H0 ; try congruence.
  (eapply Genv.find_funct_ptr_prop ; eauto). 
  
  well_typed; eapply agree_preserve_args; eauto. 
  intros ; eapply (wf_live_use f (Lout live)) ; eauto.
  destruct ros ; eauto.
  intros ; eapply (wf_live_use f (Lout live)) ; eauto.
  destruct ros ; eauto. 

  - (* built in *)
    exists (State ts tf sp pc' (regmap2_setres _ dst vres rs') m').
    split.
    + eapply exec_Ibuiltin with (vargs:= vargs); eauto with valagree.
      * { exploit check_instr_spec_erase; eauto.
          simpl. intros [Heq _]. inv Heq.
          eapply agree_preserve_builtin_args; eauto with valagree.
          - intros ; eapply (wf_live_use f (Lout live)) ; eauto.
          - exploit (Hwte pc). econstructor; eauto.
            clear Hwte; intros Hwte; inv Hwte; allinv.
            inv WTI; eauto.
        }
      * eapply external_call_symbols_preserved; eauto with valagree.
        apply senv_preserved.
    + inv Hwtedge; allinv; well_typed.

      * matches pc pc'.
        eapply update_preserve_agree ; eauto.
        intros ; exploit (wf_live_incl f (Lout live)) ; eauto. 
        intuition. inversion H9 ; allinv. intuition.
      * matches pc pc'.
        rewrite regmap2_setres_noBR; try solve [eapply H9; eauto].
        rewrite regmap_setres_erase_noBR; try solve [eapply H9 ; eauto].
        unfold agree in * ; intros.
        exploit (wf_live_incl f (Lout live)) ; eauto. intros [Hok | Hcont].
        eapply (AG r) ; eauto. inv Hcont ; allinv.
        { destruct dst; simpl in *.
          - eelim H9 ; eauto.
          - congruence.
          - congruence.
        }
    
  - exploit_hyps SPEC.
    assert (Hedge : is_edge tf pc ifso) by (econstructor; eauto ; simpl ; auto).
    assert (Hwtedge : wt_edge tf (Lin f ifso (Lout live)) Γ pc ifso) by eauto.
    destruct b.
    
    + (* cond_true *)
      assert (exists i, (fn_code tf) ! ifso = Some i)
        by (eapply SSA.fn_code_closed; eauto). 
      destruct H1.
      
      exists (State ts tf sp ifso rs' m).
      split. eapply exec_Icond_true ; eauto.
      replace (rs'##2args') with (rs##args) ; eauto with valagree.
      eapply agree_preserve_args ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto.
      
      inv Hwtedge; allinv; try well_typed ; eauto.
      exploit (elim_structural tf WF pc ifso); eauto. congruence.
      inv Hwtedge; allinv; try well_typed ; matches pc ifso.
      unfold agree in * ; intros.
      exploit (wf_live_incl f (Lout live)) ; eauto. intros [Hok | Hcont].
      eapply (AG r) ; eauto. inv Hcont ; allinv.
      error_struct tf pc ifso.
      
   + (* icond false *)
     clear Hedge Hwtedge.
     assert (Hedge : is_edge tf pc ifnot) by (econstructor; eauto; simpl; auto).
     assert (Hwtedge : wt_edge tf (Lin f ifnot (Lout live)) Γ pc ifnot) by eauto.

     assert (exists i, (fn_code tf) ! ifnot = Some i).
     eapply SSA.fn_code_closed; eauto. destruct H1.
     
     exists (State ts tf sp ifnot rs' m);
       split; try (eapply exec_Icond_false ; eauto).
     replace (rs'##2args') with (rs##args) ; eauto with valagree.
     inv Hwtedge; allinv ; try well_typed ; eapply agree_preserve_args ; eauto.
     intros ; eapply (wf_live_use f (Lout live)) ; eauto.
     error_struct tf pc ifnot.
     error_struct tf pc ifnot.
     
     inv Hwtedge; allinv; try well_typed; matches pc ifnot.
     unfold agree in * ; intros.
     exploit (wf_live_incl f (Lout live) HWL pc ifnot) ; eauto. intros [Hok | Hcont].
     eapply (AG r) ; eauto. inv Hcont ; allinv.
     error_struct tf pc ifnot.
  
  - (* jump table *)
  exploit_hyps SPEC.
  assert (exists i, (fn_code tf) ! pc' = Some i).
  eapply SSA.fn_code_closed; eauto. simpl; auto.
  eapply list_nth_z_in; eauto. destruct H2.
  
  assert (Hedge : is_edge tf pc pc') by (econstructor; eauto; simpl; eapply list_nth_z_in; eauto).
  assert (Hwtedge : wt_edge tf (Lin f pc' (Lout live)) Γ pc pc') by auto.
  exists (State ts tf sp pc' rs' m);
  split; try (eapply exec_Ijumptable ; eauto).
  rewrite <- H0.  symmetry.
  inv Hwtedge; allinv ; try well_typed; conv ; eauto with agree.
  destruct arg0 ; unfold erase_reg in * ; simpl fst in *.
  replace p with (Γ pc r).
  eapply agree_preserve_arg ; eauto.
  eapply (wf_live_use f (Lout live)) ; eauto.
  exploit H5 ; eauto.
  destruct arg0 ; unfold erase_reg in * ; simpl fst in *.
  replace p with (Γ pc r).
  eapply agree_preserve_arg ; eauto.
  eapply (wf_live_use f (Lout live)) ; eauto.  
  (exploit (elim_structural tf WF pc pc'); eauto).
  (eapply list_nth_z_in in H1; eauto).  
  congruence.
    
  inv Hwtedge; allinv; try well_typed; matches pc pc'.
  unfold agree in * ; intros.
  exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto.
  econstructor ; eauto. 
  (eapply list_nth_z_in in H1; eauto).  
  intros [Hok | Hcont].
  eapply (AG r) ; eauto. inv Hcont ; allinv.
  
  (exploit (elim_structural tf WF pc pc'); eauto).
  (eapply list_nth_z_in in H1 ; eauto).
  congruence.

  - (* return None+Some *)
  exploit_hyps SPEC.
  exploit (Hwto pc). constructor 2 with (or:= None); eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
  exists (SSA.Returnstate ts (regmap2_optget None Vundef rs') m'); split ; eauto.
  eapply SSA.exec_Ireturn; eauto. congruence.
  exploit (Hwto pc). constructor 2 with (or:= Some r); eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
  exists (Returnstate ts (regmap2_optget (Some r) Vundef rs') m'); split ; eauto.
  eapply exec_Ireturn; eauto. congruence.
  simpl. replace (rs'#2r) with (rs#(erase_reg  r)); eauto.
  well_typed; conv ; eauto with valagree. 
  destruct r ; simpl.
  replace p with (Γ pc r).
  eapply agree_preserve_arg ; eauto.
  eapply (wf_live_use f (Lout live)) ; eauto.
  exploit H4 ; eauto.
    
  - (* internal *)
    simpl in TRANSF. monadInv TRANSF.   
    inv WFDFS ; auto.
    exploit WELL_TYPED; eauto.
    intros [live [TYPECHECK CFNS]]. 
    (case_eq (extern_gen_ssa f (fun pc => Lin f pc (Lout live))) ; intros [size def] def_phi Hext);
      (rewrite Hext in * );
      (exploit typecheck_function_size ; eauto);
      (intros Heq ; subst).

    inv H1.
    exploit typecheck_function_correct; eauto.
    intros [Γ [WTF [WFINIT [HERA [HNORM [[HCK HNODUP] HH]]]]]].
    inv HERA. 

    exists (State ts x (Vptr stk Ptrofs.zero) x.(fn_entrypoint) (init_regs args x.(fn_params)) m').
    split.
    eapply exec_function_internal; eauto.
    erewrite <- typecheck_function_correct_ssize; eauto.
    replace (RTLt.fn_entrypoint f) with (fn_entrypoint x) at 1; auto.
    replace (RTLt.fn_params f) with (map erase_reg (fn_params x)); auto.
    
    econstructor ; eauto.
    * econstructor; eauto.
      eapply STRUCT; eauto.
      constructor; auto. 
    * eapply transf_function_wf_ssa_function; eauto.
      constructor; auto. 
    * eapply agree_init_regs_gamma ; eauto. 
      apply inclist_refl. 

  - (* external *)
  inv TRANSF.
  exists (Returnstate ts res m'). split. 
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto with valagree.
  eapply senv_preserved.
  econstructor ; eauto.

  - (* return state *)
  inv STACKS. 
  exists (State ts0 tf sp pc (rs'#2 res0 <- vres) m);
    split; ( try constructor ; eauto).
  
  econstructor ; eauto.
  unfold agree; intros. destruct res0; conv. 
  destruct (peq r0 r).
  (* same : receive the same value *)
  inv e. rewrite PMap.gss. simpl in H11. inv H11. 
  rewrite P2Map.gss at 1 ; auto. 
  (* different : use the info in the stack *)
  rewrite PMap.gso ; auto.
  rewrite P2Map.gso; auto. intro. elim n ; inv H0 ; auto.
Qed. 

(** ** Final semantics preservation result *)
Theorem transf_program_correct:
  forward_simulation (RTLt.semantics prog) (SSA.semantics tprog).
Proof.
  eapply forward_simulation_step.
  - eapply senv_preserved; eauto.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact transl_step_correct. 
Qed.

  End CORRECTNESS.

  
End PRESERVATION.
