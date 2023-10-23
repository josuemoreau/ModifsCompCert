Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import SSA. 
Require Import SSAutils. 
Require Import Utilsvalidproof.
Require Import DomCompute.
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require FSetAVL.
Require Import Opt.
Require Import OptInv.
Require Import DLib.

(** Common Subexpression Elimination based on Global Value Numbering *)

(** * Validation algorithm *)
Section Checker.  
  
  Variable f : function.
  
  Notation code := (fn_code f).
  Notation phicode := (fn_phicode f).

  Definition certif := PTree.t ssa_def.
  Variable certificate : certif.
  
  Definition ssa_def_to_node (d:ssa_def) : node := 
    match d with
      | SDIop pc => pc
      | SDPhi pc _ => pc
    end.
  
  Definition top_set l : PTree.t unit :=
    fold_left (fun p s => PTree.set s tt p) l (PTree.empty _).
  
  Lemma in_top_set : forall l x, In x l -> PTree.get x (top_set l) = Some tt.
  Proof.
    assert (forall l s x,
              s ! x = Some tt ->
              (fold_left (fun (p : PTree.t unit) (s : PTree.elt) => PTree.set s tt p)
                         l s) ! x = Some tt).
    induction l; simpl; intros; go.
    apply IHl.
    rewrite PTree.gsspec; flatten.
    assert (forall l s x,
              In x l ->
              (fold_left (fun (p : PTree.t unit) (s : PTree.elt) => PTree.set s tt p)
                         l s) ! x = Some tt).
    induction l; simpl; intros; go.
    destruct H0; auto.
    apply H.
    subst; rewrite PTree.gss; auto.
    intros; apply H0; auto.
  Qed.
  
  Definition test_param_no_repr (s:PTree.t unit) : bool :=
    forall_ptree (fun r d =>
                     match get_ssa_eq f d with
                       | None => false
                       | Some e => 
                         let dst := ssa_eq_to_dst e in
                         match PTree.get dst s with
                           | Some _ => false
                           | None => 
                             match certificate ! dst with
                               | None => true
                               | Some _ => false
                             end
                         end
                     end) certificate.

  Definition make_repr (l:list reg) : reg -> (reg * node) :=    
    let s := top_set l in
    if test_param_no_repr s then
      let map := PTree.map (fun r d => match get_ssa_eq f d with
                                          | None => (r, xH)
                                          | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                        end) certificate in
      (fun r => match PTree.get r map with
                | Some r' => r'
                | None => (r, xH)
                end)
    else (fun r => (r,xH)).

  Lemma make_repr_not_id : forall l r r',
    In r l ->  fst (make_repr l r') = r -> r = r'.
  Proof.
    unfold make_repr; intros r r' Hi.
    flatten; simpl; auto.
    destruct p as (r0 & n0); intro; subst; simpl in *.
    unfold test_param_no_repr in Eq.
    rewrite PTree.gmap in Eq0.
    unfold option_map in Eq0.
    flatten Eq0.
    exploit ptree_forall; eauto.
    simpl.
    flatten.
    exploit in_top_set; eauto.
    congruence.
  Qed.

  Lemma test_itempotent s : 
    test_param_no_repr s = true ->
    let map := PTree.map (fun r d => match get_ssa_eq f d with
                                        | None => (r, xH)
                                        | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                      end) certificate in    
    forall r r', PTree.get r map = Some r' -> PTree.get (fst r') map = None.
  Proof.
    unfold test_param_no_repr; intros.
    rewrite PTree.gmap in H0.
    rewrite PTree.gmap.
    destruct (certificate ! r) eqn:E; inv H0.
    exploit ptree_forall; eauto; clear H.
    simpl.
    flatten; simpl.
    rewrite Eq1; auto.
  Qed.

  Lemma make_repr_itempotent : forall l r,
    fst (make_repr l (fst (make_repr l r))) = fst (make_repr l r).
  Proof.
    intros l r.
    unfold make_repr.
    destruct (test_param_no_repr (top_set l)) eqn:E1; simpl; auto.
    set (map := PTree.map (fun r d => match get_ssa_eq f d with
                                        | None => (r, xH)
                                        | Some e => (ssa_eq_to_dst e, ssa_def_to_node d)
                                      end) certificate).
    destruct (map ! r) eqn:E2; simpl; auto.
    - exploit test_itempotent; eauto.
      intros; assert (T : map ! (fst p) = None) by auto.
      rewrite T; auto.
    - rewrite E2; auto.
  Qed.
  
  Definition op_eq (x y:operation) : bool :=
    if eq_operation x y then true else false.

  Lemma op_eq_true_iff : forall x y, 
    op_eq x y = true <-> x = y.
  Proof.
    unfold op_eq; intros; destruct eq_operation; intuition congruence.
  Qed.

  
  Definition check_GVN_instr (f:function)
             (repr:reg-> (reg*node)) 
             (pc:node) (ins:instruction) : bool :=
    match ins with
      | Iop op args dst _ =>
        let dst' := fst (repr dst) in
        (peq dst dst') 
          ||
          (match PTree.get dst certificate with
             | None => false
             | Some (SDIop pc') =>
               match get_ssa_eq f (SDIop pc') with
                 | Some (EqIop op' args' dst0') =>
                   (peq dst' dst0') &&
                   (op_eq op op') && 
                   (fn_dom_test f pc' pc) &&
                   (negb (op_depends_on_memory op)) &&
                   (forall_list2 (fun x y => peq (fst (repr x)) (fst (repr y))) args args')
                 | _ => false
               end                 
             | Some _ => false
           end)
      | _ => true
    end.

  Definition check_GVN_phiblock (f:function)
             (repr:reg-> (reg*node)) (pc:node) (phib:phiblock) : bool :=
        forallb
          (fun (phi:phiinstruction) =>
             let (args,dst) := phi in
             let dst' := fst (repr dst) in
             (peq dst dst') 
               ||
               (match PTree.get dst certificate with
                  | None => false
                  | Some (SDPhi pc' idx) =>
                    (peq pc pc') 
                      &&
                      (match get_ssa_eq f (SDPhi pc' idx) with
                         | Some (EqPhi dst0' args') =>
                           (peq dst' dst0') 
                           &&
                           (forall_list2 (fun x y => peq (fst (repr x)) (fst (repr y))) args args')
                         | _ => false
                       end)                 
                  | Some _ => false
                end))
          phib.

  Definition dst_at_top l (m:PTree.t instruction) : list reg :=
    PTree.fold (fun l oc ins => 
                  match ins with 
                    | Iload _ _ _ r _ 
                    | Icall _ _ _ r _ => r :: l
                    | Ibuiltin _ _ (BR r) _ => r :: l
                    | _ => l
                  end) m l.

  Lemma dst_at_top_prop1 : forall m l pc,
    match m!pc with
      | Some (Iload _ _ _ r _) 
      | Some (Icall _ _ _ r _) => In r (dst_at_top l m)
      | Some (Ibuiltin _ _ (BR r) _) => In r (dst_at_top l m)
      | _ => True
    end.
  Proof.
    intros m l pc.
    unfold dst_at_top.
    apply PTree_Properties.fold_rec; intros.
    - rewrite <- H; flatten; auto.
    - rewrite PTree.gempty; auto.
    - rewrite PTree.gsspec.
      flatten; auto.
  Qed.

  Lemma dst_at_top_prop0 : forall m l,
    forall r, In r l -> In r (dst_at_top l m).
  Proof.
    intros m l.
    unfold dst_at_top.
    apply PTree_Properties.fold_rec; intros; auto.
    flatten; auto.
  Qed.

  Definition check_GVN : option (reg-> (reg * node)) :=
    let top_list := dst_at_top (fn_ext_params f) (fn_code f) in
    let repr := make_repr top_list in
    let check_params := forallb (fun r => peq (fst (repr r)) r) top_list in
    let check_instr := forall_ptree (check_GVN_instr f repr) (fn_code f) in
    let check_phiblock := forall_ptree (check_GVN_phiblock f repr) (fn_phicode f) in
    if check_params && check_instr && check_phiblock
    then Some repr
    else None.

End Checker.

(** * CSE optimisation based on GVN *)

Axiom extern_gvn: function -> certif.

Definition get_repr (f:function) (c:certif):=
  match check_GVN f c with
    | Some repr => repr
    | None => (fun x => (x,xH))
  end.

Definition get_extern_gvn (f:function): (reg -> (reg* node)) :=
  get_repr f (extern_gvn f).

Definition analysis (f: function) := ((get_extern_gvn f, f),P2Map.init true).

Definition res := ((reg -> reg*node)  (* repr(x) = (r, r_def) *)
                    * function        (* function *)                           
                   )%type.

Definition check_def (code:code) (pc:node) (x:reg) : bool :=
  match code!pc with
    | Some (Iop op args dst succ) => if peq x dst then true else false
    | Some (Iload chunk addr args dst succ) => if peq x dst then true else false
    | Some (Icall sig fn args dst succ) => if peq x dst then true else false
    | Some (Ibuiltin fn args (BR dst) succ) => if peq x dst then true else false
    | _ => false
  end.

Definition transf_instr (r:res) (pc:node) (instr:instruction) : instruction :=
  let '(repr,f) := r in
  match instr with
  | Iop op args dst s =>
    if is_trivial_op op then instr 
      else
        let (dst',def') := repr dst in
        if negb (peq dst dst') (* && is_dom def' pc  *)
           && check_def (fn_code f) def' dst' && negb (peq def' pc) 
        then Iop Omove (dst' :: nil) dst s               
        else instr
  | _ => instr
  end.

Definition transf_function (f: function) := 
  @Opt.transf_function res analysis transf_instr f. 
     
Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.
