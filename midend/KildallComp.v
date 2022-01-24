(* Additional lemmas on Kildall *)

Require Import Coqlib.
Require Import Iteration.
Require Import Maps.
Require Import Lattice.
Require Import Kildall.
Require Import Classical.

Section CORRECTNESS.

Lemma add_successors_correct2:
  forall tolist from pred n s,
    ~ (In n pred!!!s) -> (~In s tolist \/ n<>from) ->
    ~ In n (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  - tauto.
  - apply IHtolist.
    * intro.
      unfold successors_list at 1 in H1.
      { case_eq ((PTree.set a (from :: pred !!! a) pred) ! s);
        [ intros l Hl | intros Hl]; rewrite Hl in *.
        - (* normal case *)
          destruct (peq a s); subst.
          rewrite PTree.gss in Hl. inv Hl. inv H1.
          destruct H0. elim H0. intuition. congruence.
                       elim H0. auto.
                       elim H. auto.
          rewrite PTree.gso in Hl ; auto.
          unfold successors_list in H.
          rewrite Hl in *. intuition.
        - (* error case *) inv H1.
      }
    * destruct H0. left.
      intro. elim H0. intuition.
      intuition.
Qed.

Context {A: Type}.
Variable code: PTree.t A.
Variable successors: A -> list positive.

Definition make_preds : PTree.t (list positive) :=
  make_predecessors code successors.

Lemma make_predecessors_correct2_aux :
  forall n i s,
    code ! n = Some i ->
    ~In s (successors i) ->
    ~In n make_preds!!!s.
Proof.
  intros until s. intros Hcode.
  set (P := fun (m:PTree.t A) preds =>
              ~In s (successors i) -> ~In n preds!!!s) in *.
  apply PTree_Properties.fold_rec with (P := P).
(* extensionality *)
  unfold P; intros.
  apply H0; auto.
(* base case *)
  red ; unfold successors_list. repeat rewrite PTree.gempty. auto.
(* inductive case *)
  unfold P; intros.
  eapply add_successors_correct2; eauto.
  destruct (peq n k).
  - inv e.
    left ; auto.
    rewrite Hcode in *. congruence.
  - auto.
Qed.

Lemma make_predecessors_correct2 :
  forall n i s,
    code ! n = Some i ->
    In n make_preds!!!s ->
    In s (successors i).
Proof.
  generalize make_predecessors_correct2_aux ; intro.
  intros.
  assert (Hdecpos:forall (p1 p2: positive), {p1 = p2}+{p1 <> p2}) by decide equality.
  assert (Hin := In_dec  Hdecpos s (successors i)).
  destruct Hin; auto.
  exploit H ; eauto. intuition.
Qed.

Lemma make_predecessors_some : forall s l,
  make_preds ! s = Some l ->
  forall p, In p l -> exists i, code ! p = Some i.
Proof.
  unfold make_preds, make_predecessors.
  apply PTree_Properties.fold_rec; intros.
  - rewrite <- H. eapply H0; eauto.
  - rewrite PTree.gempty in H. inv H.
  - destruct (peq k p).
    * subst. rewrite PTree.gss. eauto.
    * rewrite PTree.gso; auto.
      destruct (classic (In p a !!! s \/ p = k /\ In s (successors v))).
      {
        destruct H4 as [Hcase1 | Hcase2].
        - unfold successors_list in *.
          case_eq (a ! s) ; intros.
          * rewrite H4 in *. eapply (H1 s); eauto.
          * rewrite H4 in *. inv Hcase1.
        - inv Hcase2. congruence.
      }
      {
        eelim add_successors_correct2 with (tolist := (successors v)); eauto.
        unfold successors_list. rewrite H2.
        auto.
      }
Qed.

Lemma add_successors_nodup:
  forall tolist from pred s,
   (list_norepet pred!!!s) ->
   (list_norepet tolist) ->
   (forall succ, In succ tolist -> ~ In from pred!!!succ) ->
   list_norepet (add_successors pred from tolist)!!!s.
Proof.
  induction tolist; simpl; intros.
  - tauto.
  - apply IHtolist.
    * unfold successors_list.
      { case_eq ((PTree.set a (from :: pred !!! a) pred) ! s);
        [ intros l Hl | intros Hl].
        - (* normal case *)
          unfold successors_list in Hl. rewrite Hl.
          destruct (peq a s); subst.
          + rewrite PTree.gss in Hl. inv Hl.
            constructor; auto.
            eapply H1; eauto.
          + rewrite PTree.gso in Hl ; auto.
            unfold successors_list in H.
            rewrite Hl in *. auto.
        - (* error case *)
          unfold successors_list in Hl. rewrite Hl.
          constructor.
      }
    * inv H0; auto.
    * intros.
      destruct (peq succ a).
      -- subst. inv H0. congruence.
      -- unfold successors_list. rewrite PTree.gso; auto.
         eapply H1; eauto.
Qed.

Lemma add_successors_preserve : forall tolist a from pc,
    ~ In pc tolist ->
    (add_successors a from tolist) !!! pc =
    a !!! pc.
Proof.
  induction tolist.
  - auto.
  - intros. simpl.
    rewrite IHtolist.
    + assert (pc <> a).
      { intro. subst.
        elim H.
        constructor; auto.
      }
      unfold successors_list.
      rewrite PTree.gso; auto.
    + intro. elim H.
      solve [econstructor; eauto].
Qed.

Lemma make_predecessors_list_list_norepet :
  forall pcins,
  list_norepet (map fst pcins) ->
  forall acc jp,
  list_norepet (acc !!! jp) ->
  (forall pc p i, In (p,i) pcins -> ~ In p (acc !!! pc)) ->
  (forall p i, In (p,i) pcins -> In jp (successors i) -> list_norepet (successors i)) ->
  list_norepet (fold_left (fun a p => add_successors a (fst p) (successors (snd p))) pcins acc) !!! jp.
Proof.
  induction pcins; intros.
  - simpl. auto.
  - simpl. destruct a as [pc ins].
    simpl map in H.
    simpl fst in *.
    simpl snd in *.
    eapply IHpcins; eauto.
    + inv H; auto.
    + destruct (in_dec peq jp (successors ins)).
      * eapply add_successors_nodup; eauto.
        -- eapply H2; eauto.
           constructor; eauto.
        -- intros. eapply H1; eauto.
           constructor; auto.
      * rewrite add_successors_preserve; eauto.
    + intros.
      destruct (in_dec peq pc0 (successors ins)).
      * apply add_successors_correct2; auto.
        -- eapply H1; eauto.
           econstructor 2; eauto.
        -- right. intro Hcont; subst.
           inv H. eapply in_map with (f:= fst) in H3.
           simpl fst in *. congruence.
      * rewrite add_successors_preserve; eauto.
        eapply H1; eauto.
        econstructor 2; eauto.
    + intros.
      eapply H2; eauto.
      econstructor 2; eauto.
Qed.

Lemma make_predecessors_list_norepet :
  forall jp,
    (forall p i, code ! p = Some i -> In jp (successors i) -> list_norepet (successors i)) ->
    list_norepet (make_preds !!! jp).
Proof.
  intros.
  unfold make_preds, make_predecessors.
  rewrite PTree.fold_spec.
  eapply make_predecessors_list_list_norepet; eauto.
  - eapply PTree.elements_keys_norepet; eauto.
  - unfold successors_list.
    rewrite PTree.gempty.
    constructor.
  - intros.
    unfold successors_list.
    rewrite PTree.gempty.
    intro Hcont. inv Hcont.
  - intros.
    eapply H; eauto.
    eapply PTree.elements_complete; eauto.
Qed.

End CORRECTNESS.

Section Pred_Succs.

Lemma same_successors_same_predecessors_aux0 {A B} :
  forall f1 (f2:B->list positive) (m1:PTree.t A) t a,
 (forall i, m1! i = None) ->
  PTree.xfold
    (fun pred pc instr => add_successors pred pc (f1 instr)) a m1 t = t.
Proof.
  induction m1; simpl; auto.
  intros a t T.
  generalize (T xH); destruct o; simpl; try congruence.
  intros _.
  rewrite IHm1_2.
  - rewrite IHm1_1; auto.
    intros i; generalize (T (xO i)); auto.
  - intros i; generalize (T (xI i)); auto.
Qed.

Lemma same_successors_same_predecessors_aux1 {A B} :
  forall f1 f2 (m1:PTree.t A) (m2:PTree.t B) t a,
 (forall i,
    (PTree.map1 f1 m1) ! i =
    (PTree.map1 f2 m2) ! i) ->
  PTree.xfold
    (fun pred pc instr => add_successors pred pc (f1 instr)) a m1 t =
  PTree.xfold
    (fun pred pc instr => add_successors pred pc (f2 instr)) a m2 t.
Proof.
  induction m1; simpl; auto; intros.
  - erewrite same_successors_same_predecessors_aux0; eauto.
    intros i; generalize (H i); simpl.
    rewrite PTree.gmap1.
    destruct (m2!i); simpl; auto.
    destruct i; simpl; congruence.
  - destruct m2.
    + erewrite same_successors_same_predecessors_aux0; eauto.
      erewrite same_successors_same_predecessors_aux0; eauto.
      erewrite same_successors_same_predecessors_aux0; eauto.
      generalize (H xH); destruct o; simpl; try congruence.
      destruct i; auto.
      intros i; generalize (H (xI i)); simpl.
      rewrite PTree.gmap1.
      destruct (m1_2!i); simpl; congruence.
      intros i; generalize (H (xO i)); simpl.
      rewrite PTree.gmap1.
      destruct (m1_1!i); simpl; congruence.
    + rewrite IHm1_1 with (m2:=m2_1); eauto.
      rewrite IHm1_2 with (m2:=m2_2); eauto.
      generalize (H xH).
      simpl.
      destruct o; destruct o0; simpl; try congruence.
      intros T; inv T.
      rewrite IHm1_2 with (m2:=m2_2); eauto.
      intros i; generalize (H (xI i)); simpl; auto.
      intros i; generalize (H (xI i)); simpl; auto.
      intros i; generalize (H (xO i)); simpl; auto.
Qed.

Lemma same_successors_same_predecessors {A B} : forall f1 f2 (m1:PTree.t A) (m2:PTree.t B),
 (forall i,
    (PTree.map1 f1 m1) ! i =
    (PTree.map1 f2 m2) ! i) ->
  make_predecessors m1 f1 = make_predecessors m2 f2.
Proof.
  unfold make_predecessors; intros.
  apply same_successors_same_predecessors_aux1; auto.
Qed.

End Pred_Succs.
