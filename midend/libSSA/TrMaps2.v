Require Import Coqlib.
Require Import Maps.

Lemma PTree_xfold_none : forall (A B:Type) (f:A->positive->B->A) (m:PTree.t B) (x:A) p',
    (forall p, PTree.get p m = None) ->
    PTree.xfold f p' m x = x.
Proof.
  induction m; intros; auto.
  simpl.
  rewrite IHm1; try rewrite IHm2; auto.
  destruct o; auto.
  - generalize (H 1%positive).
    Transparent PTree.get.
    simpl. congruence.
  - intros; generalize (H (xI p)); simpl; auto.
  - intros; generalize (H (xO p)); simpl; auto.
Qed.

Lemma PTree_xfold_same : forall (A B:Type) (f:A->positive->B->A) (m1 m2:PTree.t B) (x y:A) p',
    (forall p, m1!p = m2!p) ->
    x = y ->
    PTree.xfold f p' m1 x = PTree.xfold f p' m2 y.
Proof.
  induction m1; simpl; intros; auto.
  rewrite PTree_xfold_none; auto.
  intros p; rewrite <- H; auto.
  induction p; simpl; auto.
  subst; destruct m2.
  generalize (H xH); simpl; intros; subst.
  repeat rewrite PTree_xfold_none; auto.
  intros p; generalize (H (xO p)); simpl; auto.
  intros p; generalize (H (xI p)); simpl; auto.  
  generalize (H xH); simpl; intros; subst.
  destruct o0.
  apply IHm1_2.
  intros p; generalize (H (xI p)); simpl; auto.
  f_equal.
  apply IHm1_1; auto.
  intros p; generalize (H (xO p)); simpl; auto.
  apply IHm1_2.
  intros p; generalize (H (xI p)); simpl; auto.
  apply IHm1_1; auto.
  intros p; generalize (H (xO p)); simpl; auto.
Qed.

Set Implicit Arguments.

(* PTrees with pairs of positive as keys *)
Module P2Tree : TREE with Definition elt := (positive * positive)%type.

  Definition elt: Type := (positive * positive)%type.
  
  Definition elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Proof.
    decide equality.
    apply peq.
    apply peq.
  Defined.

  Definition t (A:Type) : Type := PTree.t (PTree.t A).

  Definition empty (A: Type) : t A := PTree.empty _.

  Definition get (A: Type) (a:elt) (m: t A) : option A :=
    let (a1,a2) := a in
      match PTree.get a1 m with
        | None => None
        | Some m => PTree.get a2 m
      end.

  Definition set (A: Type) (a:elt) (v: A) (m:t A) : t A :=
    let (a1,a2) := a in
      let m1 := match PTree.get a1 m with
                  | None => PTree.set a2 v (PTree.empty _)
                  | Some m1 => PTree.set a2 v m1
                end in
      PTree.set a1 m1 m.

  Definition remove (A: Type) (a:elt) (m:t A) : t A :=
    let (a1,a2) := a in
      let m1 := match PTree.get a1 m with
                  | None => PTree.empty _
                  | Some m1 => m1
                end in
      PTree.set a1 (PTree.remove a2 m1) m.

  (** The ``good variables'' properties for trees, expressing
    commutations between [get], [set] and [remove]. *)
  Lemma gempty:
    forall (A: Type) (i: elt), get i (empty A) = None.
  Proof.
    intros A [i1 i2]; unfold get, empty.
    rewrite PTree.gempty; auto.
  Qed.

  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = Some x.
  Proof.
    intros A [i1 i2] x m; unfold get, set.
    rewrite PTree.gss; auto.
    destruct (PTree.get i1 m).
    rewrite PTree.gss; auto.
    rewrite PTree.gss; auto.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] x m H; unfold get, set.
    destruct (PTree.elt_eq i1 j1); subst.
    rewrite PTree.gss; auto.
    destruct (PTree.get j1 m).
    rewrite PTree.gso; intuition congruence.
    rewrite PTree.gso; try intuition congruence.
    rewrite PTree.gempty; auto.
    rewrite PTree.gso; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then Some x else get i m.
  Proof.
    intros A i j x m.
    destruct (elt_eq i j); subst.
    apply gss.
    apply gso; auto.
  Qed.

  Lemma gsident:
    forall (A: Type) (i: elt) (m: t A) (v: A),
    get i m = Some v -> set i v m = m.
  Proof.
    intros A [i1 i2] m v; unfold get, set.
    case_eq (PTree.get i1 m); [intros m2 H2 H| intros H2 H].    
    apply PTree.gsident.
    rewrite PTree.gsident; auto.
    congruence.
  Qed.

  Lemma grs:
    forall (A: Type) (i: elt) (m: t A), get i (remove i m) = None.
  Proof.
    intros A [i1 i2] m; unfold get, remove.
    rewrite PTree.gss.
    rewrite PTree.grs; auto.
  Qed.

  Lemma gro:
    forall (A: Type) (i j: elt) (m: t A),
    i <> j -> get i (remove j m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] m H; unfold get, remove.
    destruct (PTree.elt_eq i1 j1); subst.
    rewrite PTree.gss.
    rewrite PTree.gro.
    destruct (PTree.get j1 m); auto.
    rewrite PTree.gempty; auto.
    congruence.
    rewrite PTree.gso; auto.
  Qed.

  Lemma grspec:
    forall (A: Type) (i j: elt) (m: t A),
    get i (remove j m) = if elt_eq i j then None else get i m.
  Proof.
    intros A i j m.
    destruct (elt_eq i j); subst.
    apply grs.
    apply gro; auto.
  Qed.

  (** Extensional equality between trees. *)
  Definition beq (A: Type) (f:A -> A -> bool) (m1 m2: t A) : bool :=
    let mb := PTree.combine
                (fun m'1 m'2 =>
                   match m'1, m'2 with
                     | Some m'1, Some m'2 => Some (PTree.beq f m'1 m'2)
                     | Some m'1, None => Some (PTree.beq f m'1 (PTree.empty _))
                     | None, Some m'2 => Some (PTree.beq f (PTree.empty _) m'2)
                     | None, None => None
                   end)
                m1 m2
    in PTree.fold (fun x _ y => y && x) mb true.

  Lemma beq_correct:
    forall (A: Type) (eqA: A -> A -> bool) (t1 t2: t A),
    beq eqA t1 t2 = true <->
    (forall (x: elt),
     match get x t1, get x t2 with
     | None, None => True
     | Some y1, Some y2 => eqA y1 y2 = true
     | _, _ => False
    end).
  Proof.
    intros A eqA t1 t2. unfold get, beq.
    rewrite PTree.fold_spec.
    rewrite <- fold_left_rev_right.
    unfold fold_right. fold (forallb (snd (A:=positive))).
    rewrite forallb_forall.
    setoid_rewrite <- (in_rev).
    assert (forall (A B:Type) (P:A*B->Prop), (forall p, P p) <-> (forall a b, P (a, b))) by intuition.
    rewrite H. clear H.
    setoid_rewrite (fun A m i v => conj (@PTree.elements_complete A m i v) (@PTree.elements_correct A m i v) : _ <-> _).
    setoid_rewrite (@PTree.gcombine _ _ _ _ eq_refl).
    split.
    - intros H [x1 x2]. specialize (H x1 false). simpl in H.
      destruct (PTree.get); destruct (PTree.get).
      + apply PTree.beq_correct. destruct (PTree.beq eqA t0 t3); auto.
      + assert (PTree.beq eqA t0 (PTree.empty A) = true) by (destruct PTree.beq; auto).
        rewrite PTree.beq_correct in H0. specialize (H0 x2). rewrite (PTree.gempty) in H0. trivial.
      + assert (PTree.beq eqA (PTree.empty A) t0 = true).
        { simpl; destruct PTree.bempty; auto. }
        rewrite PTree.beq_correct in H0. specialize (H0 x2). rewrite (PTree.gempty) in H0. trivial.
      + trivial.
    - intros H x1 []. trivial.
      pose proof (fun x => H (x1, x)). clear H. simpl in H0.
      destruct (PTree.get); destruct (PTree.get).
      + rewrite <- PTree.beq_correct in H0. congruence.
      + assert (PTree.beq eqA t0 (PTree.empty A) = true).
        rewrite PTree.beq_correct. intro. rewrite PTree.gempty. apply H0.
        congruence.
      + assert (PTree.beq eqA (PTree.empty A) t0 = true).
        rewrite PTree.beq_correct. intro. rewrite PTree.gempty. apply H0.
        congruence.
      + congruence.
  Qed.

  (** Applying a function to all data of a tree. *)
  Definition map (A B: Type) (f: elt -> A -> B) (m:t A) : t B :=
    PTree.map (fun a1 => PTree.map (fun a2 => f (a1,a2))) m.

  Lemma gmap:
    forall (A B: Type) (f: elt -> A -> B) (i: elt) (m: t A),
    get i (map f m) = option_map (f i) (get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map.
    rewrite PTree.gmap.
    case_eq (PTree.get i1 m); intros; simpl; auto.
    rewrite PTree.gmap; auto.
  Qed.

  (** Same as [map], but the function does not receive the [elt] argument. *)
  Definition map1 (A B: Type) (f:A -> B) (m:t A) : t B :=
    PTree.map1 (PTree.map1 f) m.

  Lemma gmap1:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map1 f m) = option_map f (get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map1.
    rewrite PTree.gmap1.
    case_eq (PTree.get i1 m); intros; simpl; auto.
    rewrite PTree.gmap1; auto.
  Qed.

  (** Applying a function pairwise to all data of two trees. *)
  Definition combine (A B C: Type) (f:option A -> option B -> option C) (m1:t A) (m2:t B) : t C :=
    PTree.combine (fun om1 om2 =>
      match om1, om2 with
        | None, None => None
        | None, Some m2 => Some (PTree.combine f (@PTree.empty _) m2)
        | Some m2, None => Some (PTree.combine f m2 (@PTree.empty _))
        | Some m1, Some m2 => Some (PTree.combine f m1 m2)
      end) m1 m2.

  Lemma gcombine:
    forall (A B C: Type) (f: option A -> option B -> option C),
    f None None = None ->
    forall (m1: t A) (m2: t B) (i: elt),
    get i (combine f m1 m2) = f (get i m1) (get i m2).
  Proof.
    intros A B C f Hf m1 m2 [i1 i2]; unfold get, combine.
    Opaque PTree.gcombine  PTree.get PTree.set PTree.empty PTree.bempty.
    rewrite PTree.gcombine; auto. 
    case_eq (PTree.get i1 m1); intros; simpl; auto.
    case_eq (PTree.get i1 m2); intros; simpl; auto.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gempty; auto.
    case_eq (PTree.get i1 m2); intros; simpl; auto.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gempty; auto.
  Qed.

  Lemma combine_commut:
    forall (A B: Type) (f g: option A -> option A -> option B),
    (forall (i j: option A), f i j = g j i) ->
    forall (m1 m2: t A),
    combine f m1 m2 = combine g m2 m1.
  Proof.
    intros A B f g Hf m1 m2; unfold get, combine.
    apply PTree.combine_commut.
    clear m1 m2; intros m1 m2.
    destruct m1; destruct m2; auto; apply f_equal.
    apply PTree.combine_commut; auto.
    apply PTree.combine_commut; auto.
    apply PTree.combine_commut; auto.
  Qed.

  (** Enumerating the bindings of a tree. *)
  Fixpoint xelements (A : Type) (m : t A) (i : positive)
           (k: list (positive * positive * A)) {struct m} : list (positive * positive * A) :=
    match m with
    | PTree.Leaf => k
    | PTree.Node l None r =>
      xelements l (xO i) (xelements r (xI i) k)
    | PTree.Node l (Some x) r =>
      let elmts := PTree.fold
                     (fun l x2 a => ((PTree.prev i, x2),a)::l) x (@nil _) in
      xelements l (xO i) (elmts ++ xelements r (xI i) k)
    end.

  Definition elements (A: Type) (m : t A) := xelements m xH nil.

  Remark xelements_append:
    forall A (m: t A) i k1 k2,
      xelements m i (k1 ++ k2) = xelements m i k1 ++ k2.
  Proof.
    induction m; intros; simpl.
    - auto.
    - destruct o; rewrite IHm2.
      + rewrite <- IHm1; auto.
        rewrite app_assoc. auto.
      + rewrite <- IHm1; auto.
  Qed.

  Remark xelements_leaf:
    forall A i, xelements (@PTree.Leaf (PTree.t A)) i nil = nil.
  Proof.
    intros; reflexivity.
  Qed.

  Remark xelements_node:
    forall A (m1: t A) o (m2: t A) i,
      xelements (PTree.Node m1 o m2) i nil =
      xelements m1 (xO i) nil
                ++ match o with None => nil | Some v => PTree.fold
                     (fun l x2 a => ((PTree.prev i, x2),a)::l) v (@nil _)    end
                ++ xelements m2 (xI i) nil.
  Proof.
    intros. simpl. destruct o; simpl; rewrite <- xelements_append; auto.
  Qed.

  Lemma xelements_incl:
    forall (A: Type) (m: t A) (i : positive) k x,
      In x k -> In x (xelements m i k).
  Proof.
    induction m; intros; simpl.
    - auto.
    - destruct o.
      + apply IHm1.
        apply in_app. right. auto.
      + auto. 
  Qed.

  Lemma gleaf : forall (A: Type) (i1 i2: positive), @get A (i1,i2) PTree.Leaf = None.
  Proof.
    intros. simpl.
    rewrite PTree.gleaf. auto.
  Qed.

  Lemma fold_left_acc_in {A B: Type}: forall (f: A -> B) (l: list A) k res, 

      fold_left (fun (res : list B) (i : A) => (f i)::res) l k = res ->
      forall (i : B), In i k -> In i res.
  Proof. 
    induction l ; intros.
    - simpl in H. subst. auto.
    - simpl in H. eapply IHl ; eauto.
      right; auto.
  Qed.
  
  Lemma fold_left_acc {A B: Type}: forall (f: A -> B) (l: list A) k res, 

      fold_left (fun (res : list B) (i : A) => (f i)::res) l k = res ->
      forall (i : A), In i l -> In (f i) res .
  Proof. 
    induction l ; intros.
    - inv H0.
    - inv H0.
      + simpl.
        eapply fold_left_acc_in; eauto.
        left; auto.
      + simpl. eapply IHl; eauto.
  Qed. 

  Lemma in_fold_left_acc {A B: Type}: forall (f: A -> B) (l: list A) k res, 

      fold_left (fun (res : list B) (i : A) => (f i)::res) l k = res ->
      forall (i : B), In i res -> In i k \/ exists j, In j l /\ i = f j.
  Proof. 
    induction l ; intros.
    - simpl in H. subst. auto. 
    - simpl in H. 
      exploit IHl; eauto. intros [P | P].
      + inv P.
        * right. exists a; split; try left ; auto. 
        * auto.
      + right. inv P. inv H1. exists x ; split; try right; auto. 
  Qed. 

  Lemma xelements_correct:
    forall (A: Type) (m: t A) (i1 i2 j : positive) (v: A) k,
      get (i1,i2) m = Some v -> In (PTree.prev (PTree.prev_append i1 j), i2, v) (xelements m j k).
  Proof.
    induction m; intros.
    - rewrite gleaf in H. congruence.
    - destruct o.
      + Transparent PTree.get.
        destruct i1; simpl; simpl in H. 
        * case_eq (m2 ! i1) ; intros; rewrite H0 in *; try congruence.
          apply xelements_incl.
          apply in_app. right.
          apply IHm2; eauto.
          simpl. rewrite H0. auto.
        * apply IHm1; eauto. 
        * apply xelements_incl.
          apply in_app. left.
          clear IHm1 IHm2.
          rewrite PTree.fold_spec.
          set (f:= fun (p: positive * A) => (PTree.prev j, fst p, snd p)) in *.
          replace (PTree.prev j, i2, v) with (f (i2,v)) by auto.
          eapply fold_left_acc ; eauto.
          eapply PTree.elements_correct; eauto.
      + Transparent PTree.get.
        destruct i1; simpl; simpl in H.
        * case_eq (m2 ! i1) ; intros; rewrite H0 in *; try congruence.
          apply xelements_incl.
          apply IHm2; eauto.
          simpl. rewrite H0. auto.
        * apply IHm1; eauto. 
        * congruence. 
  Qed.

  Lemma elements_correct:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    get i m = Some v -> In (i, v) (elements m).
  Proof.
    unfold elements; intros A m [i1 i2] v Hin.
    replace i1 with (PTree.prev_append 1 i1) by auto.
    rewrite <- PTree.prev_append_prev. 
    eapply xelements_correct ; eauto.
  Qed.

  Lemma in_xelements:
    forall (A: Type) (m: t A) (i1 i2 k: positive) (v: A) ,
    In (i1, i2, v) (xelements m k nil) ->
    exists j, i1 = PTree.prev (PTree.prev_append j k) /\ get (j,i2) m = Some v.
  Proof.
    induction m; intros.
  - rewrite xelements_leaf in H. contradiction.
  - rewrite xelements_node in H.
    rewrite ! in_app_iff in H.
    destruct H as [P | [P | P]].
    + exploit IHm1; eauto. intros (j & Q & R).
      exists (xO j); split; auto.
    + destruct o; simpl in P; intuition auto.
      rewrite PTree.fold_spec in P.
      set (f:= fun (p: positive * A) => (PTree.prev k, fst p, snd p)) in *.
      eapply in_fold_left_acc with (f0:= f) in P ; eauto.
      inv P; inv H. inv H0.
      unfold f in H1. inv H1.
      exists xH; split; auto.
      simpl. eapply PTree.elements_complete; eauto.
      destruct x ; auto.
    + exploit IHm2; eauto. intros (j & Q & R). exists (xI j); auto.
  Qed.

  Theorem elements_complete:
    forall (A: Type) (m: t A) (i: elt) (v: A),
    In (i, v) (elements m) -> get i m = Some v.
  Proof.
    unfold elements. intros A m [i1 i2] v H. exploit in_xelements; eauto. intros (j & P & Q).
    rewrite PTree.prev_append_prev in P. change i1 with (PTree.prev_append 1 i1) in P.
    exploit PTree.prev_append_inj; eauto. simpl snd in *. intros; congruence.
  Qed.
  
  Remark list_norepet_map:
    forall (A B: Type) (f: A -> B) (l: list A),
      list_norepet (List.map f l) -> list_norepet l.
  Proof.
    induction l; simpl; intros.
    constructor.
    inv H. constructor; auto. red; intros; elim H2. apply List.in_map; auto.
  Qed.

  Definition xkeys (A: Type) (m: t A) (i: positive) :=
    List.map (@fst (positive * positive) A) (xelements m i nil).

  Remark xkeys_leaf:
    forall A i, xkeys (@PTree.Leaf (PTree.t A)) i = nil.
  Proof.
    intros; reflexivity.
  Qed.

  Remark xkeys_node:
    forall A (m1: t A) o (m2: t A) i,
      xkeys (PTree.Node m1 o m2) i =
      xkeys m1 (xO i)
            ++ match o with None => nil | Some v =>
                                          List.map (@fst (positive * positive) A)
                                                   (PTree.fold
                                                      (fun l x2 a => ((PTree.prev i, x2),a)::l) v (@nil _))
               end
            ++ xkeys m2 (xI i).
  Proof.
    intros. unfold xkeys. rewrite xelements_node. rewrite ! map_app. destruct o; auto.
  Qed.

  Lemma in_xkeys:
    forall (A: Type) (m: t A) (i k1 k2: positive),
      In (k1,k2) (xkeys m i) ->
      (exists j, k1 = PTree.prev (PTree.prev_append j i)).
  Proof.
    unfold xkeys; intros.
    apply (list_in_map_inv) in H. destruct H as (((j1, j2), v) & H0 & H).
    simpl in *. inv H0. 
    exploit in_xelements; eauto. intros (k & P & Q). exists k; auto.
  Qed.

  Lemma in_fold_left_acc_map {A B: Type}: forall (f: A -> B) (l: list A) k, 
      fold_left (fun (res : list B) (i : A) => (f i)::res) l k = (rev (List.map f l)) ++ k.
  Proof. 
    induction l ; simpl; intros.
    - auto. 
    - simpl.
      rewrite IHl; eauto.
      rewrite app_ass. auto.
  Qed.

  Lemma rev_no_repet : forall (A: Type) (l:list A),
      list_norepet l ->
      list_norepet (rev l).
  Proof.
    induction l ; intros; auto.
    simpl. inv H.
    apply list_norepet_app; repeat split; auto.
    - constructor; auto.
      apply list_norepet_nil.
    - red ; intros. inv H0; auto.
      intro Hcont; subst.
      elim H2; apply in_rev; auto.
  Qed.

  Lemma list_disjoint_app : forall (A: Type) (l1 l2 l3: list A),
      list_disjoint l1 l3 ->
      list_disjoint l2 l3 -> 
      list_disjoint (l1 ++ l2) l3.
  Proof.
    induction l1 ; intros; simpl; auto.
    red ; intros.
    intro; subst.
    inv H1.
    - eelim H; eauto. left; auto.
    - apply in_app in H3. inv H3.
      + eelim H ; eauto. right; auto.
      + eelim H0; eauto. 
  Qed.

  Lemma list_disjoint_rev : forall (A: Type) (l1 l2: list A),
      list_disjoint l1 l2 ->
      list_disjoint (rev l1) l2.
  Proof.
    induction l1 ; intros; auto.
    simpl. red; intros.
    intro Hcont; subst.
    apply in_app in H0. inv H0.
    eelim H; eauto.
    - right; auto. apply in_rev; auto.
    - inv H2; auto. eelim H; eauto. left; auto.
  Qed.

  Lemma list_norepet_map_fst : forall A i0 t0 p,
  list_norepet
    (List.map (fun x : positive * A => (PTree.prev i0, fst x)) (PTree.xelements t0 p nil)).
  Proof.
    unfold PTree.elements.
    induction t0; intros ; auto.
    - simpl; apply list_norepet_nil.
    - rewrite PTree.xelements_node.
      destruct o ; simpl.
      + repeat rewrite map_app.
        repeat apply list_norepet_append; auto.
        * simpl.
          constructor; eauto.
          intro Hcont. apply in_map_iff in Hcont; eauto.
          inv Hcont. inv H. inv H0.
          destruct x.
          apply PTree.in_xelements in H1.
          inv H1. inv H. simpl in *.
          rewrite PTree.prev_append_prev in H2.
          simpl in H2.
          unfold PTree.prev in *.
          apply PTree.prev_append_inj in H2; congruence.
          
        * simpl.
          { red; intros. inv H0.
            - intro Hcont. subst.
              apply in_map_iff in H; eauto.
              inv H. inv H0. inv H.
              destruct x.
              apply PTree.in_xelements in H1.
              inv H1. inv H. simpl in *.
              rewrite PTree.prev_append_prev in H2.
              simpl in H2. 
              unfold PTree.prev in *.
              apply PTree.prev_append_inj in H2; congruence.
            - intro Hcont; subst.
              apply in_map_iff in H; eauto.
              apply in_map_iff in H1; eauto.
              inv H. inv H0.
              inv H1. inv H.
              inv H0.
              destruct x, x0.
              apply PTree.in_xelements in H1.
              apply PTree.in_xelements in H2.
              inv H1. inv H. simpl in *.
              inv H2. inv H.
              repeat rewrite PTree.prev_append_prev in H0.
              simpl in H0.
              apply PTree.prev_append_inj in H0; congruence.
          }
      + repeat rewrite map_app.
        repeat apply list_norepet_append; auto.
        red; intros. intro Hcont; subst.
        apply in_map_iff in H; eauto.
        apply in_map_iff in H0; eauto.
        inv H. inv H0.
        inv H1. inv H.
        inv H0.
        destruct x, x0.
        apply PTree.in_xelements in H1.
        apply PTree.in_xelements in H2.
        inv H1. inv H. simpl in *.
        inv H2. inv H.
        repeat rewrite PTree.prev_append_prev in H0.
        simpl in H0.
        apply PTree.prev_append_inj in H0; congruence.
  Qed.

  Lemma disjoint_map_fst : 
  forall A l (t1 : PTree.t A) (p i : positive),
  (forall j : positive, ~ In (PTree.prev i, j) l) ->
  list_disjoint
    (List.map (fun x : positive * A => (PTree.prev i, fst x)) (PTree.xelements t1 p nil))
    l.
  Proof.
    induction t1; intros ; auto.
    - simpl; red ; intros ; auto. 
    - rewrite PTree.xelements_node.
      destruct o ; simpl.
      + repeat rewrite map_app.
        apply list_disjoint_app; auto.
        simpl. red ; intros.
        intro ; subst.
        inv H0.
        * eelim H; eauto.
        * apply in_map_iff in H2.
          inv H2. inv H0.
          destruct x. simpl in *.
          eelim H; eauto.
      + repeat rewrite map_app.
        apply list_disjoint_app; eauto.
  Qed.
  
  Lemma xelements_keys_norepet:
    forall (A: Type) (m: t A) (i: positive),
      list_norepet (xkeys m i).
  Proof.
    induction m; intros.
    - rewrite xkeys_leaf; constructor.
    - assert (NOTIN1: forall j, ~ In ((PTree.prev i), j) (xkeys m1 (xO i))).
      { red; intros. exploit in_xkeys; eauto. intros (j0 & EQ).
        rewrite PTree.prev_append_prev in EQ. simpl in EQ.
        apply PTree.prev_append_inj in EQ. discriminate. }
      assert (NOTIN2: forall j, ~ In ((PTree.prev i), j) (xkeys m2 (xI i))).
      { red; intros. exploit in_xkeys; eauto. intros (j0 & EQ).
        rewrite PTree.prev_append_prev in EQ. simpl in EQ.
        apply PTree.prev_append_inj in EQ. discriminate. }
      assert (DISJ: forall x1 x2, In (x1,x2) (xkeys m1 (xO i)) -> In (x1,x2) (xkeys m2 (xI i)) -> False).
      { intros. exploit in_xkeys. eexact H. intros (j1 & EQ1).
        exploit in_xkeys. eexact H0. intros (j2 & EQ2).
        rewrite PTree.prev_append_prev in *. simpl in *. rewrite EQ2 in EQ1.
        apply PTree.prev_append_inj in EQ1. discriminate. }
      rewrite xkeys_node. apply list_norepet_append.
      + auto.
      + apply list_norepet_append; auto.
        * destruct o; simpl; try constructor.
          rewrite PTree.fold_spec.
          rewrite in_fold_left_acc_map. 
          rewrite <- map_rev. rewrite <- app_nil_end.
          rewrite map_map.
          rewrite map_rev.          
          apply rev_no_repet. simpl.
          apply list_norepet_map_fst.
            
        * destruct o ; simpl.
          { 
            rewrite PTree.fold_spec.
            rewrite in_fold_left_acc_map ; eauto.
            rewrite <- map_rev. rewrite <- app_nil_end.
            rewrite map_map.
            rewrite map_rev.          
            apply list_disjoint_rev.
            simpl. apply disjoint_map_fst; auto.
          }
          { red ; intros; auto. }
      + destruct o; simpl; try constructor.
          rewrite PTree.fold_spec.
          rewrite in_fold_left_acc_map. 
          rewrite <- map_rev. rewrite <- app_nil_end.
          rewrite map_map.
          rewrite map_rev.
          apply list_disjoint_sym.
          apply list_disjoint_app.
          apply list_disjoint_rev.
          simpl.
          { apply disjoint_map_fst; auto. }
          { red; intros (x1,y1) (x2,y2) Hin1 Hin2 Hcont; inv Hcont; eauto. }
          { red; intros (x1,y1) (x2,y2) Hin1 Hin2 Hcont; inv Hcont; eauto. }
  Qed.            
   
  Theorem elements_keys_norepet:
    forall (A: Type) (m: t A),
    list_norepet (List.map (@fst elt A) (elements m)).
  Proof.
    intros. apply (xelements_keys_norepet m xH).
  Qed.

  Lemma get_node_none : forall A (t0: PTree.t A) m1 m2,
      (forall  i1 i2, get (i1,i2) (PTree.Node m1 (Some t0) m2) = None) ->
      forall i2, PTree.get i2 t0 = None.
  Proof.
    induction t0; intros; simpl.
    - apply PTree.gleaf.
    - specialize (H xH i2).
      simpl in H. auto.
  Qed.

  Remark xelements_empty:
    forall (A: Type) (m: t A) i, (forall i, get i m = None) -> xelements m i nil = nil.
  Proof.
    induction m; intros.
    - auto.
    - rewrite xelements_node.
      rewrite IHm1, IHm2; simpl.
      + destruct o; auto.
        rewrite <- app_nil_end.
        rewrite PTree.fold_spec.
        replace (PTree.elements t0) with (@nil (positive * A)); auto.
        unfold PTree.elements.
        rewrite PTree.xelements_empty; auto.
        eapply get_node_none; eauto.
      + intros (i1,j1). apply (H (xI i1,j1)).
      + intros (i1,j1). apply (H (xO i1,j1)).
  Qed. 

  Lemma option_rel_Some_None_elim : forall (A B:Type) (R: A -> B -> Prop)  (m1 m2: t A) t0 n1 n2,
  (forall i : elt,
    option_rel R (get i (PTree.Node m1 (Some t0) m2)) (get i (PTree.Node n1 None n2))) ->
    (forall i, t0 ! i = None).
  Proof.
    intros.
    specialize (H (xH,i)).
    inv H.
    destruct t0; auto.
  Qed.

  Lemma option_rel_None_Some_elim : forall (A B:Type) (R: A -> B -> Prop)  (m1 m2: t A) t0 n1 n2,
  (forall i : elt,
    option_rel R (get i (PTree.Node m1 None m2)) (get i (PTree.Node n1 (Some t0) n2))) ->
    (forall i, t0 ! i = None).
  Proof.
    intros.
    specialize (H (xH,i)).
    inv H.
    destruct t0; auto.
  Qed.

  Lemma option_rel_Some_Some_elim : forall (A B:Type) (R: A -> B -> Prop)  (m1 m2: t A) t0 t1 n1 n2,
  (forall i : elt,
    option_rel R (get i (PTree.Node m1 (Some t0) m2)) (get i (PTree.Node n1 (Some t1) n2))) ->
    (forall i, option_rel R (t0 ! i) (t1 ! i)).
  Proof.
    intros.
    specialize (H (xH,i)).
    inv H.
    destruct t0; auto; constructor.
    constructor; auto.
  Qed.

  Lemma list_forall2_rev : forall (A B: Type) (R: A -> B -> Prop) l1 l2,
      list_forall2 R l1 l2 ->
      list_forall2 R (rev l1) (rev l2).
  Proof.
    induction 1 ; intros.
    - simpl; auto. constructor.
    - simpl. apply list_forall2_app; auto.
      repeat constructor; auto.
  Qed.

  Lemma list_forall2_map : forall A B f (R : A -> B -> Prop) l1 l2 ,
      let RR := (fun (i_x : positive * positive * A) (i_y : positive * positive * B) =>
                   fst i_x = fst i_y /\ R (snd i_x) (snd i_y)) in
      let RR0 := (fun (i_x : positive * A) (i_y : positive * B) =>
                    fst i_x = fst i_y /\ R (snd i_x) (snd i_y)) in
      (forall a b, RR0 a b -> RR (f A a) (f B b)) ->
      list_forall2 RR0 l1 l2 ->
      list_forall2 RR (List.map (f A) l1) (List.map (f B) l2).
  Proof.
    intros A B f R.
    induction 2 ; intros.
    - simpl; auto. constructor.
    - simpl. constructor; auto.
  Qed.
              
  Theorem elements_canonical_order':
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
      (forall i, option_rel R (get i m) (get i n)) ->
      list_forall2
        (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
        (elements m) (elements n).
  Proof.
    intros until n. unfold elements. generalize 1%positive. revert m n.
    induction m; intros.
    - simpl. rewrite xelements_empty. constructor.
      intros. specialize (H i). rewrite gempty in H. inv H; auto.
    - destruct n as [ | n1 o' n2 ].
      + rewrite (xelements_empty (PTree.Node m1 o m2)). simpl; constructor.
        intros. specialize (H i). rewrite gempty in H. inv H; auto.
      + rewrite ! xelements_node. repeat apply list_forall2_app.
        * apply IHm1. intros (i,j). apply (H (xO i,j)).
        * { destruct o, o' ; simpl; try solve [constructor].
            - rewrite PTree.fold_spec.
              rewrite PTree.fold_spec.
              set (f:= fun A (x: positive * A) => (PTree.prev p, fst x, snd x)) in *.
              rewrite in_fold_left_acc_map with (f0:= f A) ; eauto.
              rewrite in_fold_left_acc_map with (f0:= f B) ; eauto.
              repeat rewrite <- app_nil_end.
              apply list_forall2_rev.
              eapply list_forall2_map ; eauto.
              + unfold f ; intros.
                inv H0; split; simpl; auto.
                congruence.
              + eapply PTree.elements_canonical_order'; eauto.
                eapply option_rel_Some_Some_elim; eauto.
            - rewrite PTree.fold_spec.
              replace (PTree.elements t0) with (@nil (positive * A)).
              + simpl. constructor.
              + unfold PTree.elements.
                rewrite PTree.xelements_empty; auto.
                eapply option_rel_Some_None_elim; eauto.
            - rewrite PTree.fold_spec.
              replace (PTree.elements t0) with (@nil (positive * B)).
              + simpl. constructor.
              + unfold PTree.elements.
                rewrite PTree.xelements_empty; auto.
                eapply option_rel_None_Some_elim; eauto.
          }                
        * apply IHm2. intros (i,j). apply (H (xI i,j)).
  Qed. 

  Theorem elements_canonical_order:
    forall (A B: Type) (R: A -> B -> Prop) (m: t A) (n: t B),
      (forall i x, get i m = Some x -> exists y, get i n = Some y /\ R x y) ->
      (forall i y, get i n = Some y -> exists x, get i m = Some x /\ R x y) ->
      list_forall2
        (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
        (elements m) (elements n).
  Proof.
    intros. apply elements_canonical_order'.
    intros. destruct (get i m) as [x|] eqn:GM.
    exploit H; eauto. intros (y & P & Q). rewrite P; constructor; auto.
    destruct (get i n) as [y|] eqn:GN.
    exploit H0; eauto. intros (x & P & Q). congruence.
    constructor.
  Qed.

  Theorem elements_extensional:
    forall (A: Type) (m n: t A),
      (forall i, get i m = get i n) ->
      elements m = elements n.
  Proof.
    intros.
    exploit (@elements_canonical_order' _ _ (fun (x y: A) => x = y) m n).
    intros. rewrite H. destruct (get i n); constructor; auto.
    induction 1. auto. destruct a1 as [a2 a3]; destruct b1 as [b2 b3]; simpl in *.
    destruct H0. congruence.
  Qed.

  Lemma fold_left_acc_k : forall (A B : Type) (f : A -> B) (l : list A) (k : list B),
      fold_left (fun acc i => (f i) :: acc) l k = (fold_left (fun k i => f i :: k) l nil) ++ k.
  Proof.
    induction l ; intros; auto.
    simpl.
    rewrite  IHl; auto.
    symmetry.
    rewrite IHl; auto.
    rewrite app_ass. simpl. auto.
  Qed.

  Lemma xelements_remove:
    forall (A: Type) v (m: t A) i1 i2 j,
      get (i1,i2) m = Some v ->
      exists l1 l2,
        xelements m j nil = l1 ++ (PTree.prev (PTree.prev_append i1 j), i2, v) :: l2
        /\ xelements (remove (i1,i2) m) j nil = l1 ++ l2.
  Proof.
    induction m; intros.
    - rewrite gleaf in H; discriminate.
    - Transparent PTree.set.
      assert (REMOVE: xelements (remove (i1,i2) (PTree.Node m1 o m2)) j nil =
                      xelements (match i1 with
                                 | xH => PTree.Node m1
                                                    (match o with
                                                     | None => None
                                                     | Some t => Some (PTree.remove i2 t)
                                                     end)
                                                    m2
                                 | xO ii => PTree.Node (remove (ii,i2) m1) o m2
                                 | xI ii => PTree.Node m1 o (remove (ii,i2) m2) end)
                                j nil).
      {
      destruct i1; simpl remove.
      - destruct m1; auto.
      - auto.
      - destruct o; auto.
        inv H.
    }
      rewrite REMOVE. destruct i1; simpl in H.
      + assert (GET : get (i1, i2) m2 = Some v) by auto.
        destruct (IHm2 i1 i2 (xI j) GET) as (l1 & l2 & EQ & EQ').
        exists (xelements m1 (xO j) nil ++
                          match o with None => nil | Some x =>
                                                     PTree.fold
          (fun (l0 : list (positive * positive * A)) (x2 : positive) (a : A) => (PTree.prev j, x2, a) :: l0) x
          nil
                          end ++ l1).
        exists l2; split.
        * rewrite xelements_node, EQ, ! app_ass; auto.
        * rewrite xelements_node, EQ', ! app_ass. auto.          
    + assert (GET : get (i1, i2) m1 = Some v) by auto.
      destruct (IHm1 i1 i2 (xO j) GET) as (l1 & l2 & EQ & EQ').
      exists l1;
      exists (l2 ++
                 match o with
                   None => nil
                 | Some x =>
                   PTree.fold
          (fun (l0 : list (positive * positive * A)) (x2 : positive) (a : A) => (PTree.prev j, x2, a) :: l0) x
          nil
                 end ++
              xelements m2 (xI j) nil);
      split.
      rewrite xelements_node, EQ, ! app_ass. auto.
      rewrite xelements_node, EQ', ! app_ass. auto.
    + simpl PTree.prev_append.
      rewrite ! xelements_node; auto.
      destruct o ; try congruence.
      rewrite ! PTree.fold_spec.
      generalize H ; intros GET.
      apply PTree.elements_remove in H. destruct H as [l1 [l2 [EQ1 EQ2]]].
      rewrite EQ1, EQ2.
      rewrite ! fold_left_app.
      simpl.
      set (F:= (fun (a : list (positive * positive * A)) (p : positive * A) => (PTree.prev j, fst p, snd p) :: a)) in *.
      simpl.
      unfold F at 1.
      rewrite fold_left_acc_k.
      rewrite app_ass.
      fold F.
      unfold F at 3. rewrite fold_left_acc_k.
      fold F.
      rewrite ! app_ass.
      simpl.
      exists (xelements m1 j~0 nil ++ fold_left F l2 nil).
      rewrite <- app_ass.
      exists (fold_left F l1 nil ++ xelements m2 j~1 nil).
      split; auto.
      rewrite <- app_ass.
      auto.
  Qed.  
  
  Theorem elements_remove:
    forall (A: Type) i v (m: t A),
    get i m = Some v ->
    exists l1 l2, elements m = l1 ++ (i,v) :: l2 /\ elements (remove i m) = l1 ++ l2.
  Proof.
    intros A (i,j) v m Hget.
    exploit xelements_remove. eauto. instantiate (1 := xH).
    rewrite PTree.prev_append_prev. auto.
  Qed.

  Fixpoint xfold (A B: Type) (f: B -> elt -> A -> B)
           (i: positive) (m: t A) (v: B) {struct m} : B :=
    match m with
    | PTree.Leaf => v
    | PTree.Node l None r =>
      let v1 := xfold f (xO i) l v in
      xfold f (xI i) r v1
    | PTree.Node l (Some x) r =>
      let v1 := xfold f (xO i) l v in
      let v2 := fold_left (fun k j => f k ((PTree.prev i), (fst j)) (snd j)) (rev (PTree.elements x)) v1 in
      xfold f (xI i) r v2
    end. 

  Definition fold (A B : Type) (f: B -> elt -> A -> B) (m: t A) (v: B) :=
    xfold f xH m v.

  Lemma fold_left_PTree_fold_glue : forall (A B: Type) (f: B -> elt -> A -> B) e l k,
      
      fold_left (fun (k : B) (j0 : positive * A) => f k (e, fst j0) (snd j0)) 
                (rev l)
                k
      =
      fold_left (fun (a : B) (p : elt * A) => f a (fst p) (snd p))
                (rev (List.map (fun i : positive * A => (e, fst i, snd i)) l))
                k.
  Proof.
    intros.
    rewrite <- fold_left_rev_right.
    rewrite <- fold_left_rev_right.
    rewrite ! rev_involutive.
    revert k.
    induction l ; intros; auto.
    simpl.
    rewrite IHl ; eauto.
  Qed.
    
  Lemma xfold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (m: t A) (v: B) j,
    xfold f j m v =
    List.fold_left (fun a p => f a (fst p) (snd p)) (xelements m j nil) v.
  Proof.
    induction m ; intros.
    - simpl. auto.
    - rewrite xelements_node.
      destruct o ; simpl.
      + set (F:= fun (a : B) (p : elt * A) => f a (fst p) (snd p)) in *.
        rewrite IHm1. rewrite IHm2.
        rewrite ! fold_left_app.
        rewrite ! PTree.fold_spec.
        rewrite in_fold_left_acc_map.
        rewrite <- app_nil_end.
        rewrite fold_left_PTree_fold_glue. auto.
      + rewrite IHm1. rewrite IHm2.
        rewrite <- fold_left_app. auto.
  Qed.

  Theorem fold_spec:
    forall (A B: Type) (f: B -> elt -> A -> B) (v: B) (m: t A),
      fold f m v =
      List.fold_left (fun a p => f a (fst p) (snd p)) (elements m) v.
  Proof.
    intros.
    apply xfold_spec. 
  Qed.

  Fixpoint fold1 (A B: Type) (f: B -> A -> B) (m: t A) (v:B) : B :=
    match m with
    | PTree.Leaf => v
    | PTree.Node l None r =>
        let v1 := fold1 f l v in
        fold1 f r v1
    | PTree.Node l (Some x) r =>
        let v1 := fold1 f l v in
        let v2 := fold_left (fun k j => f k (snd j)) (rev (PTree.elements x)) v1 in
        fold1 f r v2
    end.

  Lemma glue2 : forall (A B: Type) (f: B -> A -> B) e l k,
      (fold_left (fun (k : B) (j : positive * A) => f k (snd j))
                 (rev l) k) =
      fold_left  (fun (a : B) (p : positive * positive * A) => f a (snd p))
                 (rev (List.map (fun i0 : positive * A => (e, fst i0, snd i0)) l))
                 k.
  Proof.
    intros.
    rewrite <- fold_left_rev_right.
    rewrite <- fold_left_rev_right.
    rewrite ! rev_involutive.
    revert k.
    induction l ; intros; auto.
    simpl.
    rewrite IHl ; eauto.
  Qed.

  Lemma fold1_xelements: forall (A B: Type) (f: B -> A -> B) m i v l,
    List.fold_left (fun a p => f a (snd p)) l (fold1 f m v) =
    List.fold_left (fun a p => f a (snd p)) (xelements m i l) v.
  Proof.
    induction m; intros.
    simpl. auto.
    destruct o; simpl.
    - rewrite <- IHm1.
      rewrite fold_left_app.
      rewrite <- IHm2.
      rewrite PTree.fold_spec.
      rewrite in_fold_left_acc_map.
      rewrite <- app_nil_end.
      erewrite glue2; auto.
    - rewrite <- IHm1. rewrite <- IHm2. auto.
  Qed.

  Lemma fold1_spec:
    forall (A B: Type) (f: B -> A -> B) (v: B) (m: t A),
    fold1 f m v =
    List.fold_left (fun a p => f a (snd p)) (elements m) v.
  Proof.
    intros. apply fold1_xelements with (l := @nil (positive * positive * A)).
  Qed.    
  
End P2Tree.
