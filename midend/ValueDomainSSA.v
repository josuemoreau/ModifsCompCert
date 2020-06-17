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

Require Import FunInd.
Require Import Zwf Coqlib Maps Integers Floats Lattice.
Require Import Compopts AST.
Require Import Values Memory Globalenvs Events.

Hint Extern 2 (_ = _) => congruence : va.
Hint Extern 2 (_ <> _) => congruence : va.
Hint Extern 2 (_ < _) => xomega : va.
Hint Extern 2 (_ <= _) => xomega : va.
Hint Extern 2 (_ > _) => xomega : va.
Hint Extern 2 (_ >= _) => xomega : va.

(** The abstract domains for scalar value analysis (no alias analysis) *)

Require Import ValueDomain.

Section MATCH.

(** * Abstracting values *)

Inductive aval : Type :=
  | Vbot                     (**r bottom (empty set of values) *)
  | I (n: int)               (**r exactly [Vint n] *)
  | Uns (n: Z)               (**r a [n]-bit unsigned integer, or [Vundef] *)
  | Sgn (n: Z)               (**r a [n]-bit signed integer, or [Vundef] *)
  | L (n: int64)             (**r exactly [Vlong n] *)
  | F (f: float)             (**r exactly [Vfloat f] *)
  | FS (f: float32)          (**r exactly [Vsingle f] *)
  | Vtop.

Definition eq_aval: forall (v1 v2: aval), {v1=v2} + {v1<>v2}.
Proof.
  intros. generalize zeq Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec; intros.
  decide equality.
Defined.

Definition is_uns (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n -> Int.testbit i m = false.
Definition is_sgn (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n - 1 -> Int.testbit i m = Int.testbit i (Int.zwordsize - 1).

Inductive vmatch : val -> aval -> Prop :=
  | vmatch_i: forall i, vmatch (Vint i) (I i)
  | vmatch_Uns: forall i n, 0 <= n -> is_uns n i -> vmatch (Vint i) (Uns n)
  | vmatch_Uns_undef: forall n, vmatch Vundef (Uns n)
  | vmatch_Sgn: forall i n, 0 < n -> is_sgn n i -> vmatch (Vint i) (Sgn n)
  | vmatch_Sgn_undef: forall n, vmatch Vundef (Sgn n)
  | vmatch_l: forall i, vmatch (Vlong i) (L i)
  | vmatch_f: forall f, vmatch (Vfloat f) (F f)
  | vmatch_s: forall f, vmatch (Vsingle f) (FS f)
  | vmatch_vtop: forall v, vmatch v Vtop.

Lemma vmatch_top: forall v, vmatch v Vtop.
Proof.
  intros. constructor. 
Qed.

Hint Extern 1 (vmatch _ _) => constructor : va.

(* Some properties about [is_uns] and [is_sgn]. *)

Lemma is_uns_mon: forall n1 n2 i, is_uns n1 i -> n1 <= n2 -> is_uns n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_sgn_mon: forall n1 n2 i, is_sgn n1 i -> n1 <= n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_uns_sgn: forall n1 n2 i, is_uns n1 i -> n1 < n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. rewrite ! H by omega. auto.
Qed.

Definition usize := Int.size.

Definition ssize (i: int) := Int.size (if Int.lt i Int.zero then Int.not i else i) + 1.

Lemma is_uns_usize:
  forall i, is_uns (usize i) i.
Proof.
  unfold usize; intros; red; intros.
  apply Int.bits_size_2. omega.
Qed.

Lemma is_sgn_ssize:
  forall i, is_sgn (ssize i) i.
Proof.
  unfold ssize; intros; red; intros.
  destruct (Int.lt i Int.zero) eqn:LT.
- rewrite <- (negb_involutive (Int.testbit i m)).
  rewrite <- (negb_involutive (Int.testbit i (Int.zwordsize - 1))).
  f_equal.
  generalize (Int.size_range (Int.not i)); intros RANGE.
  rewrite <- ! Int.bits_not by omega.
  rewrite ! Int.bits_size_2 by omega.
  auto.
- rewrite ! Int.bits_size_2 by omega.
  auto.
Qed.

Lemma is_uns_zero_ext:
  forall n i, is_uns n i <-> Int.zero_ext n i = i.
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto. symmetry; apply H; auto. omega.
  rewrite <- H. red; intros. rewrite Int.bits_zero_ext by omega. rewrite zlt_false by omega. auto.
Qed.

Lemma is_sgn_sign_ext:
  forall n i, 0 < n -> (is_sgn n i <-> Int.sign_ext n i = i).
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto.
  transitivity (Int.testbit i (Int.zwordsize - 1)).
  apply H0; omega. symmetry; apply H0; omega.
  rewrite <- H0. red; intros. rewrite ! Int.bits_sign_ext by omega.
  f_equal. transitivity (n-1). destruct (zlt m n); omega.
  destruct (zlt (Int.zwordsize - 1) n); omega.
Qed.

Lemma is_zero_ext_uns:
  forall i n m,
  is_uns m i \/ n <= m -> is_uns m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite Int.bits_zero_ext by omega.
  destruct (zlt m0 n); auto. destruct H. apply H; omega. omegaContradiction.
Qed.

Lemma is_zero_ext_sgn:
  forall i n m,
  n < m ->
  is_sgn m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite ! Int.bits_zero_ext by omega.
  transitivity false. apply zlt_false; omega.
  symmetry; apply zlt_false; omega.
Qed.

Lemma is_sign_ext_uns:
  forall i n m,
  0 <= m < n ->
  is_uns m i ->
  is_uns m (Int.sign_ext n i).
Proof.
  intros; red; intros. rewrite Int.bits_sign_ext by omega.
  apply H0. destruct (zlt m0 n); omega. destruct (zlt m0 n); omega.
Qed.

Lemma is_sign_ext_sgn:
  forall i n m,
  0 < n -> 0 < m ->
  is_sgn m i \/ n <= m -> is_sgn m (Int.sign_ext n i).
Proof.
  intros. apply is_sgn_sign_ext; auto.
  destruct (zlt m n). destruct H1. apply is_sgn_sign_ext in H1; auto.
  rewrite <- H1. rewrite (Int.sign_ext_widen i) by omega. apply Int.sign_ext_idem; auto.
  omegaContradiction.
  apply Int.sign_ext_widen; omega.
Qed.

Hint Resolve is_uns_mon is_sgn_mon is_uns_sgn is_uns_usize is_sgn_ssize : va.

Lemma is_uns_1:
  forall n, is_uns 1 n -> n = Int.zero \/ n = Int.one.
Proof.
  intros. destruct (Int.testbit n 0) eqn:B0; [right|left]; apply Int.same_bits_eq; intros.
  rewrite Int.bits_one. destruct (zeq i 0). subst i; auto. apply H; omega.
  rewrite Int.bits_zero. destruct (zeq i 0). subst i; auto. apply H; omega.
Qed.


(** Smart constructors for [Uns] and [Sgn]. *)

Definition uns  (n: Z) : aval :=
  if zle n 1 then Uns 1
  else if zle n 7 then Uns 7
  else if zle n 8 then Uns 8
  else if zle n 15 then Uns 15
  else if zle n 16 then Uns 16
  else Vtop.

Definition sgn (n: Z) : aval :=
  if zle n 8 then Sgn 8 else if zle n 16 then Sgn 16 else Vtop.

Lemma vmatch_uns':
  forall i n, is_uns (Z.max 0 n) i -> vmatch (Vint i) (uns n).
Proof.
  intros.
  assert (A: forall n', n' >= 0 -> n' >= n -> is_uns n' i) by (eauto with va).
  unfold uns.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16). auto with va.
  auto with va.
Qed.

Lemma vmatch_uns:
  forall i n, is_uns n i -> vmatch (Vint i) (uns n).
Proof.
  intros. apply vmatch_uns'. eauto with va.
Qed.

Lemma vmatch_uns_undef: forall n, vmatch Vundef (uns n).
Proof.
  intros. unfold uns.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vmatch_sgn':
  forall i n, is_sgn (Z.max 1 n) i -> vmatch (Vint i) (sgn n).
Proof.
  intros.
  assert (A: forall n', n' >= 1 -> n' >= n -> is_sgn n' i) by (eauto with va).
  unfold sgn.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vmatch_sgn:
  forall i n, is_sgn n i -> vmatch (Vint i) (sgn n).
Proof.
  intros. apply vmatch_sgn'. eauto with va.
Qed.

Lemma vmatch_sgn_undef: forall n, vmatch Vundef (sgn n).
Proof.
  intros. unfold sgn.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Hint Resolve vmatch_uns vmatch_uns_undef vmatch_sgn vmatch_sgn_undef : va.

Lemma vmatch_Uns_1:
  forall v, vmatch v (Uns 1) -> v = Vundef \/ v = Vint Int.zero \/ v = Vint Int.one.
Proof.
  intros. inv H; auto. right. exploit is_uns_1; eauto. intuition congruence.
Qed.

(** Ordering *)

Inductive vge: aval -> aval -> Prop :=
  | vge_bot: forall v, vge v Vbot
  | vge_i: forall i, vge (I i) (I i)
  | vge_l: forall i, vge (L i) (L i)
  | vge_f: forall f, vge (F f) (F f)
  | vge_s: forall f, vge (FS f) (FS f)
  | vge_uns_i: forall n i, 0 <= n -> is_uns n i -> vge (Uns n) (I i)
  | vge_uns_uns: forall n1 n2, n1 >= n2  -> vge (Uns n1) (Uns n2)
  | vge_sgn_i: forall n i, 0 < n -> is_sgn n i -> vge (Sgn n) (I i)
  | vge_sgn_sgn: forall n1 n2, n1 >= n2 -> vge (Sgn n1) (Sgn n2)
  | vge_sgn_uns: forall n1 n2, n1 > n2 -> vge (Sgn n1) (Uns n2)
  | vge_top_v: forall av, vge Vtop av.

Hint Constructors vge : va.

Lemma vge_top: forall v, vge Vtop v.
Proof.
  destruct v; constructor; constructor.
Qed.

Hint Resolve vge_top : va.

Lemma vge_refl: forall v, vge v v.
Proof.
  destruct v; auto with va.
Qed.

Lemma vge_trans: forall u v, vge u v -> forall w, vge v w -> vge u w.
Proof.
  induction 1; intros w V; inv V; eauto with va. 
Qed.

Lemma vmatch_ge:
  forall v x y, vge x y -> vmatch v y -> vmatch v x.
Proof.
  induction 1; intros V; inv V; eauto  with va.
Qed.

(** Least upper bound *)

Definition vlub (v w: aval) : aval :=
  match v, w with
  | Vbot, _ => w
  | _, Vbot => v
  | I i1, I i2 =>
      if Int.eq i1 i2 then v else
      if Int.lt i1 Int.zero || Int.lt i2 Int.zero
      then sgn (Z.max (ssize i1) (ssize i2))
      else uns (Z.max (usize i1) (usize i2))
  | I i, Uns n | Uns n, I i =>
      if Int.lt i Int.zero
      then sgn (Z.max (ssize i) (n + 1))
      else uns (Z.max (usize i) n)
  | I i, Sgn n | Sgn n, I i =>
      sgn (Z.max (ssize i) n)
  | Uns n1, Uns n2 => Uns (Z.max n1 n2)
  | Uns n1, Sgn n2 => sgn (Z.max (n1 + 1) n2)
  | Sgn n1, Uns n2 => sgn (Z.max n1 (n2 + 1))
  | Sgn n1, Sgn n2 => sgn (Z.max n1 n2)
  | F f1, F f2 =>
      if Float.eq_dec f1 f2 then v else Vtop
  | FS f1, FS f2 =>
      if Float32.eq_dec f1 f2 then v else Vtop
  | L i1, L i2 =>
      if Int64.eq i1 i2 then v else Vtop
  | _, _ => Vtop
  end.

Lemma vlub_comm:
  forall v w, vlub v w = vlub w v.
Proof.
  intros. unfold vlub; destruct v; destruct w; auto.
- rewrite Int.eq_sym. predSpec Int.eq Int.eq_spec n0 n.
  congruence.
  rewrite orb_comm.
  destruct (Int.lt n0 Int.zero || Int.lt n Int.zero); f_equal; apply Z.max_comm.
- f_equal.  apply Z.max_comm.
- f_equal.  apply Z.max_comm.
- f_equal.  apply Z.max_comm.
- f_equal.  apply Z.max_comm.
- rewrite Int64.eq_sym. predSpec Int64.eq Int64.eq_spec n0 n; congruence.
- rewrite dec_eq_sym. destruct (Float.eq_dec f0 f). congruence. auto.
- rewrite dec_eq_sym. destruct (Float32.eq_dec f0 f). congruence. auto.
Qed.

Lemma vge_uns_uns': forall n, vge (uns n) (Uns n).
Proof.
  unfold uns; intros.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vge_uns_i': forall n i, 0 <= n -> is_uns n i -> vge (uns n) (I i).
Proof.
  intros. apply vge_trans with (Uns n). apply vge_uns_uns'. auto with va.
Qed.

Lemma vge_sgn_sgn': forall n, vge (sgn n) (Sgn n).
Proof.
  unfold sgn; intros.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vge_sgn_i': forall n i, 0 < n -> is_sgn n i -> vge (sgn n) (I i).
Proof.
  intros. apply vge_trans with (Sgn n). apply vge_sgn_sgn'. auto with va.
Qed.

Hint Resolve vge_uns_uns' vge_uns_i' vge_sgn_sgn' vge_sgn_i' : va.

Lemma usize_pos: forall n, 0 <= usize n.
Proof.
  unfold usize; intros. generalize (Int.size_range n); omega.
Qed.

Lemma ssize_pos: forall n, 0 < ssize n.
Proof.
  unfold ssize; intros.
  generalize (Int.size_range (if Int.lt n Int.zero then Int.not n else n)); omega.
Qed.

Lemma vge_lub_l:
  forall x y, vge (vlub x y) x.
Proof.
  assert (IFSTRICT: forall (cond: bool) x1 x2 y, vge x1 y -> vge x2 y -> vge (if cond then x1 else x2) y).
  { destruct cond; auto with va. }
  unfold vlub; destruct x, y; eauto with va.
- predSpec Int.eq Int.eq_spec n n0. auto with va.
  destruct (Int.lt n Int.zero || Int.lt n0 Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va.
- destruct (Int.lt n Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va.
- apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
- destruct (Int.lt n0 Int.zero).
  eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn (n + 1)); eauto with va.
  eapply vge_trans. apply vge_uns_uns'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn (n + 1)); eauto  with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto with va.
- destruct (Float.eq_dec f f0); constructor.
- destruct (Float32.eq_dec f f0); constructor.
Qed.

Lemma vge_lub_r:
  forall x y, vge (vlub x y) y.
Proof.
  intros. rewrite vlub_comm. apply vge_lub_l.
Qed.

Lemma vmatch_lub_l:
  forall v x y, vmatch v x -> vmatch v (vlub x y).
Proof.
  intros. eapply vmatch_ge; eauto. apply vge_lub_l.
Qed.

Lemma vmatch_lub_r:
  forall v x y, vmatch v y -> vmatch v (vlub x y).
Proof.
  intros. rewrite vlub_comm. apply vmatch_lub_l; auto.
Qed.


Definition vincl (v w: aval) : bool :=
  match v, w with
  | Vbot, _ => true
  | I i, I j => Int.eq_dec i j
  | I i, Uns n => Int.eq_dec (Int.zero_ext n i) i && zle 0 n
  | I i, Sgn n => Int.eq_dec (Int.sign_ext n i) i && zlt 0 n
  | Uns n, Uns m => zle n m 
  | Uns n, Sgn m => zlt n m 
  | Sgn n, Sgn m => zle n m 
  | L i, L j => Int64.eq_dec i j
  | F i, F j => Float.eq_dec i j
  | FS i, FS j => Float32.eq_dec i j
  | _, Vtop => true
  | _, _ => false
  end.

Lemma vincl_ge: forall v w, vincl v w = true -> vge w v.
Proof.
  unfold vincl; destruct v; destruct w;
  intros; try discriminate; try InvBooleans; try subst; auto  with va.
- constructor; auto. rewrite is_uns_zero_ext; auto.
- constructor; auto. rewrite is_sgn_sign_ext; auto.
Qed.

(** Generic operations that just do constant propagation. *)

Definition unop_int (sem: int -> int) (x: aval) :=
  match x with I n => I (sem n) | _ => Vtop end.

Lemma unop_int_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vint i => Vint(sem i) | _ => Vundef end) (unop_int sem x).
Proof.
  intros. unfold unop_int; inv H; auto with va.
Qed.

Definition binop_int (sem: int -> int -> int) (x y: aval) :=
  match x, y with I n, I m => I (sem n m) | _, _ => Vtop end.

Lemma binop_int_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vint i, Vint j => Vint(sem i j) | _, _ => Vundef end) (binop_int sem x y).
Proof.
  intros. unfold binop_int; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_long (sem: int64 -> int64) (x: aval) :=
  match x with L n => L (sem n) | _ => Vtop end.

Lemma unop_long_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vlong i => Vlong(sem i) | _ => Vundef end) (unop_long sem x).
Proof.
  intros. unfold unop_long; inv H; auto with va.
Qed.

Definition binop_long (sem: int64 -> int64 -> int64) (x y: aval) :=
  match x, y with L n, L m => L (sem n m) | _, _ => Vtop end.

Lemma binop_long_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vlong i, Vlong j => Vlong(sem i j) | _, _ => Vundef end) (binop_long sem x y).
Proof.
  intros. unfold binop_long; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_float (sem: float -> float) (x: aval) :=
  match x with F n => F (sem n) | _ => Vtop end.

Lemma unop_float_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vfloat i => Vfloat(sem i) | _ => Vundef end) (unop_float sem x).
Proof.
  intros. unfold unop_float; inv H; auto with va.
Qed.

Definition binop_float (sem: float -> float -> float) (x y: aval) :=
  match x, y with F n, F m => F (sem n m) | _, _ => Vtop end.

Lemma binop_float_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vfloat i, Vfloat j => Vfloat(sem i j) | _, _ => Vundef end) (binop_float sem x y).
Proof.
  intros. unfold binop_float; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_single (sem: float32 -> float32) (x: aval) :=
  match x with FS n => FS (sem n) | _ => Vtop end.

Lemma unop_single_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vsingle i => Vsingle(sem i) | _ => Vundef end) (unop_single sem x).
Proof.
  intros. unfold unop_single; inv H; auto with va.
Qed.

Definition binop_single (sem: float32 -> float32 -> float32) (x y: aval) :=
  match x, y with FS n, FS m => FS (sem n m) | _, _ => Vtop end.

Lemma binop_single_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vsingle i, Vsingle j => Vsingle(sem i j) | _, _ => Vundef end) (binop_single sem x y).
Proof.
  intros. unfold binop_single; inv H; auto with va; inv H0; auto with va.
Qed.

(** Logical operations *)

Definition shl (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shl i amount)
        | Uns n => uns (n + Int.unsigned amount)
        | Sgn n => sgn (n + Int.unsigned amount)
        | _ => Vtop
        end
      else Vtop
  | _ => Vtop
  end.

Lemma shl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shl v w) (shl x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shl v w) Vtop).
  {
    destruct v; destruct w; simpl; try constructor.
  }
  destruct y; auto. simpl. inv H0. unfold Val.shl.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE.
  inv H; auto with va.
- apply vmatch_uns'. red; intros. rewrite Int.bits_shl by omega.
  destruct (zlt m (Int.unsigned n)). auto. apply H1; xomega.
- apply vmatch_sgn'. red; intros. zify.
  rewrite ! Int.bits_shl by omega.
  rewrite ! zlt_false by omega.
  rewrite H1 by omega. symmetry. rewrite H1 by omega. auto.
- destruct v; constructor.
Qed.

Definition shru (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shru i amount)
        | Uns n => uns (n - Int.unsigned amount)
        | _ => uns (Int.zwordsize - Int.unsigned amount)
        end
      else Vtop
  | _ => Vtop
  end.

Lemma shru_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shru v w) (shru x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shru v w) Vtop)
    by (destruct v; destruct w; simpl; try constructor).
  destruct y; auto. inv H0. unfold shru, Val.shru.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  - exploit Int.ltu_inv; eauto.
    intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
    assert (DEFAULT2: forall i, vmatch (Vint (Int.shru i n)) (uns (Int.zwordsize - Int.unsigned n))).
    {
      intros. apply vmatch_uns. red; intros.
      rewrite Int.bits_shru by omega. apply zlt_false. omega.
    }
    inv H; auto with va.
    + apply vmatch_uns'. red; intros. zify.
      rewrite Int.bits_shru by omega.
      destruct (zlt (m + Int.unsigned n) Int.zwordsize); auto.
      apply H1; omega.
    + destruct v ; eauto with va. 
  - destruct v; constructor.
Qed.

Definition shr (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shr i amount)
        | Uns n => sgn (n + 1 - Int.unsigned amount)
        | Sgn n => sgn (n - Int.unsigned amount)
        | _ => sgn (Int.zwordsize - Int.unsigned amount)
        end
      else Vtop
  | _ => Vtop
  end.

Lemma shr_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shr v w) (shr x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shr v w) Vtop).
  {
    destruct v; destruct w; simpl; try constructor.
  }
  destruct y; auto. inv H0. unfold shr, Val.shr.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
  assert (DEFAULT2: forall i, vmatch (Vint (Int.shr i n)) (sgn (Int.zwordsize - Int.unsigned n))).
  {
    intros. apply vmatch_sgn. red; intros.
    rewrite ! Int.bits_shr by omega. f_equal.
    destruct (zlt (m + Int.unsigned n) Int.zwordsize);
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize);
    omega.
  } 
  assert (SGN: forall i p, is_sgn p i -> 0 < p -> vmatch (Vint (Int.shr i n)) (sgn (p - Int.unsigned n))).
  {
    intros. apply vmatch_sgn'. red; intros. zify.
    rewrite ! Int.bits_shr by omega.
    transitivity (Int.testbit i (Int.zwordsize - 1)).
    destruct (zlt (m + Int.unsigned n) Int.zwordsize).
    apply H0; omega.
    auto.
    symmetry.
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize).
    apply H0; omega.
    auto.
  }
  inv H; eauto with va.
  - destruct v ; auto with va.
  - destruct v; constructor.
Qed.

Definition and (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.and i1 i2)
  | I i, Uns n | Uns n, I i => uns (Z.min n (usize i))
  | I i, x | x, I i => uns (usize i)
  | Uns n1, Uns n2 => uns (Z.min n1 n2)
  | Uns n, _ => uns n
  | _, Uns n => uns n
  | Sgn n1, Sgn n2 => sgn (Z.max n1 n2)
  | _, _ => Vtop
  end.

Lemma and_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.and v w) (and x y).
Proof.
  assert (UNS_l: forall i j n, is_uns n i -> is_uns n (Int.and i j)).
  {
    intros; red; intros. rewrite Int.bits_and by auto. rewrite (H m) by auto.
    apply andb_false_l.
  }
  assert (UNS_r: forall i j n, is_uns n i -> is_uns n (Int.and j i)).
  {
    intros. rewrite Int.and_commut. eauto.
  }
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.min n m) (Int.and i j)).
  {
    intros. apply Z.min_case; auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.and i j)).
  {
    intros; red; intros. rewrite ! Int.bits_and by auto with va.
    rewrite H by auto with va. rewrite H0 by auto with va. auto.
  }
  intros.
  unfold and, Val.and; inv H; eauto with va; inv H0;
    try (destruct w) ;
    try (destruct v) ; eauto with va.
Qed.

Definition or (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.or i1 i2)
  | I i, Uns n | Uns n, I i => uns (Z.max n (usize i))
  | Uns n1, Uns n2 => uns  (Z.max n1 n2)
  | Sgn n1, Sgn n2 => sgn  (Z.max n1 n2)
  | _, _ => Vtop
  end.

Lemma or_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.or v w) (or x y).
Proof.
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite Int.bits_or by auto.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite ! Int.bits_or by xomega.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  intros. unfold or, Val.or; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition xor (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.xor i1 i2)
  | I i, Uns n | Uns n, I i => uns (Z.max n (usize i))
  | Uns n1, Uns n2 => uns  (Z.max n1 n2)
  | Sgn n1, Sgn n2 => sgn  (Z.max n1 n2)
  | _, _ => Vtop
  end.

Lemma xor_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.xor v w) (xor x y).
Proof.
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.max n m) (Int.xor i j)).
  {
    intros; red; intros. rewrite Int.bits_xor by auto.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.xor i j)).
  {
    intros; red; intros. rewrite ! Int.bits_xor by xomega.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  intros. unfold xor, Val.xor; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition notint (v: aval) :=
  match v with
  | I i => I (Int.not i)
  | Uns n => sgn (n + 1)
  | Sgn n => Sgn n
  | _ => Vtop
  end.

Lemma notint_sound:
  forall v x, vmatch v x -> vmatch (Val.notint v) (notint x).
Proof.
  assert (SGN: forall n i, is_sgn n i -> is_sgn n (Int.not i)).
  {
    intros; red; intros. rewrite ! Int.bits_not by omega.
    f_equal. apply H; auto.
  }
  intros. unfold Val.notint, notint; inv H; eauto with va.
Qed.

Definition rol (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.rol i j)
  | I j, Uns n => uns (n + Int.unsigned j)
  | I j, Sgn n => if zlt n Int.zwordsize then sgn (n + Int.unsigned j) else Vtop
  | _, _ => Vtop
  end.

Lemma rol_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.rol v w) (rol x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.rol v w) Vtop) by constructor.
  unfold rol; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.rol.
  inv H; auto with va.
- apply vmatch_uns. red; intros. rewrite Int.bits_rol by auto.
  generalize (Int.unsigned_range n); intros.
  rewrite Zmod_small by omega.
  apply H1. omega. omega.
- destruct (zlt n0 Int.zwordsize); auto with va.
  apply vmatch_sgn. red; intros. rewrite ! Int.bits_rol by omega.
  generalize (Int.unsigned_range n); intros.
  rewrite ! Zmod_small by omega.
  rewrite H1 by omega. symmetry. rewrite H1 by omega. auto.
- destruct (zlt n0 Int.zwordsize); auto with va.
Qed.

Definition ror (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.ror i j)
  | _, _ => Vtop
  end.

Lemma ror_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.ror v w) (ror x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.ror v w) Vtop) by constructor.
  unfold ror; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.ror.
  inv H; auto with va.
Qed.

Definition rolm (x: aval) (amount mask: int) :=
  and (rol x (I amount)) (I mask).

Lemma rolm_sound:
  forall v x amount mask,
  vmatch v x -> vmatch (Val.rolm v amount mask) (rolm x amount mask).
Proof.
  intros.
  replace (Val.rolm v amount mask) with (Val.and (Val.rol v (Vint amount)) (Vint mask)).
  apply and_sound. apply rol_sound. auto. constructor. constructor.
  destruct v; auto.
Qed.

(** Integer arithmetic operations *)

Definition neg := unop_int Int.neg.

Lemma neg_sound:
  forall v x, vmatch v x -> vmatch (Val.neg v) (neg x).
Proof (unop_int_sound Int.neg).

Definition add (x y: aval) :=
  match x, y with
  | I i, I j => I (Int.add i j)
  | _, _ => Vtop
  end.

Lemma add_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.add v w) (add x y).
Proof.
  intros. unfold Val.add, add. destruct Archi.ptr64.
- inv H; inv H0; constructor.
- inv H; inv H0; constructor;
  ((apply padd_sound; assumption) || (eapply poffset_sound; eassumption) || idtac).
Qed.

Definition sub (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.sub i1 i2)
  | _, _ => Vtop
  end.

Lemma sub_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.sub v w) (sub x y).
Proof.
  intros. unfold Val.sub, sub. destruct Archi.ptr64.
- inv H; inv H0; eauto with va.
- inv H; inv H0; try (destruct (eq_block b b0)); eauto  with va.
Qed.

Definition mul := binop_int Int.mul.

Lemma mul_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mul v w) (mul x y).
Proof (binop_int_sound Int.mul).

Definition mulhs := binop_int Int.mulhs.

Lemma mulhs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhs v w) (mulhs x y).
Proof (binop_int_sound Int.mulhs).

Definition mulhu := binop_int Int.mulhu.

Lemma mulhu_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhu v w) (mulhu x y).
Proof (binop_int_sound Int.mulhu).

Definition divs (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else Vtop
      else I (Int.divs i1 i2)
  | _, _ => Vtop
  end.

Lemma divs_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divs v w = Some u -> vmatch u (divs x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition divu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
       then if va_strict tt then Vbot else Vtop
      else I (Int.divu i1 i2)
  | _, _ => Vtop
  end.

Lemma divu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divu v w = Some u -> vmatch u (divu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition mods (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else Vtop
      else I (Int.mods i1 i2)
  | _, _ => Vtop
  end.

Lemma mods_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.mods v w = Some u -> vmatch u (mods x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      then if va_strict tt then Vbot else Vtop
      else I (Int.modu i1 i2)
  | I i2, _ => uns (usize i2)
  | _, _ => Vtop
  end.

Lemma modu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modu v w = Some u -> vmatch u (modu x y).
Proof.
  assert (UNS: forall i j, j <> Int.zero -> is_uns (usize j) (Int.modu i j)).
  {
    intros. apply is_uns_mon with (usize (Int.modu i j)); auto with va.
    unfold usize, Int.size. apply Int.Zsize_monotone.
    generalize (Int.unsigned_range_2 j); intros RANGE.
    assert (Int.unsigned j <> 0).
    { red; intros; elim H. rewrite <- (Int.repr_unsigned j). rewrite H0. auto. }
    exploit (Z_mod_lt (Int.unsigned i) (Int.unsigned j)). omega. intros MOD.
    unfold Int.modu. rewrite Int.unsigned_repr. omega. omega.
  }
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero) eqn:Z; inv H1.
  assert (i0 <> Int.zero) by (generalize (Int.eq_spec i0 Int.zero); rewrite Z; auto).
  unfold modu. inv H; inv H0; auto with va. rewrite Z. constructor.
Qed.

Definition shrx (v w: aval) :=
  match v, w with
  | I i, I j => if Int.ltu j (Int.repr 31) then I(Int.shrx i j) else Vtop
  | _, _ => Vtop
  end.

Lemma shrx_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.shrx v w = Some u -> vmatch u (shrx x y).
Proof.
  intros.
  destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:LTU; inv H1.
  unfold shrx; inv H; auto with va; inv H0; auto with va.
  rewrite LTU; auto with va.
Qed.

(** 64-bit integer operations *)

Definition shift_long (sem: int64 -> int -> int64) (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int64.iwordsize' then
        match v with
        | L i => L (sem i amount)
        | _ => Vtop
        end
      else Vtop
  | _ => Vtop
  end.

Lemma shift_long_sound:
  forall sem v w x y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with
          | Vlong i, Vint j => if Int.ltu j Int64.iwordsize'
                               then Vlong (sem i j) else Vundef
          | _, _ => Vundef end)
         (shift_long sem x y).
Proof.
  intros.
  assert (DEFAULT:
    vmatch (match v, w with
            | Vlong i, Vint j => if Int.ltu j Int64.iwordsize'
                                 then Vlong (sem i j) else Vundef
            | _, _ => Vundef end)
           Vtop).
  { destruct v; try constructor; destruct w; try constructor.
  }    
  unfold shift_long. destruct y; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; auto.
  destruct x; auto.
  inv H; inv H0. rewrite LT. constructor.
Qed.

Definition shll := shift_long Int64.shl'.

Lemma shll_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shll v w) (shll x y).
Proof (shift_long_sound Int64.shl').

Definition shrl := shift_long Int64.shr'.

Lemma shrl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shrl v w) (shrl x y).
Proof (shift_long_sound Int64.shr').

Definition shrlu := shift_long Int64.shru'.

Lemma shrlu_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shrlu v w) (shrlu x y).
Proof (shift_long_sound Int64.shru').

Definition andl := binop_long Int64.and.

Lemma andl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.andl v w) (andl x y).
Proof (binop_long_sound Int64.and).

Definition orl := binop_long Int64.or.

Lemma orl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.orl v w) (orl x y).
Proof (binop_long_sound Int64.or).

Definition xorl := binop_long Int64.xor.

Lemma xorl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.xorl v w) (xorl x y).
Proof (binop_long_sound Int64.xor).

Definition notl := unop_long Int64.not.

Lemma notl_sound:
  forall v x, vmatch v x -> vmatch (Val.notl v) (notl x).
Proof (unop_long_sound Int64.not).

Definition rotate_long (sem: int64 -> int64 -> int64) (v w: aval) :=
  match v, w with
  | L i, I amount => L (sem i (Int64.repr (Int.unsigned amount)))
  | _, _ => Vtop
  end.

Lemma rotate_long_sound:
  forall sem v w x y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with
          | Vlong i, Vint j => Vlong (sem i (Int64.repr (Int.unsigned j)))
          | _, _ => Vundef end)
         (rotate_long sem x y).
Proof.
  intros.
  assert (DEFAULT:
    vmatch (match v, w with
            | Vlong i, Vint j => Vlong (sem i (Int64.repr (Int.unsigned j)))
            | _, _ => Vundef end)
           Vtop).
  { destruct v; try constructor. }
  unfold rotate_long. destruct x; auto. destruct y; auto. inv H; inv H0. constructor.
Qed.

Definition roll := rotate_long Int64.rol.

Lemma roll_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.roll v w) (roll x y).
Proof (rotate_long_sound Int64.rol).

Definition rorl := rotate_long Int64.ror.

Lemma rorl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.rorl v w) (rorl x y).
Proof (rotate_long_sound Int64.ror).

Definition negl := unop_long Int64.neg.

Lemma negl_sound:
  forall v x, vmatch v x -> vmatch (Val.negl v) (negl x).
Proof (unop_long_sound Int64.neg).

Definition addl (x y: aval) :=
  match x, y with
  | L i, L j => L (Int64.add i j)
  | _, _ => Vtop
  end.

Lemma addl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.addl v w) (addl x y).
Proof.
  intros. unfold Val.addl, addl. destruct Archi.ptr64.
- inv H; inv H0; constructor;
  ((apply padd_sound; assumption) || (eapply poffset_sound; eassumption) || idtac).
- inv H; inv H0; constructor.
Qed.

Definition subl (v w: aval) :=
  match v, w with
  | L i1, L i2 => L (Int64.sub i1 i2)
  | _, _ => Vtop
  end.

Lemma subl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.subl v w) (subl x y).
Proof.
  intros. unfold Val.subl, subl. destruct Archi.ptr64.
- inv H; inv H0; try (destruct (eq_block b b0)); eauto with va.
- inv H; inv H0; eauto with va.
Qed.

Definition mull := binop_long Int64.mul.

Lemma mull_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mull v w) (mull x y).
Proof (binop_long_sound Int64.mul).

Definition mullhs := binop_long Int64.mulhs.

Lemma mullhs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mullhs v w) (mullhs x y).
Proof (binop_long_sound Int64.mulhs).

Definition mullhu := binop_long Int64.mulhu.

Lemma mullhu_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mullhu v w) (mullhu x y).
Proof (binop_long_sound Int64.mulhu).

Definition divls (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      || Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone
      then if va_strict tt then Vbot else Vtop
      else L (Int64.divs i1 i2)
  | _, _ => Vtop
  end.

Lemma divls_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divls v w = Some u -> vmatch u (divls x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition divlu (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
       then if va_strict tt then Vbot else Vtop
      else L (Int64.divu i1 i2)
  | _, _ => Vtop
  end.

Lemma divlu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divlu v w = Some u -> vmatch u (divlu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modls (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      || Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone
      then if va_strict tt then Vbot else Vtop
      else L (Int64.mods i1 i2)
  | _, _ => Vtop
  end.

Lemma modls_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modls v w = Some u -> vmatch u (modls x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modlu (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      then if va_strict tt then Vbot else Vtop
      else L (Int64.modu i1 i2)
  | _, _ => Vtop
  end.

Lemma modlu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modlu v w = Some u -> vmatch u (modlu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition shrxl (v w: aval) :=
  match v, w with
  | L i, I j => if Int.ltu j (Int.repr 63) then L(Int64.shrx' i j) else Vtop
  | _, _ => Vtop
  end.

Lemma shrxl_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.shrxl v w = Some u -> vmatch u (shrxl x y).
Proof.
  intros.
  destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.ltu i0 (Int.repr 63)) eqn:LTU; inv H1.
  unfold shrxl; inv H; auto with va; inv H0; auto with va.
  rewrite LTU; auto with va.
Qed.

Definition rolml (x: aval) (amount: int) (mask: int64) :=
  andl (roll x (I amount)) (L mask).

Lemma rolml_sound:
  forall v x amount mask,
  vmatch v x -> vmatch (Val.rolml v amount mask) (rolml x amount mask).
Proof.
  intros.
  replace (Val.rolml v amount mask) with (Val.andl (Val.roll v (Vint amount)) (Vlong mask)).
  apply andl_sound. apply roll_sound. auto. constructor. constructor.
  destruct v; auto.
Qed.

(** Floating-point arithmetic operations *)

Definition negf := unop_float Float.neg.

Lemma negf_sound:
  forall v x, vmatch v x -> vmatch (Val.negf v) (negf x).
Proof (unop_float_sound Float.neg).

Definition absf := unop_float Float.abs.

Lemma absf_sound:
  forall v x, vmatch v x -> vmatch (Val.absf v) (absf x).
Proof (unop_float_sound Float.abs).

Definition addf := binop_float Float.add.

Lemma addf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.addf v w) (addf x y).
Proof (binop_float_sound Float.add).

Definition subf := binop_float Float.sub.

Lemma subf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.subf v w) (subf x y).
Proof (binop_float_sound Float.sub).

Definition mulf := binop_float Float.mul.

Lemma mulf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulf v w) (mulf x y).
Proof (binop_float_sound Float.mul).

Definition divf := binop_float Float.div.

Lemma divf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.divf v w) (divf x y).
Proof (binop_float_sound Float.div).

Definition negfs := unop_single Float32.neg.

Lemma negfs_sound:
  forall v x, vmatch v x -> vmatch (Val.negfs v) (negfs x).
Proof (unop_single_sound Float32.neg).

Definition absfs := unop_single Float32.abs.

Lemma absfs_sound:
  forall v x, vmatch v x -> vmatch (Val.absfs v) (absfs x).
Proof (unop_single_sound Float32.abs).

Definition addfs := binop_single Float32.add.

Lemma addfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.addfs v w) (addfs x y).
Proof (binop_single_sound Float32.add).

Definition subfs := binop_single Float32.sub.

Lemma subfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.subfs v w) (subfs x y).
Proof (binop_single_sound Float32.sub).

Definition mulfs := binop_single Float32.mul.

Lemma mulfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulfs v w) (mulfs x y).
Proof (binop_single_sound Float32.mul).

Definition divfs := binop_single Float32.div.

Lemma divfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.divfs v w) (divfs x y).
Proof (binop_single_sound Float32.div).

(** Conversions *)

Definition zero_ext (nbits: Z) (v: aval) :=
  match v with
  | I i => I (Int.zero_ext nbits i)
  | Uns n => uns (Z.min n nbits)
  | _ => uns nbits
  end.

Lemma zero_ext_sound:
  forall nbits v x, vmatch v x -> vmatch (Val.zero_ext nbits v) (zero_ext nbits x).
Proof.
  assert (DFL: forall nbits i, is_uns nbits (Int.zero_ext nbits i)).
  {
    intros; red; intros. rewrite Int.bits_zero_ext by omega. apply zlt_false; auto.
  }
  intros. inv H; simpl; auto with va. apply vmatch_uns.
  red; intros. zify.
  rewrite Int.bits_zero_ext by omega.
  destruct (zlt m nbits); auto with va.
  destruct v ; auto with va.
  simpl. auto with va.
Qed.

Definition sign_ext (nbits: Z) (v: aval) :=
  match v with
  | I i => I (Int.sign_ext nbits i)
  | Uns n => if zlt n nbits then Uns n else sgn nbits
  | Sgn n => sgn (Z.min n nbits)
  | _ => sgn nbits
  end.

Lemma sign_ext_sound:
  forall nbits v x, 0 < nbits -> vmatch v x -> vmatch (Val.sign_ext nbits v) (sign_ext nbits x).
Proof.
  assert (DFL: forall nbits i, 0 < nbits -> vmatch (Vint (Int.sign_ext nbits i)) (sgn nbits)).
  {
    intros. apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  }
  intros. inv H0; simpl; auto with va.
- destruct (zlt n nbits); eauto with va.
  constructor; auto. eapply is_sign_ext_uns; eauto with va.
- destruct (zlt n nbits); auto with va.
- apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  apply Z.min_case; auto with va.
- destruct v ; auto with va.
  simpl. auto with va.
Qed.

Definition longofint (v: aval) :=
  match v with
  | I i => L (Int64.repr (Int.signed i))
  | _ => Vtop
  end.

Lemma longofint_sound:
  forall v x, vmatch v x -> vmatch (Val.longofint v) (longofint x).
Proof.
  unfold Val.longofint, longofint; intros; inv H; auto with va.
Qed.

Definition longofintu (v: aval) :=
  match v with
  | I i => L (Int64.repr (Int.unsigned i))
  | _ => Vtop
  end.

Lemma longofintu_sound:
  forall v x, vmatch v x -> vmatch (Val.longofintu v) (longofintu x).
Proof.
  unfold Val.longofintu, longofintu; intros; inv H; auto with va.
Qed.

Definition singleoffloat (v: aval) :=
  match v with
  | F f => FS (Float.to_single f)
  | _   => Vtop
  end.

Lemma singleoffloat_sound:
  forall v x, vmatch v x -> vmatch (Val.singleoffloat v) (singleoffloat x).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.singleoffloat v) Vtop).
  { constructor. }
  destruct x; auto. inv H. constructor.
Qed.

Definition floatofsingle (v: aval) :=
  match v with
  | FS f => F (Float.of_single f)
  | _   => Vtop
  end.

Lemma floatofsingle_sound:
  forall v x, vmatch v x -> vmatch (Val.floatofsingle v) (floatofsingle x).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.floatofsingle v) Vtop).
  { constructor. }
  destruct x; auto. inv H. constructor.
Qed.

Definition intoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma intoffloat_sound:
  forall v x w, vmatch v x -> Val.intoffloat v = Some w -> vmatch w (intoffloat x).
Proof.
  unfold Val.intoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition intuoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma intuoffloat_sound:
  forall v x w, vmatch v x -> Val.intuoffloat v = Some w -> vmatch w (intuoffloat x).
Proof.
  unfold Val.intuoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition floatofint (x: aval) :=
  match x with
  | I i => F(Float.of_int i)
  | _   => Vtop
  end.

Lemma floatofint_sound:
  forall v x w, vmatch v x -> Val.floatofint v = Some w -> vmatch w (floatofint x).
Proof.
  unfold Val.floatofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatofintu (x: aval) :=
  match x with
  | I i => F(Float.of_intu i)
  | _   => Vtop
  end.

Lemma floatofintu_sound:
  forall v x w, vmatch v x -> Val.floatofintu v = Some w -> vmatch w (floatofintu x).
Proof.
  unfold Val.floatofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition intofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma intofsingle_sound:
  forall v x w, vmatch v x -> Val.intofsingle v = Some w -> vmatch w (intofsingle x).
Proof.
  unfold Val.intofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition intuofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma intuofsingle_sound:
  forall v x w, vmatch v x -> Val.intuofsingle v = Some w -> vmatch w (intuofsingle x).
Proof.
  unfold Val.intuofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition singleofint (x: aval) :=
  match x with
  | I i => FS(Float32.of_int i)
  | _   => Vtop
  end.

Lemma singleofint_sound:
  forall v x w, vmatch v x -> Val.singleofint v = Some w -> vmatch w (singleofint x).
Proof.
  unfold Val.singleofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition singleofintu (x: aval) :=
  match x with
  | I i => FS(Float32.of_intu i)
  | _   => Vtop
  end.

Lemma singleofintu_sound:
  forall v x w, vmatch v x -> Val.singleofintu v = Some w -> vmatch w (singleofintu x).
Proof.
  unfold Val.singleofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition longoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_long f with
      | Some i => L i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma longoffloat_sound:
  forall v x w, vmatch v x -> Val.longoffloat v = Some w -> vmatch w (longoffloat x).
Proof.
  unfold Val.longoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_long f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition longuoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_longu f with
      | Some i => L i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma longuoffloat_sound:
  forall v x w, vmatch v x -> Val.longuoffloat v = Some w -> vmatch w (longuoffloat x).
Proof.
  unfold Val.longuoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_longu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition floatoflong (x: aval) :=
  match x with
  | L i => F(Float.of_long i)
  | _   => Vtop
  end.

Lemma floatoflong_sound:
  forall v x w, vmatch v x -> Val.floatoflong v = Some w -> vmatch w (floatoflong x).
Proof.
  unfold Val.floatoflong; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatoflongu (x: aval) :=
  match x with
  | L i => F(Float.of_longu i)
  | _   => Vtop
  end.

Lemma floatoflongu_sound:
  forall v x w, vmatch v x -> Val.floatoflongu v = Some w -> vmatch w (floatoflongu x).
Proof.
  unfold Val.floatoflongu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition longofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_long f with
      | Some i => L i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma longofsingle_sound:
  forall v x w, vmatch v x -> Val.longofsingle v = Some w -> vmatch w (longofsingle x).
Proof.
  unfold Val.longofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_long f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition longuofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_longu f with
      | Some i => L i
      | None => if va_strict tt then Vbot else Vtop
      end
  | _ => Vtop
  end.

Lemma longuofsingle_sound:
  forall v x w, vmatch v x -> Val.longuofsingle v = Some w -> vmatch w (longuofsingle x).
Proof.
  unfold Val.longuofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_longu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition singleoflong (x: aval) :=
  match x with
  | L i => FS(Float32.of_long i)
  | _   => Vtop
  end.

Lemma singleoflong_sound:
  forall v x w, vmatch v x -> Val.singleoflong v = Some w -> vmatch w (singleoflong x).
Proof.
  unfold Val.singleoflong; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition singleoflongu (x: aval) :=
  match x with
  | L i => FS(Float32.of_longu i)
  | _   => Vtop
  end.

Lemma singleoflongu_sound:
  forall v x w, vmatch v x -> Val.singleoflongu v = Some w -> vmatch w (singleoflongu x).
Proof.
  unfold Val.singleoflongu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatofwords (x y: aval) :=
  match x, y with
  | I i, I j => F(Float.from_words i j)
  | _, _     => Vtop
  end.

Lemma floatofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.floatofwords v w) (floatofwords x y).
Proof.
  intros. unfold floatofwords; inv H; simpl; auto with va; inv H0; auto with va.
Qed.

Definition longofwords (x y: aval) :=
  match y, x with
  | I j, I i => L(Int64.ofwords i j)
  | _, _     => Vtop
  end.

Lemma longofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.longofwords v w) (longofwords x y).
Proof.
  intros. unfold longofwords; inv H0; inv H; simpl; auto with va.
Qed.

Definition loword (x: aval) :=
  match x with
  | L i => I(Int64.loword i)
  | _   => Vtop
  end.

Lemma loword_sound: forall v x, vmatch v x -> vmatch (Val.loword v) (loword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.

Definition hiword (x: aval) :=
  match x with
  | L i => I(Int64.hiword i)
  | _   => Vtop
  end.

Lemma hiword_sound: forall v x, vmatch v x -> vmatch (Val.hiword v) (hiword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.

(** Comparisons and variation intervals *)

Definition cmp_intv (c: comparison) (i: Z * Z) (n: Z) : ValueDomain.abool :=
  let (lo, hi) := i in
  match c with
  | Ceq => if zlt n lo || zlt hi n then ValueDomain.Maybe false else ValueDomain.Btop
  | Cne => ValueDomain.Btop
  | Clt => if zlt hi n then ValueDomain.Maybe true else if zle n lo then ValueDomain.Maybe false else ValueDomain.Btop
  | Cle => if zle hi n then ValueDomain.Maybe true else if zlt n lo then ValueDomain.Maybe false else ValueDomain.Btop
  | Cgt => if zlt n lo then ValueDomain.Maybe true else if zle hi n then ValueDomain.Maybe false else ValueDomain.Btop
  | Cge => if zle n lo then ValueDomain.Maybe true else if zlt hi n then ValueDomain.Maybe false else ValueDomain.Btop
  end.

Definition zcmp (c: comparison) (n1 n2: Z) : bool :=
  match c with
  | Ceq => zeq n1 n2
  | Cne => negb (zeq n1 n2)
  | Clt => zlt n1 n2
  | Cle => zle n1 n2
  | Cgt => zlt n2 n1
  | Cge => zle n2 n1
  end.

Lemma zcmp_intv_sound:
  forall c i x n,
  fst i <= x <= snd i ->
  ValueDomain.cmatch (Some (zcmp c x n)) (cmp_intv c i n).
Proof.
  intros c [lo hi] x n; simpl; intros R.
  destruct c; unfold zcmp, proj_sumbool.
- (* eq *)
  destruct (zlt n lo). rewrite zeq_false by omega. constructor.
  destruct (zlt hi n). rewrite zeq_false by omega. constructor.
  constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). rewrite zlt_true by omega. constructor.
  destruct (zle n lo). rewrite zlt_false by omega. constructor.
  constructor.
- (* le *)
  destruct (zle hi n). rewrite zle_true by omega. constructor.
  destruct (zlt n lo). rewrite zle_false by omega. constructor.
  constructor.
- (* gt *)
  destruct (zlt n lo). rewrite zlt_true by omega. constructor.
  destruct (zle hi n). rewrite zlt_false by omega. constructor.
  constructor.
- (* ge *)
  destruct (zle n lo). rewrite zle_true by omega. constructor.
  destruct (zlt hi n). rewrite zle_false by omega. constructor.
  constructor.
Qed.

Lemma cmp_intv_None:
  forall c i n, ValueDomain.cmatch None (cmp_intv c i n).
Proof.
  unfold cmp_intv; intros. destruct i as [lo hi].
  destruct c.
- (* eq *)
  destruct (zlt n lo). constructor. destruct (zlt hi n); constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). constructor. destruct (zle n lo); constructor.
- (* le *)
  destruct (zle hi n). constructor. destruct (zlt n lo); constructor.
- (* gt *)
  destruct (zlt n lo). constructor. destruct (zle hi n); constructor.
- (* ge *)
  destruct (zle n lo). constructor. destruct (zlt hi n); constructor.
Qed.

Definition uintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.unsigned n, Int.unsigned n)
  | Uns n => if zlt n Int.zwordsize then (0, two_p n - 1) else (0, Int.max_unsigned)
  | _ => (0, Int.max_unsigned)
  end.

Lemma uintv_sound:
  forall n v, vmatch (Vint n) v -> fst (uintv v) <= Int.unsigned n <= snd (uintv v).
Proof.
  intros. inv H; simpl; try (apply Int.unsigned_range_2).
- omega.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2. rewrite Int.zero_ext_mod by omega.
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. omega.
+ apply Int.unsigned_range_2.
Qed.

Lemma cmpu_intv_sound:
  forall valid c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  ValueDomain.cmatch (Val.cmpu_bool valid c (Vint n1) (Vint n2)) (cmp_intv c (uintv v1) (Int.unsigned n2)).
Proof.
  intros. simpl. replace (Int.cmpu c n1 n2) with (zcmp c (Int.unsigned n1) (Int.unsigned n2)).
  apply zcmp_intv_sound; apply uintv_sound; auto.
  destruct c; simpl; auto.
  unfold Int.ltu. destruct (zle (Int.unsigned n1) (Int.unsigned n2)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
  unfold Int.ltu. destruct (zle (Int.unsigned n2) (Int.unsigned n1)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
Qed.

Lemma cmpu_intv_sound_2:
  forall valid c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  ValueDomain.cmatch (Val.cmpu_bool valid c (Vint n2) (Vint n1)) (cmp_intv (swap_comparison c) (uintv v1) (Int.unsigned n2)).
Proof.
  intros. rewrite <- Val.swap_cmpu_bool. apply cmpu_intv_sound; auto.
Qed.

Definition sintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.signed n, Int.signed n)
  | Uns n =>
      if zlt n Int.zwordsize then (0, two_p n - 1) else (Int.min_signed, Int.max_signed)
  | Sgn n =>
      if zlt n Int.zwordsize
      then (let x := two_p (n-1) in (-x, x-1))
      else (Int.min_signed, Int.max_signed)
  | _ => (Int.min_signed, Int.max_signed)
  end.

Lemma sintv_sound:
  forall n v, vmatch (Vint n) v -> fst (sintv v) <= Int.signed n <= snd (sintv v).
Proof.
  intros. inv H; simpl; try (apply Int.signed_range).
- omega.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2.
  assert (Int.unsigned (Int.zero_ext n0 n) = Int.unsigned n mod two_p n0) by (apply Int.zero_ext_mod; omega).
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. intros.
  replace (Int.signed (Int.zero_ext n0 n)) with (Int.unsigned (Int.zero_ext n0 n)).
  rewrite H. omega.
  unfold Int.signed. rewrite zlt_true. auto.
  assert (two_p n0 <= Int.half_modulus).
  { change Int.half_modulus with (two_p (Int.zwordsize - 1)).
    apply two_p_monotone. omega. }
  omega.
+ apply Int.signed_range.
- destruct (zlt n0 (Int.zwordsize)); simpl.
+ rewrite is_sgn_sign_ext in H2 by auto. rewrite <- H2.
  exploit (Int.sign_ext_range n0 n). omega. omega.
+ apply Int.signed_range.
Qed.

Lemma cmp_intv_sound:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  ValueDomain.cmatch (Val.cmp_bool c (Vint n1) (Vint n2)) (cmp_intv c (sintv v1) (Int.signed n2)).
Proof.
  intros. simpl. replace (Int.cmp c n1 n2) with (zcmp c (Int.signed n1) (Int.signed n2)).
  apply zcmp_intv_sound; apply sintv_sound; auto.
  destruct c; simpl; rewrite ? Int.eq_signed; auto.
  unfold Int.lt. destruct (zle (Int.signed n1) (Int.signed n2)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
  unfold Int.lt. destruct (zle (Int.signed n2) (Int.signed n1)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
Qed.

Lemma cmp_intv_sound_2:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  ValueDomain.cmatch (Val.cmp_bool c (Vint n2) (Vint n1)) (cmp_intv (swap_comparison c) (sintv v1) (Int.signed n2)).
Proof.
  intros. rewrite <- Val.swap_cmp_bool. apply cmp_intv_sound; auto.
Qed.

(** Comparisons *)
Definition cmpu_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | I i1, I i2 => ValueDomain.Just (Int.cmpu c i1 i2)
  | _, I i => ValueDomain.club (cmp_intv c (uintv v) (Int.unsigned i)) (ValueDomain.cmp_different_blocks c)
  | I i, _ => ValueDomain.club (cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i)) (ValueDomain.cmp_different_blocks c)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmpu_bool_sound:
  forall valid c v w x y,
    vmatch v x ->
    vmatch w y ->
    ValueDomain.cmatch (Val.cmpu_bool valid c v w) (cmpu_bool c x y).
Proof.
  intros.
  unfold cmpu_bool; inversion H; subst; inversion H0; subst;
    try (destruct w ) ;
    try (destruct v ) ;
    eauto using ValueDomain.cmatch_top, ValueDomain.cmp_different_blocks_none,
    ValueDomain.pcmp_none,
    ValueDomain.cmatch_lub_l, ValueDomain.cmatch_lub_r,
    MATCH.cmpu_intv_sound, MATCH.cmpu_intv_sound_2, MATCH.cmp_intv_None with va.
  - constructor.
Qed.

Definition cmp_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | I i1, I i2 => ValueDomain.Just (Int.cmp c i1 i2)
  | _, I i => cmp_intv c (sintv v) (Int.signed i)
  | I i, _ => cmp_intv (swap_comparison c) (sintv w) (Int.signed i)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmp_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> ValueDomain.cmatch (Val.cmp_bool c v w) (cmp_bool c x y).
Proof.
  intros.
  unfold cmp_bool; inversion H; subst; inversion H0; subst;
   try (destruct w ) ;
   try (destruct v ) ;  
  auto using ValueDomain.cmatch_top, cmp_intv_sound, cmp_intv_sound_2, cmp_intv_None.
- constructor.
Qed.

Definition cmplu_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | L i1, L i2 => ValueDomain.Just (Int64.cmpu c i1 i2)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmplu_bool_sound:
  forall valid c v w x y, vmatch v x -> vmatch w y -> ValueDomain.cmatch (Val.cmplu_bool valid c v w) (cmplu_bool c x y).
Proof.
  intros.
  unfold cmplu_bool; inversion H; subst; inversion H0; subst;
    try (destruct w ) ;
    try (destruct v ) ;
    auto using ValueDomain.cmatch_top, 
             ValueDomain.cmatch_lub_l, ValueDomain.cmatch_lub_r.
- constructor.
Qed.

Definition cmpl_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | L i1, L i2 => ValueDomain.Just (Int64.cmp c i1 i2)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmpl_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> ValueDomain.cmatch (Val.cmpl_bool c v w) (cmpl_bool c x y).
Proof.
  intros.
  unfold cmpl_bool; inversion H; subst; inversion H0; subst;
  auto using ValueDomain.cmatch_top.
- constructor.
Qed.

Definition cmpf_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | F f1, F f2 => ValueDomain.Just (Float.cmp c f1 f2)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmpf_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> ValueDomain.cmatch (Val.cmpf_bool c v w) (cmpf_bool c x y).
Proof.
  intros. inv H; try constructor; inv H0; constructor.
Qed.

Definition cmpfs_bool (c: comparison) (v w: aval) : ValueDomain.abool :=
  match v, w with
  | FS f1, FS f2 => ValueDomain.Just (Float32.cmp c f1 f2)
  | _, _ => ValueDomain.Btop
  end.

Lemma cmpfs_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> ValueDomain.cmatch (Val.cmpfs_bool c v w) (cmpfs_bool c x y).
Proof.
  intros. inv H; try constructor; inv H0; constructor.
Qed.

Definition maskzero (x: aval) (mask: int) : ValueDomain.abool :=
  match x with
  | I i => ValueDomain.Just (Int.eq (Int.and i mask) Int.zero)
  | Uns n => if Int.eq (Int.zero_ext n mask) Int.zero then ValueDomain.Maybe true else ValueDomain.Btop
  | _ => ValueDomain.Btop
  end.

Lemma maskzero_sound:
  forall mask v x,
  vmatch v x ->
  ValueDomain.cmatch (Val.maskzero_bool v mask) (maskzero x mask).
Proof.
  intros. inv H; simpl; auto with va.
  predSpec Int.eq Int.eq_spec (Int.zero_ext n mask) Int.zero; auto with va.
  replace (Int.and i mask) with Int.zero.
  rewrite Int.eq_true. constructor.
  rewrite is_uns_zero_ext in H1. rewrite Int.zero_ext_and in * by auto.
  rewrite <- H1. rewrite Int.and_assoc. rewrite Int.and_commut in H. rewrite H.
  rewrite Int.and_zero; auto.
  destruct (Int.eq (Int.zero_ext n mask) Int.zero); constructor.
Qed.

Definition of_optbool (ab: ValueDomain.abool) : aval :=
  match ab with
  | ValueDomain.Just b => I (if b then Int.one else Int.zero)
  | _ => Uns 1
  end.

Lemma of_optbool_sound:
  forall ob ab, ValueDomain.cmatch ob ab -> vmatch (Val.of_optbool ob) (of_optbool ab).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.of_optbool ob) (Uns 1)).
  {
    destruct ob; simpl; auto with va.
    destruct b; constructor; try omega.
    change 1 with (usize Int.one). apply is_uns_usize.
    red; intros. apply Int.bits_zero.
  }
  inv H; auto. simpl. destruct b; constructor.
Qed.

Definition resolve_branch (ab: ValueDomain.abool) : option bool :=
  match ab with
  | ValueDomain.Just b => Some b
  | ValueDomain.Maybe b => Some b
  | _ => None
  end.

Lemma resolve_branch_sound:
  forall b ab b',
  ValueDomain.cmatch (Some b) ab -> resolve_branch ab = Some b' -> b' = b.
Proof.
  intros. inv H; simpl in H0; congruence.
Qed.

(** Normalization at load time *)

Definition vnormalize (chunk: memory_chunk) (v: aval) :=
  match chunk, v with
  | _, Vbot => Vbot
  | Mint8signed, I i => I (Int.sign_ext 8 i)
  | Mint8signed, Uns n => if zlt n 8 then Uns n else Sgn 8
  | Mint8signed, Sgn n => Sgn (Z.min n 8)
  | Mint8signed, _ => Sgn 8
  | Mint8unsigned, I i => I (Int.zero_ext 8 i)
  | Mint8unsigned, Uns n => Uns  (Z.min n 8)
  | Mint8unsigned, _ => Uns  8
  | Mint16signed, I i => I (Int.sign_ext 16 i)
  | Mint16signed, Uns n => if zlt n 16 then Uns  n else Sgn  16
  | Mint16signed, Sgn n => Sgn  (Z.min n 16)
  | Mint16signed, _ => Sgn 16
  | Mint16unsigned, I i => I (Int.zero_ext 16 i)
  | Mint16unsigned, Uns n => Uns  (Z.min n 16)
  | Mint16unsigned, _ => Uns  16
  | Mint32, (I _ | Uns _ | Sgn _ ) => v
  | Mint64, (L _ ) => v
  | Mint64, (Uns _ | Sgn _) => Vtop
  | Mfloat32, FS f => v
  | Mfloat64, F f => v
  | Many32, (I _ | Uns _ | Sgn _ | FS _ ) => v
  | Many64, _ => v
  | _, _ => Vtop
  end.

Lemma vnormalize_sound:
  forall chunk v x, vmatch v x -> vmatch (Val.load_result chunk v) (vnormalize chunk x).
Proof.
  unfold Val.load_result, vnormalize; generalize Archi.ptr64; intros ptr64;
  induction 1; destruct chunk; auto with va.
- destruct (zlt n 8); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. xomega. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 16); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. xomega. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 8); auto with va.
- destruct (zlt n 16); auto with va.
- constructor. xomega. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- constructor. xomega. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- destruct v ; auto with va.
  constructor.
  omega. apply is_sign_ext_sgn; auto with va.
- destruct v ; auto with va.
  constructor. omega. apply is_zero_ext_uns; auto with va.
- destruct v ; auto with va.
  constructor. omega. apply is_sign_ext_sgn; auto with va.
- destruct v ; auto with va.
  constructor. omega. apply is_zero_ext_uns; auto with va.
Qed.

End MATCH.

Module AVal <: SEMILATTICE_WITH_TOP.

  Definition t := aval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_aval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. unfold beq; intros. InvBooleans. auto. Qed.
  Definition ge := vge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. unfold eq, ge; intros. subst y. apply vge_refl. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. unfold ge; intros. eapply vge_trans; eauto. Qed.
  Definition bot : t := Vbot.
  Lemma ge_bot: forall x, ge x bot.
  Proof. intros. constructor. Qed.
  Definition top : t := Vtop.
  Lemma ge_top: forall x, ge top x.
  Proof. intros. apply vge_top. Qed.
  Definition lub := vlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof vge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof vge_lub_r.
End AVal.

Hint Constructors ValueDomain.cmatch : va.
Hint Constructors vmatch: va.
Hint Resolve 
       shl_sound shru_sound shr_sound
       and_sound or_sound xor_sound notint_sound
       ror_sound rolm_sound
       neg_sound add_sound sub_sound
       mul_sound mulhs_sound mulhu_sound
       divs_sound divu_sound mods_sound modu_sound shrx_sound
       shll_sound shrl_sound shrlu_sound
       andl_sound orl_sound xorl_sound notl_sound roll_sound rorl_sound
       negl_sound addl_sound subl_sound
       mull_sound mullhs_sound mullhu_sound
       divls_sound divlu_sound modls_sound modlu_sound shrxl_sound
       negf_sound absf_sound
       addf_sound subf_sound mulf_sound divf_sound
       negfs_sound absfs_sound
       addfs_sound subfs_sound mulfs_sound divfs_sound
       zero_ext_sound sign_ext_sound longofint_sound longofintu_sound
       singleoffloat_sound floatofsingle_sound
       intoffloat_sound intuoffloat_sound floatofint_sound floatofintu_sound
       intofsingle_sound intuofsingle_sound singleofint_sound singleofintu_sound
       longoffloat_sound longuoffloat_sound floatoflong_sound floatoflongu_sound
       longofsingle_sound longuofsingle_sound singleoflong_sound singleoflongu_sound
       longofwords_sound loword_sound hiword_sound
       cmpu_bool_sound cmp_bool_sound cmplu_bool_sound cmpl_bool_sound
       cmpf_bool_sound cmpfs_bool_sound
       maskzero_sound : va.
