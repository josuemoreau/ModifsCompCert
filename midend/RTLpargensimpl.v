(** Coalescing and RTLpar generation *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSApar.
Require RTLpar.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import CSSAutils.
Require CSSAlive.

Section TRANSFORMATION.

(** RTLpar generation functions *)

Definition compute_phi_classes phi classes :=
  match phi with
  | Iphi args dst =>
      fold_left
        (fun acc arg =>
          P2Tree.set arg dst acc)
        args classes
  end.

Definition compute_phib_classes phib classes :=
  fold_left
    (fun acc phi => compute_phi_classes phi acc)
    phib classes.

Definition compute_phicode_classes (f : function) :=
  PTree.fold
    (fun acc pc phib => compute_phib_classes phib acc)
    (fn_phicode f) (P2Tree.empty reg).

Definition check_phi_ressources_coalescing regrepr phi :=
  match phi with
  | Iphi args dst =>
      forallb (fun arg => p2eq (regrepr arg) dst) (dst :: args)
  end.

Definition check_cssa_coalescing_in_phib regrepr phib :=
  forallb (check_phi_ressources_coalescing regrepr) phib.

Definition check_cssa_coalescing_in_phicode regrepr f :=
  forallb (check_cssa_coalescing_in_phib regrepr)
    (map snd (PTree.elements (fn_phicode f))).

Definition compute_regrepr (f : function) :=
  let classes := compute_phicode_classes f in
  if check_cssa_coalescing_in_phicode
    (fun r =>
      match P2Tree.get r classes with
      | Some repr => repr
      | None => r
      end) f
  then
    Errors.OK (fun r =>
      match P2Tree.get r classes with
      | Some repr => repr
      | None => r
      end)
  else Errors.Error (Errors.msg "check_coalescing_in_phicode").

Definition transl_instruction regrepr ins :=
  match ins with
  | Inop s => Inop s
  | Iop op args res s =>
      Iop op (map regrepr args) (regrepr res) s
  | Iload chunk addr args dst s =>
      Iload chunk addr (map regrepr args) (regrepr dst) s
  | Istore chunk addr args src s =>
      Istore chunk addr (map regrepr args) (regrepr src) s
  | Icall sig (inl r) args res s =>
      Icall sig (inl (regrepr r))
        (map regrepr args) (regrepr res) s
  | Icall sig os args res s =>
      Icall sig os (map regrepr args) (regrepr res) s
  | Itailcall sig (inl r) args =>
      Itailcall sig (inl (regrepr r)) (map (regrepr) args)
  | Itailcall sig os args =>
      Itailcall sig os (map regrepr args)
  | Ibuiltin ef args res s =>
      Ibuiltin ef (map regrepr args) (regrepr res) s
  | Icond cond args ifso ifnot =>
      Icond cond (map regrepr args) ifso ifnot
  | Ijumptable arg tbl =>
      Ijumptable (regrepr arg) tbl
  | Ireturn None => Ireturn None
  | Ireturn (Some arg) =>
      Ireturn (Some (regrepr arg))
  end.

Definition transl_parcb regrepr (parcb : parcopyblock) :=
  map (fun parc =>
    match parc with
    | Iparcopy src dst =>
        Iparcopy (regrepr src) (regrepr dst)
    end)
    parcb.

Definition transl_code (regrepr : reg -> reg)
    (code : code) :=
  PTree.map1
    (transl_instruction regrepr)
    code.

Definition transl_parcopycode (regrepr : reg -> reg)
    (parcode : parcopycode) :=
  PTree.map1
    (transl_parcb regrepr)
    parcode.

(** The transformation *)

Definition transl_function (f : CSSApar.function) :=
  match compute_regrepr f with
  | Errors.Error m => Errors.Error m
  | Errors.OK regrepr =>
      Errors.OK
        (RTLpar.mkfunction
          f.(fn_sig)
          (map regrepr f.(fn_params))
          f.(fn_stacksize)
          (transl_code regrepr f.(fn_code))
          (transl_parcopycode regrepr f.(fn_parcopycode))
          f.(fn_max_indice)
          f.(fn_entrypoint))
  end.

Definition transl_fundef :=
  transf_partial_fundef transl_function.

Definition transl_program (p: CSSApar.program) :
    Errors.res RTLpar.program :=
  transform_partial_program transl_fundef p.

End TRANSFORMATION.
