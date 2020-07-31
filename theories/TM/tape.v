Require Import ZArith Lia.

Set Implicit Arguments.

Section iter.

  Variable (X : Type) (f : X -> X).

  Fixpoint iter n x :=
    match n with
      | 0   => x
      | S n => iter n (f x)
    end.

  Fact iter_plus n m x : iter n (iter m x) = iter (m+n) x.
  Proof. revert x; induction m; simpl; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite <- iter_plus; auto.
  Qed.

End iter.

Open Scope Z_scope.

Print Z.

Section iterZ.

  Variable (X : Type) (l : X -> X) (r : X -> X) 
           (Hlr : forall x, l (r x) = x) (Hrl : forall x, r (l x) = x).

  Fixpoint iterZ i x :=
    match i with
      | Z0     => x
      | Zpos n => iter r (Pos.to_nat n) x
      | Zneg n => iter l (Pos.to_nat n) x
    end.

  Fact iterZ_0 x : iterZ 0 x = x.
  Proof. auto. Qed.

  Fact iterZ_r x : iterZ 1 x = r x.
  Proof. auto. Qed.

  Fact iterZ_l x : iterZ (-1) x = l x.
  Proof. auto. Qed.

  Fact iterZ_plus i j x : iterZ i (iterZ j x) = iterZ (j+i) x.
  Proof.
    (* Not that easy *)
  Admitted.

  Fact iterZ_abs_r i x : 0 <= i -> iterZ i x = iter r (Z.abs_nat i) x.
  Proof.
  Admitted.

  Fact iterZ_abs_l i x : i <= 0 -> iterZ i x = iter l (Z.abs_nat i) x.
  Proof.
  Admitted.

End iterZ.

Section tapes.

  (** Some ideas for axiomatized tapes *)

  Variable Σ : Type.

  (** tape where reads and writes can occur at any position (Z) relative
      to the current position (Z) *) 

  Record tape_Z : Type := {
    tpZ    :> Type;
    tpZ_rd : tpZ -> Z -> option Σ;
    tpZ_wr : tpZ -> Z -> Σ -> tpZ;
    tpZ_mv : tpZ -> Z -> tpZ;
    tpZ_rd_mv : forall t i j, tpZ_rd (tpZ_mv t i) j = tpZ_rd t (j-i);
    tpZ_wr_mv : forall t i j a, tpZ_wr (tpZ_mv t i) j a = tpZ_mv (tpZ_wr t (j-i) a) i;
    tpZ_mv_mv : forall t i j, tpZ_mv (tpZ_mv t i) j = tpZ_mv t (i+j);
    tpZ_rd_wr_eq : forall t i j a, i = j -> tpZ_rd (tpZ_wr t i a) j = Some a;
    tpZ_rd_wr_neq : forall t i j a, i <> j -> tpZ_rd (tpZ_wr t i a) j = tpZ_rd t j;
 (*   tpZ_nil : tpZ;
    tpZ_nil_spec : forall i, tpZ_rd tpZ_nil i = None;
    tpZ_ext : forall t t', (forall i, tpZ_rd t i = tpZ_rd t' i) -> t = t';           (* Extensionnality *)
    tpZ_fin : forall t, exists n, forall i, n < Z.abs i -> tpZ_rd t i = None;       (* Tape is logically finite *) *)
  }.

  Section tape_Z_props.

    Variable T : tape_Z.

    Implicit Type t : tpZ T.

    Fact tpZ_mv_wr t i j a : tpZ_mv _ (tpZ_wr _ t i a) j = tpZ_wr _ (tpZ_mv _ t j) (i+j) a.
    Proof. rewrite tpZ_wr_mv; do 2 f_equal; ring. Qed.

  End tape_Z_props.

  (** tape where reads/writes occur at the current position *)

  Record tape_0 : Type := {
    tp0    :> Type;
    tp0_rd0 : tp0 -> option Σ;
    tp0_wr0 : tp0 -> Σ -> tp0;
    tp0_lft : tp0 -> tp0;                        (* -1 *)
    tp0_rt  : tp0 -> tp0;                        (* +1 *)
    tp0_lr  : forall t, tp0_lft (tp0_rt t) = t;
    tp0_rl  : forall t, tp0_rt (tp0_lft t) = t;
    tp0_rd_wr : forall t a, tp0_rd0 (tp0_wr0 t a) = Some a;
    tp0_rd_lwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_lft n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_lft n t);
    tp0_rd_rwr : forall t n a, (0 < n)%nat -> tp0_rd0 (iter tp0_rt  n (tp0_wr0 t a)) 
                                            = tp0_rd0 (iter tp0_rt  n t);
  }.

  Section tape_0_props.

    (* Building a tape_Z with a tape_0 *)

    Variable T : tape_0.

    Implicit Type t : tp0 T.

    Definition tp0_mv t i := iterZ (tp0_lft _) (tp0_rt _) i t.

    Definition tp0_rd t i := tp0_rd0 _ (tp0_mv t (-i)).
    Definition tp0_wr t i a := tp0_mv (tp0_wr0 _ (tp0_mv t (-i)) a) i.

    Hint Resolve tp0_lr tp0_rl : core.

    Definition tp0_tp : tape_Z.
    Proof.
      exists (tp0 T) tp0_rd tp0_wr tp0_mv.
      + intros t i j; unfold tp0_rd, tp0_mv.
        rewrite iterZ_plus; do 2 f_equal; auto; lia.
      + intros t i j a; unfold tp0_wr, tp0_mv.
        rewrite !iterZ_plus; auto.
        f_equal; try lia.
        do 2 f_equal; lia.
      + intros t i j; unfold tp0_mv.
        rewrite iterZ_plus; auto.
      + intros t i j a <-.
        unfold tp0_rd, tp0_wr, tp0_mv.
        rewrite iterZ_plus; auto.
        replace (i+-i) with 0 by ring.
        rewrite iterZ_0.
        rewrite tp0_rd_wr; auto.
      + intros t i j a H.
        unfold tp0_rd, tp0_wr, tp0_mv.
        rewrite iterZ_plus; auto.
        destruct (Z_dec i j) as [ [ D | D ] | ]; try lia.
        * rewrite iterZ_abs_l; auto; try lia.
          rewrite tp0_rd_lwr; try lia.
          rewrite <- iterZ_abs_l with (r := tp0_rt _); auto; try lia.
          rewrite iterZ_plus; auto; do 2 f_equal; ring.
        * rewrite iterZ_abs_r; auto; try lia.
          rewrite tp0_rd_rwr; try lia.
          rewrite <- iterZ_abs_r with (l := tp0_lft _); auto; try lia.
          rewrite iterZ_plus; auto; do 2 f_equal; ring.
    Qed.

   End tape_0_props.

End tapes.