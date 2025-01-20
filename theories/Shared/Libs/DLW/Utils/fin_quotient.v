(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia Permutation.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_list utils_decidable fin_base.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import measure_ind.

Set Implicit Arguments.

(* * Finite quotient by a decidable equivalence *)

Section fp_quotient.

  Variable (X : Type).
 
  Implicit Type (R : X -> X -> Prop).

  Record fp_quotient R := Mk_finite_partial_quotient {
    fpq_size : nat;
    fpq_class : X -> option (pos fpq_size);
    fpq_repr : pos fpq_size -> X;
    fpq_eq : forall c, fpq_class (fpq_repr c) = Some c;
    fpq_None : forall x, ~ R x x <-> fpq_class x = None;
    fpq_Some : forall x y, R x y <-> fpq_class x = fpq_class y /\ fpq_class x <> None;
  }.

  Local Definition per R := 
     (forall x y, R x y -> R y x) /\ (forall x y z, R x y -> R y z -> R x z).
  Local Definition dec R := 
      forall x y, { R x y } + { ~ R x y }.

  Let Some_inj K (x y : K) : Some x = Some y -> x = y.
  Proof. inversion 1; auto. Qed. 
  
  Theorem decidable_PER_fp_quotient l R : 
            (forall x, R x x <-> exists y, In y l /\ R x y) 
          -> per R -> dec R -> fp_quotient R.
  Proof.
    revert R.
    induction on l as IHl with measure (length l); intros R Hl (H1 & H2) H3.
    destruct l as [ | x l ].
    + exists 0 (fun _ => None) (@pos_O_invert _).
      * intros p; invert pos p.
      * intros x; rewrite Hl; split; auto.
        intros _ (? & [] & _).
      * intros x y; split.
        - intros H4. 
          assert (R x x) as C.
          { apply H2 with y; auto. }
          apply Hl in C.
          destruct C as (? & [] & _).
        - intros (_ & []); auto.
    + destruct list_discrim with (P := R x) (Q := fun y => ~ R x y) (l := l)
        as (lx & m & G1 & G2 & G3).
      1: { intro; apply H3. }
      rewrite Forall_forall in G2, G3.
      set (T u v := ~ R x u /\ R u v).
      destruct (IHl m) with (R := T) as [ n cl rp Q1 Q2 Q3 ].
      * apply Permutation_length in G1; rewrite length_app in G1.
        simpl; lia.
      * intros u; unfold T; split.
        - rewrite Hl.
          intros (F1 & w & [ -> | F2 ] & F3).
          ++ apply H1 in F3; tauto.
          ++ exists w; split; auto.
             apply Permutation_in with (1 := G1), in_app_or in F2.
             destruct F2; auto.
             apply G2 in H.
             contradict F1.
             apply H2 with w; auto.
        - intros (v & F1 & F2 & F3); split; auto.
          apply H2 with v; auto.
      * split.
        - intros u v (F1 & F2); split; auto.
          contradict F1; apply H2 with v; auto.
        - intros a b c (F1 & F2) (F3 & F4); split; auto.
          apply H2 with b; auto.
      * intros u v; unfold T.
        destruct (H3 x u); destruct (H3 u v); tauto.
      * destruct (H3 x x) as [ Hx | Hx ].
        - set (cl' y := match H3 x y with
               | left Hy  => Some (pos0)
               | right Hy => match cl y with
                 | Some p => Some (pos_nxt p)
                 | None => None
               end
             end).
          set (rp' p := match pos_S_inv p with
                | inl _  => x
                | inr (exist _ q _) => rp q
              end).
         exists _ cl' rp'.
         ++ intros p; invert pos p; unfold cl', rp'; simpl.
            ** destruct (H3 x x) as [ | [] ]; auto.
            ** rewrite Q1.
               destruct (H3 x (rp p)) as [ | H ]; auto.
               unfold T in Q2.
               specialize (Q1 p).
               contradict Q1.
               rewrite (proj1 (Q2 _)); try tauto; discriminate.
         ++ intros u; unfold cl'; split.
            ** intros H; destruct (H3 x u) as [ F1 | F1 ].
               { contradict H; apply H2 with x; auto. }
               rewrite (proj1 (Q2 _)); auto.
               intros (? & ?); tauto.
            ** destruct (H3 x u) as [ F1 | F1 ]; try discriminate.
               intros F2 F3.
               destruct (proj1 (Q3 u u)) as (E & ?).
               red; auto.
               destruct (cl u); try discriminate; tauto.
         ++ intros u v; split.
            ** intros H. 
               unfold cl'.
               destruct (H3 x u) as [ F1 | F1 ].
               { split; try discriminate.
                 destruct (H3 x v) as [ F2 | F2 ]; auto.
                 contradict F2; apply H2 with u; auto. }
               destruct (H3 x v) as [ F2 | F2 ].
               { contradict F1; apply H2 with v; auto. }
               destruct (proj1 (Q3 u v)) as (F3 & F4).
               { red; auto. }
               rewrite <- F3.
               destruct (cl u); auto.
               split; auto; discriminate.
            ** intros (F1 & F2); revert F1 F2.
               unfold cl'.
               { destruct (H3 x u) as [ F1 | F1 ];
                 destruct (H3 x v) as [ F2 | F2 ].
                 + intros _ _; apply H2 with x; auto.
                 + destruct (cl v); discriminate.
                 + destruct (cl u); discriminate.
                 + case_eq (cl u).
                   2: intros _ _ []; auto.
                   case_eq (cl v); try discriminate.
                   intros p Hp q Hq E _; apply Q3.
                   rewrite Hp, Hq; split; try discriminate.
                   f_equal.
                   apply Some_inj, pos_nxt_inj in E; subst; auto. }
        - exists _ cl rp; auto.
          ++ intros u; split.
             ** intros H; apply Q2; unfold T; tauto.
             ** intros H; apply Q2 in H; contradict H; split; auto.
                contradict Hx; apply H2 with u; auto.
          ++ intros u v; split.
             ** intros H; apply Q3.
                split; auto.
                contradict Hx; apply H2 with u; auto.
             ** intros H; apply Q3 in H; destruct H; auto.
  Qed.

  Record fin_quotient R := Mk_finite_quotient {
    fq_size : nat;
    fq_class : X -> pos fq_size;
    fq_repr : pos fq_size -> X;
    fq_surj : forall c, fq_class (fq_repr c) = c;
    fq_equiv : forall x y, R x y <-> fq_class x = fq_class y }.

  (* We do not need the type to be finite, only the number of
     equivalent classes need be finite *)

  Theorem decidable_EQUIV_fin_quotient l R :
             (forall x, R x x)
          -> (forall x y, R x y -> R y x)
          -> (forall x y z, R x y -> R y z -> R x z)     (* R is an equivalence *)
          -> (forall x y, { R x y } + { ~ R x y })       (* R is decidable *)
          -> (forall x : X, exists y, In y l /\ R x y)   (* finitely many classes *)
          -> fin_quotient R.
  Proof.
    intros H1 H2 H3 H4 H5.
    destruct (@decidable_PER_fp_quotient l R) 
      as [ n cl rp Q1 Q2 Q3 ]; simpl; auto.
    + intros x; split; auto; intros _; exists x; auto.
    + split; auto.
    + assert (forall x, { y | cl x = Some y }) as H.
      { intros x; case_eq (cl x).
        * intros p; exists p; auto.
        * intros C; exfalso.
          apply Q2 in C.
          apply C; auto. }
      set (cl' x := proj1_sig (H x)).
      assert (H' : forall x, cl x = Some (cl' x)).
      { intros x; apply (proj2_sig (H x)). }
      generalize cl' H'; clear H cl' H'; intros cl' H.
      exists n cl' rp.
      * intro x.
        generalize (Q1 x); rewrite H.
        injection 1; auto.
      * intros x y; rewrite Q3.
        split.
        - intros (C1 & _).
          apply Some_inj; rewrite <- H, <- H; auto.
        - intros E; rewrite H, H, E; split; auto; discriminate.
  Qed.

End fp_quotient.

Section restriction_by_list.

  Variable (X : Type) (R : X -> X -> Prop) (Rper : per R) (Rdec : dec R) 
           (l : list X) (Hl : forall x, In x l -> R x x).

  Let T x y := R x y /\ exists z, In z l /\ R x z.

  Let HT1 x : T x x <-> exists z, In z l /\ T x z.
  Proof.
    split.
    + intros (H1 & z & H2 & H3).
      exists z; split; auto; split; eauto.
    + intros (z & H1 & H2 & y & H3 & H4); split; eauto.
      apply (proj2 Rper) with z; auto.
      apply (proj1 Rper); auto.
  Qed.
  
  Let HT2 : per T.
  Proof.
    split.
    + intros x y (H1 & z & H2 & H3); split.
      * apply (proj1 Rper); auto.
      * exists z; split; auto.
        apply (proj2 Rper) with x; auto.
        apply (proj1 Rper); auto.
    + intros x y z (H1 & a & H2 & H3) (H4 & b & H5 & H6); split; eauto.
      apply (proj2 Rper) with y; auto.
  Qed.

  Let HT3 : dec T.
  Proof.
    intros x y.
    destruct (Rdec x y) as [ H1 | H1 ].
    2: { right; contradict H1; destruct H1; auto. }
    destruct list_choose_dep with (l := l) (P := R x) (Q := fun z => ~ R x z)
      as [ (z & H) | H ].
    + intros; apply Rdec.
    + left; split; eauto.
    + right; intros (_ & z & H2 & H3).
      revert H2 H3; apply H.
  Qed.

  Theorem DEC_PER_list_proj_finite_discrete :
       { D & { _ : dec (@eq D) & { _ : finite_t D & { f : X -> D 
             | forall x y, In x l -> In y l -> R x y <-> f x = f y } } } }.
  Proof using Rper Rdec Hl.
    destruct decidable_PER_fp_quotient with (R := T) (l := l)
      as [ n cls repr G1 G2 G3 ]; auto.
    exists (option (pos n)).
    exists. { red; decide equality; apply pos_eq_dec. }
    exists. { apply finite_t_option, finite_t_pos. }
    exists cls.
    intros x y Hx Hy; split.
    + intros H; apply G3; split; auto; exists y; auto.
    + intros H.
      apply G3; split; auto.
      red; rewrite <- G2.
      intros C; apply C.
      assert (R x x) as H1 by now apply Hl.
      split; eauto.
  Qed.

End restriction_by_list. 
