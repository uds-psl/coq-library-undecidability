(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos fin_quotient vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic fin_upto.

Set Implicit Arguments.

Local Definition forall_equiv X := @fol_quant_sem_ext X fol_fa.
Local Definition exists_equiv X := @fol_quant_sem_ext X fol_ex.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section map_vec_pos_equiv.

  Variable (X : Type) (R : X -> X -> Prop)
           (Y : Type) (T : Y -> Y -> Prop)
           (T_refl : forall y, T y y)
           (T_trans : forall x y z, T x y -> T y z -> T x z). 

  Theorem map_vec_pos_equiv n (f : vec X n -> Y) : 
           (forall p v x y, R x y -> T (f (v[x/p])) (f (v[y/p])))
        -> forall v w, (forall p, R (v#>p) (w#>p)) -> T (f v) (f w).
  Proof.
    revert f; induction n as [ | n IHn ]; intros f Hf v w H.
    + vec nil v; vec nil w; auto.
    + unfold transitive in T_trans.
      apply T_trans with (y := f (v[(w#>pos0)/pos0])).
      * rewrite <- (vec_change_same v pos0) at 1; auto.
      * revert H.
        vec split v with a; vec split w with b; intros H; simpl.
        apply IHn with (f := fun v => f(b##v)).
        - intros p q x y Hxy.
          apply (Hf (pos_nxt p) (b##q)); auto.
        - intros p; apply (H (pos_nxt p)).
  Qed. 

End map_vec_pos_equiv.

Section gfp.

  Variable (M : Type). 

  Implicit Type (R T : M -> M -> Prop).

  Notation "R ⊆ T" := (forall x y, R x y -> T x y).

  Notation "R 'o' T" := (fun x z => exists y, R x y /\ T y z) (at level 58).

  Let incl_trans R S T : R ⊆ S -> S ⊆ T -> R ⊆ T.
  Proof. firstorder. Qed.

  Let comp_mono R R' T T' : R ⊆ R' -> T ⊆ T' -> R o T ⊆ R' o T'.
  Proof. firstorder. Qed. 

  Variable (F : (M -> M -> Prop) -> M -> M -> Prop)
           (HF0 : forall R T, R ⊆ T -> F R ⊆ F T).

  Let sym R := fun x y => R y x.

  Let i := iter F (fun _ _ => True).

  Let iS n : i (S n) = F (i n).
  Proof. apply iter_S. Qed.

  Let i0 : i 0 = fun _ _ => True.
  Proof. auto. Qed.

  Let i_S n : i (S n) ⊆ i n.
  Proof.
    unfold i.
    induction n as [ | n IHn ].
    + simpl; auto.
    + intros x y.
      rewrite iter_S with (n := n).
      rewrite iter_S.
      apply HF0, IHn.
  Qed.

  Let i_decr n m : n <= m -> i m ⊆ i n.
  Proof. induction 1; auto. Qed.

  Definition gfp x y := forall n, i n x y.

  Notation I := (@eq M).

  Hypothesis HF1 : I ⊆ F I.

  Let i_refl n : I ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := HF1), HF0, IHn.
  Qed.
  
  Let gfp_refl : I ⊆ gfp.
  Proof.
    intros x y [] n.
    apply i_refl; auto.
  Qed.

  Hypothesis HF2 : forall R, sym (F R) ⊆ F (sym R).

  Let i_sym n : sym (i n) ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + intros x y; unfold i; simpl; auto.
    + rewrite iS.
      apply incl_trans with (2 := HF0 _ IHn), HF2.
  Qed.

  Let gfp_sym : sym gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_sym, H.
  Qed.

  Hypothesis HF3 : forall R, F R o F R ⊆ F (R o R).

  Let i_trans n : i n o i n ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := @HF3 _), HF0, IHn.
  Qed.

  Let gfp_trans : gfp o gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_trans.
    revert H; apply comp_mono; auto.
  Qed.

  Fact gfp_equiv : equiv _ gfp.
  Proof.
    msplit 2.
    + intro; apply gfp_refl; auto.
    + intros x y z H1 H2; apply gfp_trans; exists y; auto.
    + intros x y; apply gfp_sym.
  Qed.

  Let gfp_fix1 : F gfp ⊆ gfp.
  Proof.
    intros x y H n.
    apply i_S; rewrite iS.
    revert H; apply HF0; auto.
  Qed.

  (** This is omega continuity *)

  Variable HF4 : forall (s : nat -> M -> M -> Prop), 
                        (forall n m, n <= m -> s m ⊆ s n) 
                     -> (fun x y => forall n, F (s n) x y) ⊆ F (fun x y => forall n, s n x y).

  Let gfp_fix0 : gfp ⊆ F gfp.
  Proof.
    intros x y H.
    apply HF4; auto.
    intro; rewrite <- iS; apply H.
  Qed.

  Fact gfp_fix x y : F gfp x y <-> gfp x y.
  Proof. split; auto. Qed.

  (** This is for decidability *)

  Let dec R := forall x y, { R x y } + { ~ R x y }.

  Variable HF5 : forall R, dec R -> dec (F R).

  Let i_dec n : dec (i n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; left; auto.
    + rewrite iS; apply HF5; auto.
  Qed.

  (** For the decidability of gfp, we need the finiteness
      so that gfp = i n for a sufficiently large n *)

  (** There is a list lR of relations which contains every
      i n upto equivalence (because X is finite_t)

      By the (generalized) PHP, for n greater than
      the length of lR, one can find a duplicate
      in the list [i 0; ...;i n] ie a < b <= n such
      that i a ~ T1 ~ T2 ~ i b

      Then one can deduce i a ~ i (S a) ~ gfp *)

  Let i_dup n m : n < m -> i n ⊆ i m -> forall k, n <= k -> forall x y, gfp x y <-> i k x y.
  Proof.
    intros H1 H2.
    generalize (i_decr H1) (i_S n); rewrite iS; intros H3 H4.
    generalize (incl_trans _ _ _ H2 H3); intros H5.
    assert (forall p, i n ⊆ i (p+n)) as H6.
    { induction p as [ | p IHp ]; auto.
      simpl plus; rewrite iS.
      apply incl_trans with (1 := H5), HF0; auto. }
    intros k Hk x y; split; auto.
    intros H a.
    destruct (le_lt_dec a k).
    + revert H; apply i_decr; auto.
    + replace a with (a-n+n) by lia.
      apply H6.
      revert H; apply i_decr; auto.
  Qed.
 
  Let gfp_finite_dec b : (exists n m, n < m <= b /\ i n ⊆ i m) -> dec gfp.
  Proof.
    intros H.
    assert (forall x y, gfp x y <-> i b x y) as H1.
    { destruct H as (n & m & H1 & H2). 
      apply i_dup with (2 := H2); auto; try lia. }
    intros x y.
    destruct (i_dec b x y); [ left | right ]; rewrite H1; auto.
  Qed.

  Variable HF6 : finite_t M.

  Theorem gfp_decidable : dec gfp.
  Proof.
    destruct finite_t_weak_dec_rels with (1 := HF6)
      as (mR & HmR).
    set (l := map i (list_an 0 (S (length mR)))).
    apply (@gfp_finite_dec (S (length mR))).
    destruct php_upto 
      with (R := fun R T => forall x y, R x y <-> T x y)
           (l := l) (m := mR)
      as (a & R & b & T & c & H1 & H2).
    + intros R S H ? ?; rewrite H; tauto.
    + intros R S T H1 H2 ? ?; rewrite H1, H2; tauto.
    + intros R HR.
      apply in_map_iff in HR.
      destruct HR as (n & <- & _).
      destruct (HmR (i n)) as (T & H1 & H2).
      * intros x y; destruct (i_dec n x y); tauto.
      * exists T; auto.
    + unfold l; rewrite map_length, list_an_length; auto.
    + unfold l in H1.
      apply map_middle_inv in H1.
      destruct H1 as (a' & n & r' & H1 & H3 & H4 & H5).
      apply map_middle_inv in H5.
      destruct H5 as (b' & m & c' & H5 & H6 & H7 & H8).
      exists n, m; rewrite H4, H7; split; try (intros ? ?; apply H2).
      clear H3 H4 H6 H7 H8 H2; subst r'.
      generalize H1; intros H2.
      apply f_equal with (f := @length _) in H2.
      rewrite list_an_length, app_length in H2.
      simpl in H2; rewrite app_length in H2; simpl in H2.
      apply list_an_app_inv in H1.
      destruct H1 as (_ & H1); simpl in H1.
      injection H1; clear H1; intros H1 H3.
      symmetry in H1.
      apply list_an_app_inv in H1.
      destruct H1 as (_ & H1); simpl in H1.
      injection H1; clear H1; intros _ H1.
      lia.
  Qed.

End gfp.

Section discrete_quotient.

  Variables (Σ : fo_signature) 
            (HΣs : finite_t (syms Σ))
            (HΣr : finite_t (rels Σ))
            (X : Type) (M : fo_model Σ X)  
            (fin : finite_t X) 
            (dec : fo_model_dec M)
            (φ : nat -> X).

  Implicit Type (R T : X -> X -> Prop).

  (** Construction of the greatest fixpoint of the following operator *)

  Let fom_op R x y :=
       (forall s (v : vec _ (ar_syms Σ s)) p, R (fom_syms M s (v[x/p])) (fom_syms M s (v[y/p]))) 
    /\ (forall s (v : vec _ (ar_rels Σ s)) p, fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p])).

  Let fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof.
    intros H x y (H1 & H2); split; intros; auto.
  Qed. 

  Let fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. intros []; split; auto; tauto. Qed.

  Let fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof.
    intros (H1 & H2); split; intros; auto.
    symmetry; auto.
  Qed.

  Let fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    intros (y & H1 & H2); split; intros s v p.
    + exists (fom_syms M s (v[y/p])); split.
      * apply H1.
      * apply H2.
    + transitivity (fom_rels M s (v[y/p])).
      * apply H1.
      * apply H2.
  Qed.

  Reserved Notation "x ≃ y" (at level 70, no associativity).

  Definition fom_eq := gfp fom_op.

  Infix "≃" := fom_eq.

  Let fom_eq_equiv : equiv _ fom_eq.
  Proof. apply gfp_equiv; auto. Qed.

  (** This involves the w-continuity of fom_op *)

  Let fom_eq_fix x y : fom_op fom_eq x y <-> fom_eq x y.
  Proof. 
    apply gfp_fix; auto; clear x y.
    intros f Hf x y H; split; intros s v p.
    + intros n.
      generalize (H n); intros (H1 & H2).
      apply H1.
    + apply (H 0).
  Qed.

  (** We build the greatest bisimulation which is an equivalence 
      and a fixpoint for the above operator *) 

  Fact fom_eq_refl x : x ≃ x.
  Proof. apply (proj1 fom_eq_equiv). Qed.

  Fact fom_eq_sym x y : x ≃ y -> y ≃ x.
  Proof. apply fom_eq_equiv. Qed.

  Fact fom_eq_trans x y z : x ≃ y -> y ≃ z -> x ≃ z.
  Proof. apply fom_eq_equiv. Qed.

  Fact fom_eq_syms x y s v p : x ≃ y -> fom_syms M s (v[x/p]) ≃ fom_syms M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 
    
  Fact fom_eq_rels x y s v p : x ≃ y -> fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed.

  Hint Resolve fom_eq_refl fom_eq_sym fom_eq_trans fom_eq_syms fom_eq_rels.

  Theorem fom_eq_syms_full s v w : (forall p, v#>p ≃ w#>p) -> fom_syms M s v ≃ fom_syms M s w.
  Proof. apply map_vec_pos_equiv; eauto. Qed.

  Theorem fom_eq_rels_full s v w : (forall p, v#>p ≃ w#>p) -> fom_rels M s v <-> fom_rels M s w.
  Proof. apply map_vec_pos_equiv; eauto; tauto. Qed.

  Hint Resolve finite_t_vec finite_t_pos. 

  (** And because the signature is finite (ie the symbols and relations) 
                  the model M is finite and composed of decidable relations 

      We do have a decidable equivalence here *) 
 
  Fact fom_eq_dec : forall x y, { x ≃ y } + { ~ x ≃ y }.
  Proof.
    apply gfp_decidable; auto.
    intros R HR x y.
    apply (fol_bin_sem_dec fol_conj).
    + do 3 (apply (fol_quant_sem_dec fol_fa); auto; intros).
    + do 3 (apply (fol_quant_sem_dec fol_fa); auto; intros).
      apply (fol_bin_sem_dec fol_conj); 
        apply (fol_bin_sem_dec fol_imp); auto.
  Qed.

  Hint Resolve fom_eq_dec.

  (** And now we can build a discrete model with this equivalence 

      There is a (full) surjection from a discrete model based
      on pos n to M which preserves the semantics

    *)

  Section build_the_model.

    Let l := proj1_sig fin.
    Let Hl : forall x, In x l := proj2_sig fin.


    Let Q : fin_quotient fom_eq.
    Proof.
      apply decidable_EQUIV_fin_quotient with (l := l); eauto.
    Qed.

    Let n := fq_size Q.
    Let cls := fq_class Q.
    Let repr := fq_repr Q.
    Let E1 p : cls (repr p) = p.           Proof. apply fq_surj. Qed.
    Let E2 x y : x ≃ y <-> cls x = cls y.  Proof. apply fq_equiv. Qed.

    Let Md : fo_model Σ (pos n).
    Proof.
      exists.
      + intros s v; apply cls, (fom_syms M s), (vec_map repr v).
      + intros s v; apply (fom_rels M s), (vec_map repr v).
    Defined.

    Theorem fo_fin_model_discretize : 
      { n : nat & 
        { Md : fo_model Σ (pos n) &
          {_ : fo_model_dec Md & 
            { i : X -> pos n &
              { j : pos n -> X |
                  (forall x, i (j x) = x)
               /\ (forall s v, i (fom_syms M s v) = fom_syms Md s (vec_map i v))
               /\ (forall s v, fom_rels M s v <-> fom_rels Md s (vec_map i v))
                 } } } } }.
    Proof.
      exists n, Md; exists.
      { intros x y; simpl; apply dec. }
      exists cls, repr; msplit 2; auto.
      + intros s v; simpl.
        apply E2.
        apply fom_eq_syms_full.
        intros p; rewrite vec_map_map, vec_pos_map.
        apply E2; rewrite E1; auto.
      + intros s v; simpl.
        apply fom_eq_rels_full.
        intros p; rewrite vec_map_map, vec_pos_map.
        apply E2; rewrite E1; auto.
    Qed.

  End build_the_model.

End discrete_quotient.

Check fo_fin_model_discretize.
Print Assumptions fo_fin_model_discretize.


