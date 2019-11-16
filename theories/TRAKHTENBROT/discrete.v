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
  Require Import pos vec fin_quotient.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic gfp.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section discrete_quotient.

  (** We assume a finite signature, a finite and decidable model and a valuation 
      and we build the greatest bisimulation for this model, establishing that it
      is decidable and thus we can quotient the model under this bisim obtaining
      a discrete model which is "equivalent" *)

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
  Proof. intros ? ? ? []; split; intros; auto. Qed. 

  Let fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. intros []; split; auto; tauto. Qed.

  Let fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof. intros []; split; intros; auto; symmetry; auto. Qed.

  Let fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    intros (y & H1 & H2); split; intros s v p.
    + exists (fom_syms M s (v[y/p])); split; [ apply H1 | apply H2 ].
    + transitivity (fom_rels M s (v[y/p])); [ apply H1 | apply H2 ].
  Qed.

  Reserved Notation "x ≡ y" (at level 70, no associativity).

  Definition fom_eq := gfp fom_op.

  Infix "≡" := fom_eq.

  Let fom_eq_equiv : equiv _ fom_eq.
  Proof. apply gfp_equiv; auto. Qed.

  (** This involves the w-continuity of fom_op *)

  Let fom_eq_fix x y : fom_op fom_eq x y <-> x ≡ y.
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

  Fact fom_eq_refl x : x ≡ x.
  Proof. apply (proj1 fom_eq_equiv). Qed.

  Fact fom_eq_sym x y : x ≡ y -> y ≡ x.
  Proof. apply fom_eq_equiv. Qed.

  Fact fom_eq_trans x y z : x ≡ y -> y ≡ z -> x ≡ z.
  Proof. apply fom_eq_equiv. Qed.

  (* It is a congruence wrt to the model *)

  Fact fom_eq_syms x y s v p : x ≡ y -> fom_syms M s (v[x/p]) ≡ fom_syms M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 
    
  Fact fom_eq_rels x y s v p : x ≡ y -> fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed.

  Hint Resolve fom_eq_refl fom_eq_sym fom_eq_trans fom_eq_syms fom_eq_rels.

  Theorem fom_eq_syms_full s v w : (forall p, v#>p ≡ w#>p) -> fom_syms M s v ≡ fom_syms M s w.
  Proof. apply map_vec_pos_equiv; eauto. Qed.

  Theorem fom_eq_rels_full s v w : (forall p, v#>p ≡ w#>p) -> fom_rels M s v <-> fom_rels M s w.
  Proof. apply map_vec_pos_equiv; eauto; tauto. Qed.

  Hint Resolve finite_t_vec finite_t_pos. 

  (** And because the signature is finite (ie the symbols and relations) 
                  the model M is finite and composed of decidable relations 

      We do have a decidable equivalence here *) 
 
  Fact fom_eq_dec : forall x y, { x ≡ y } + { ~ x ≡ y }.
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
    Proof. apply decidable_EQUIV_fin_quotient with (l := l); eauto. Qed.

    Let n := fq_size Q.
    Let cls := fq_class Q.
    Let repr := fq_repr Q.
    Let E1 p : cls (repr p) = p.              Proof. apply fq_surj. Qed.
    Let E2 x y : x ≡ y <-> cls x = cls y.     Proof. apply fq_equiv. Qed.

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

Section model_equiv.

  Variable (Σ : fo_signature) 
           (X : Type) (M : fo_model Σ X) 
           (Y : Type) (K : fo_model Σ Y) 
           (i : X -> Y) (j : Y -> X) (E : forall x, i (j x) = x)
           (Hs : forall s v, i (fom_syms M s v) = fom_syms K s (vec_map i v))
           (Hr : forall s v, fom_rels M s v <-> fom_rels K s (vec_map i v)).

  Theorem fo_model_project_equiv A phi psi :
           (forall n, i (phi n) = psi n) 
        -> fol_sem M phi A <-> fol_sem K psi A.
  Proof.
    revert phi psi.
    induction A as [ | s | b A HA B HB | q A HA ]; try (simpl; tauto); intros phi psi E'.
    + simpl; rewrite Hr, vec_map_map.
      match goal with |- ?x <-> ?y => cut (x = y); [ intros ->; tauto | ] end.
      f_equal; apply vec_map_ext; intros t _; clear s v.
      induction t as [ k | s v ]; rew fot; auto.
      rewrite Hs, vec_map_map; f_equal.
      apply vec_map_ext; auto.
    + apply fol_bin_sem_ext; auto.
    + destruct q; simpl; split.
      * intros (x & Hx).
        exists (i x).
        revert Hx; apply HA.
        intros []; simpl; auto.
      * intros (y & Hy).
        exists (j y).
        revert Hy; apply HA.
        intros []; simpl; auto.
      * intros H y. 
        generalize (H (j y)); apply HA.
        intros []; simpl; auto.
      * intros H x. 
        generalize (H (i x)); apply HA.
        intros []; simpl; auto.
  Qed.

End model_equiv.

Section discrete_removal.

  (** Provided the signature has finitely (listable) many functional symbols 
      and finitely many relational symbols, satisfiability of A in a finite
      and decidable model implies satisfiability of A in a finite, decidable
      and discrete model, in fact in a model based on the finite type (pos n) *)

  Theorem fo_discrete_removal Σ (Hs : finite_t (syms Σ)) (Hr : finite_t (rels Σ)) A :
             @fo_form_fin_dec_SAT Σ A
          -> (exists n, @fo_form_fin_discr_dec_SAT_in Σ A (pos n)).
  Proof.
    intros (X & M & Hfin & Hdec & phi & HA).
    destruct (fo_fin_model_discretize Hs Hr Hfin Hdec)
      as (n & Md & Mdec & i & j & E1 & E2 & E3).
    set (psy n := i (phi n)).
    exists n, (@pos_eq_dec _), Md, (finite_t_pos _) , Mdec, psy.
    revert HA.
    apply fo_model_project_equiv with (1 := E1); auto.
  Qed.

End discrete_removal.

Check fo_discrete_removal.
Print Assumptions fo_discrete_removal.

Theorem fo_form_fin_dec_SAT_fin_discr_dec Σ A :
            finite_t (syms Σ)
         -> finite_t (rels Σ)
         -> @fo_form_fin_dec_SAT Σ A 
         -> fo_form_fin_discr_dec_SAT A.
Proof.
  intros Hs Hr H.
  destruct fo_discrete_removal with (3 := H) (A := A)
    as (n & Hn); auto.
  exists (pos n); auto.
Qed.
