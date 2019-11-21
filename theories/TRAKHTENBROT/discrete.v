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
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec fin_quotient.

From Undecidability.TRAKHTENBROT
  Require Import notations gfp fol_ops fo_terms fo_logic fo_definable fo_sat.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section discrete_quotient.

  (** We assume a finite sub-signature, a finite and decidable model and a valuation 
      and we build the greatest bisimulation for this model, establishing that it
      is decidable and thus we can quotient the model under this bisim obtaining
      a discrete model which is "equivalent" *)

  Variables (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ)).

  Definition fo_bisimilar X M x y := 
         forall A φ, incl (fol_syms A) ls
                  -> incl (fol_rels A) lr
                  -> @fol_sem Σ X M (φ↑x) A <-> fol_sem M (φ↑y) A.

  Variables (X : Type) (fin : finite_t X) 
            (M : fo_model Σ X) (dec : fo_model_dec M).

  Implicit Type (R T : X -> X -> Prop).

  (** Construction of the greatest fixpoint of the following operator fom_op.
      Any prefixpoint R ⊆ fom_op R is a simulation for the model
    *)

  Let fom_op R x y :=
       (forall s, In s ls -> forall (v : vec _ (ar_syms Σ s)) p, R (fom_syms M s (v[x/p])) (fom_syms M s (v[y/p]))) 
    /\ (forall s, In s lr -> forall (v : vec _ (ar_rels Σ s)) p, fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p])).

  (** First we show properties of fom_op 

      a) Monotonicity
      b) preserves Reflexivity, Symmetry and Transitivity
      c) preserves Decidability
      d) preserves FO definability
*)

  Hint Resolve finite_t_pos finite_t_vec.
 
  Let fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof. intros ? ? ? []; split; intros; auto. Qed. 

  Let fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. intros []; split; auto; tauto. Qed.

  Let fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof. intros []; split; intros; auto; symmetry; auto. Qed.

  Let fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    intros (y & H1 & H2); split; intros s Hs v p.
    + exists (fom_syms M s (v[y/p])); split; [ apply H1 | apply H2 ]; auto.
    + transitivity (fom_rels M s (v[y/p])); [ apply H1 | apply H2 ]; auto.
  Qed.

  Let fom_op_dec R : (forall x y, { R x y } + { ~ R x y })
                  -> (forall x y, { fom_op R x y } + { ~ fom_op R x y }).
  Proof.
    intros HR x y.
    apply (fol_bin_sem_dec fol_conj).
    + apply forall_list_sem_dec; intros.
      do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
    + apply forall_list_sem_dec; intros.
      do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
      apply (fol_bin_sem_dec fol_conj); 
        apply (fol_bin_sem_dec fol_imp); auto.
  Qed.

  Tactic Notation "solve" "with" "proj" constr(t) :=
    apply fot_def_equiv with (f := fun φ => φ t); fol def; intros; rew vec.

  Let fol_def_fom_op R : fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
                      -> fol_definable ls lr M (fun ψ => fom_op R (ψ 0) (ψ 1)).
  Proof.
    intros H.
    apply fol_def_conj.
    + apply fol_def_list_fa; intros s Hs;
      apply fol_def_vec_fa;
      apply fol_def_finite_fa; auto; intro p;
      apply fol_def_subst2; auto.
      * apply fot_def_comp; auto; intro q.
        destruct (pos_eq_dec p q); subst.
        - solve with proj (ar_syms Σ s).
        - solve with proj (pos2nat q).
      * apply fot_def_comp; auto; intro q.
        destruct (pos_eq_dec p q); subst.
        - solve with proj (ar_syms Σ s+1).
        - solve with proj (pos2nat q).
    + apply fol_def_list_fa; intros r Hr;
      apply fol_def_vec_fa;
      apply fol_def_finite_fa; auto; intro p;
      apply fol_def_iff.
      * apply fol_def_atom; auto; intro q.
        destruct (pos_eq_dec p q); subst.
        - solve with proj (ar_rels Σ r).
        - solve with proj (pos2nat q).
      * apply fol_def_atom; auto; intro q.
        destruct (pos_eq_dec p q); subst.
        - solve with proj (ar_rels Σ r+1).
        - solve with proj (pos2nat q).
  Qed.

  (** Now we build the greatest fixpoint fom_eq and show its properties

      a) it is an equivalence relation
      b) it is a congruence wrt to the model functions and relations
      c) it is decidable and FO definable

      the reason is that it is obtained after finitely many iterations of fom_op

    *)

  Reserved Notation "x ≡ y" (at level 70, no associativity).

  Definition fom_eq := gfp fom_op.

  Infix "≡" := fom_eq.

  Let fom_eq_equiv : equiv _ fom_eq.
  Proof. apply gfp_equiv; auto. Qed.

  (** This involves the w-continuity of fom_op *)

  Let fom_eq_fix x y : fom_op fom_eq x y <-> x ≡ y.
  Proof. 
    apply gfp_fix; auto; clear x y.
    intros f Hf x y H; split; intros s Hs v p.
    + intros n.
      generalize (H n); intros (H1 & H2).
      apply H1; auto.
    + apply (H 0); auto.
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

  Fact fom_eq_syms x y s v p : In s ls -> x ≡ y -> fom_syms M s (v[x/p]) ≡ fom_syms M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 
    
  Fact fom_eq_rels x y s v p : In s lr -> x ≡ y -> fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed.

  Hint Resolve fom_eq_refl fom_eq_sym fom_eq_trans fom_eq_syms fom_eq_rels.

  Theorem fom_eq_syms_full s v w : In s ls -> (forall p, v#>p ≡ w#>p) -> fom_syms M s v ≡ fom_syms M s w.
  Proof. intro; apply map_vec_pos_equiv; eauto. Qed.

  Theorem fom_eq_rels_full s v w : In s lr -> (forall p, v#>p ≡ w#>p) -> fom_rels M s v <-> fom_rels M s w.
  Proof. intro; apply map_vec_pos_equiv; eauto; tauto. Qed.

  (** And because the signature is finite (ie the symbols and relations) 
                  the model M is finite and composed of decidable relations 

      We do have a decidable equivalence here *) 

  Fact fom_eq_dec : forall x y, { x ≡ y } + { ~ x ≡ y }.
  Proof. apply gfp_decidable; auto. Qed.

  (** But we have a much stronger statement: fom_eq is first order definable *)

  Theorem fom_eq_finite : { n | forall x y, x ≡ y <-> iter fom_op (fun _ _ => True) n x y }.
  Proof. apply gfp_finite_t; auto. Qed.

  Theorem fom_eq_fol_def : fol_definable ls lr M (fun φ => fom_eq (φ 0) (φ 1)).
  Proof.
    destruct fom_eq_finite as (n & Hn).
    apply fol_def_equiv with (R := fun φ => iter fom_op (fun _ _ : X => True) n (φ 0) (φ 1)).
    + intro; rewrite <- Hn; tauto.
    + clear Hn; induction n as [ | n IHn ].
      * simpl; fol def.
      * rewrite iter_S; auto.
  Qed.

  Hint Resolve fom_eq_dec.

  (** First order indistinguishability upto formulae built with functions and constants in 
      ls and relations in ls *)

  Section fol_characterization.

    (** We show that the greatest bisimulation is equivalent to FOL undistinguishability ie 
        This result is purely for the sake of completeness of the description of fom_eq,
        it is not used in the reduction below 

        It state that x and y are bisimilar iff the is no interpretation of a FO formula 
        with one free variable that can distinguish x from y *)

    Hint Resolve fom_eq_syms_full fom_eq_rels_full.

    Let fom_eq_fol_charac1 A phi psi : 
            (forall n, In n (fol_vars A) -> phi n ≡ psi n)
         -> incl (fol_syms A) ls
         -> incl (fol_rels A) lr
         -> fol_sem M phi A <-> fol_sem M psi A.
    Proof.
      intros Hp; apply fo_model_simulation with (R := fom_eq); auto;
        intros a; exists a; auto.
    Qed.

    (** Can this be restricted to FO formula where only £0 is free ? 

        replace A with ∀ A ...

        by replacing £(2+n) with £0 we can already get A to have only
        £0 and £1 but how to get a single variable ?

        x = y <-> A[x,y] 

       If the model is discrete, on can build the finite list of decidable
       predicates as finite unions of (eq x). It should be possible
       to characterize (eq x) as the conjection of all the FO formula
       that satisfy x, hence we get Ax st that   Ax[y] <-> x = y

       Hence we can could show, x = y <-> forall A[.], A[x] <-> A[y]
       when A only has one £0 as variable

      *)

    Theorem fom_eq_fol_characterization x y : 
            x ≡ y <-> fo_bisimilar M x y.
    Proof.
      split.
      + intros H A phi.
        apply fom_eq_fol_charac1.
        intros [ | n ] _; simpl; auto.
      + intros H.
        destruct fom_eq_fol_def as (A & Hs & Hr & HA).
        generalize (H A (fun _ => y) Hs Hr).
        do 2 rewrite HA; simpl; intros E; apply E; auto.
    Qed.

  End fol_characterization.

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

    Let H1 s v : In s ls -> cls (fom_syms M s v) = fom_syms Md s (vec_map cls v).
    Proof.
      intros Hs; simpl.
      apply E2.
      apply fom_eq_syms_full; auto.
      intros p; rewrite vec_map_map, vec_pos_map.
      apply E2; rewrite E1; auto.
    Qed.

    Let H2 s v : In s lr -> fom_rels M s v <-> fom_rels Md s (vec_map cls v).
    Proof.
      intros Hs; simpl.
      apply fom_eq_rels_full; auto.
      intros p; rewrite vec_map_map, vec_pos_map.
      apply E2; rewrite E1; auto.
    Qed.

    Let H3 A phi : incl (fol_syms A) ls 
                -> incl (fol_rels A) lr
                -> fol_sem M phi A 
               <-> fol_sem Md (fun n => cls (phi n)) A.
    Proof.
      intros Hs Hr.
      apply fo_model_projection with (1 := E1) (5 := Hs) (6 := Hr); auto.
    Qed.

    Let H4 p q : fo_bisimilar Md p q -> p = q.
    Proof.
      intros H.
      rewrite <- (E1 q), <- (E1 p).
      apply E2, fom_eq_fol_characterization.
      intros A phi Hs Hr.
      specialize (H A (fun p => cls (phi p)) Hs Hr).
      revert H; apply fol_equiv_impl.
      all: rewrite H3; auto; apply fol_sem_ext; intros []; now simpl.
    Qed.

    (** Every finite & decidable model can be projected to pos n
        with decidable relations and such that identity is exactly
        FO undistinguishability *)

    Check fo_bisimilar.

    Theorem fo_fin_model_discretize : 
      { n : nat & 
        { Md : fo_model Σ (pos n) &
          {_ : fo_model_dec Md & 
            { i : X -> pos n &
              { j : pos n -> X |
                  (forall x, i (j x) = x)
               /\ (forall s v, In s ls -> i (fom_syms M s v) = fom_syms Md s (vec_map i v))
               /\ (forall s v, In s lr -> fom_rels M s v <-> fom_rels Md s (vec_map i v))
               /\ (forall A φ, incl (fol_syms A) ls 
                            -> incl (fol_rels A) lr
                            -> fol_sem M  φ                  A 
                           <-> fol_sem Md (fun n => i (φ n)) A)
               /\ (forall p q, fo_bisimilar Md p q -> p = q)
                 } } } } }.
    Proof.
      exists n, Md; exists.
      { intros x y; simpl; apply dec. }
      exists cls, repr; msplit 3; auto.
    Qed.

  End build_the_model.

End discrete_quotient.

Check fo_fin_model_discretize.
Print Assumptions fo_fin_model_discretize.

Section discrete_removal.

  (** Provided the signature has finitely (listable) many functional symbols 
      and finitely many relational symbols, satisfiability of A in a finite
      and decidable model implies satisfiability of A in a finite, decidable
      and discrete model, in fact in a model based on the finite type (pos n) *)

  Theorem fo_discrete_removal Σ A :
             @fo_form_fin_dec_SAT Σ A
          -> (exists n, @fo_form_fin_discr_dec_SAT_in Σ A (pos n)).
  Proof.
    intros (X & M & Hfin & Hdec & phi & HA).
    set (ls := fol_syms A).
    set (lr := fol_rels A).
    destruct (fo_fin_model_discretize ls lr Hfin Hdec)
      as (n & Md & Mdec & i & j & E1 & E2 & E3 & _).
    set (psy n := i (phi n)).
    exists n, (@pos_eq_dec _), Md, (finite_t_pos _) , Mdec, psy.
    revert HA.
    apply fo_model_projection with (1 := E1) (ls := ls) (lr := lr); 
      unfold lr, ls; auto; apply incl_refl.
  Qed.

End discrete_removal.

Check fo_discrete_removal.
Print Assumptions fo_discrete_removal.

Theorem fo_form_fin_dec_SAT_fin_discr_dec Σ A :
            @fo_form_fin_dec_SAT Σ A 
         -> fo_form_fin_discr_dec_SAT A.
Proof.
  intros H.
  destruct fo_discrete_removal with (1 := H) (A := A)
    as (n & Hn); auto.
  exists (pos n); auto.
Qed.

Check fo_form_fin_dec_SAT_fin_discr_dec.
Print Assumptions fo_form_fin_dec_SAT_fin_discr_dec.
