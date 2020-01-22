(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations decidable gfp fol_ops fo_sig fo_terms fo_logic fo_definable fo_sat.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

Section discrete_quotient.

  (** We show the FO bisimilarity/indistinguishability ≡ is both
      decidable and first order definable, ie there is a FO formula
      A(.,.) such that
 
            x ≡ y <-> A(x,y) holds for any x,y in the model M

      We use it to quotient the model M and get a discrete model 
      (based on the finite type pos n) where identity coincides
      with FO bisimilarity.

      The idea of the construction is the following. We
      start from a finitary signature Σ to simplify the
      explanation but the devel below works in a sub-signature 
      of Σ where the list ls bounds usable terms symbols and 
      the list lr usable bound relations symbols.

      So given a finitary Σ and a finite and Boolean model M
      for Σ, we define the operator 

                 F : (M² -> Prop) -> (M² -> Prop) 

      transforming a binary relation R : M² -> Prop into F(R).

         x F(R) y iff      t(x)  R  t(y) for any t(.) = s<v(./p)>
                       and f(x) <-> f(y) for any f(.) = r<v(./p)>

      Then F(.) is monotonic, ω-continuous, and satisfies
      I ⊆ F(I), (F(R))⁻ ⊆ F(R⁻) and F(R) o F(R) ⊆ F (R o R)
      hence Kleene's greatest fixpoint gfp(F) exists, is
      obtained after ω-steps and is an equivalence relation.

      Moreover, F preserves decidability and FO-definability.
      Now we show that gfp(F) ~ F^n(TT) for a finite n
      which implies that gfp(F) is decidable and FO-definable.
      Here TT := fun _ _ => True is the full binary relation
      over M.

      The sequence n => F^n(TT) is a sequence of decidable
      (hence also weakly decidable) relations. If 
      F^a(TT) ⊆ F^b(TT) for a < b then we have F^a(TT) ~ F^i(TT)
      for any i => a and thus for any i >= a F^i(TT) ~ gfp F.

      The sequence n => F^n(TT) belongs to the weak power list 
      of binary relations over M (upto equivalence) which contains
      all weakly decidable binary relations over M. By the PHP,
      for n greater that the length of this list (which is
      2^(m*m) where m is the cardinal of M), we must have
      F^a(TT) ~ F^b(TT) for a <> b, hence we deduce
      F^n(TT) ~ gfp F.

      Hence, gfp F is decidable and FO-definable as well.
  
  *)  
 
  Variables (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ)).

  (** fo_bisimilar means no FO formula can distinguish x from y. Beware that
      two free variables might be needed, see the remarks and counter-example 
      below *)

  Definition fo_bisimilar X M x y := 
         forall A φ, incl (fol_syms A) ls
                  -> incl (fol_rels A) lr
                  -> @fol_sem Σ X M x·φ A <-> fol_sem M y·φ A.

  (** Let us assume a finite and Boolean model m *)

  Variables (X : Type) 
            (fin : finite_t X) 
            (M : fo_model Σ X) 
            (dec : fo_model_dec M).

  Implicit Type (R T : X -> X -> Prop).

  (** Construction of the greatest fixpoint of the following operator fom_op.
      Any prefixpoint R ⊆ fom_op R is a simulation for the model *)

  Let fom_op1 R x y := forall s, In s ls 
                    -> forall (v : vec _ (ar_syms Σ s)) p, 
                              R (fom_syms M s (v[x/p])) (fom_syms M s (v[y/p])).

  Let fom_op2 x y :=   forall s, In s lr 
                    -> forall (v : vec _ (ar_rels Σ s)) p, 
                              fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).

  Let fom_op R x y := fom_op1 R x y /\ fom_op2 x y.
  
  (** First we show properties of fom_op 

      a) Monotonicity
      b) preserves Reflexivity, Symmetry and Transitivity
      c) ω-continuous
      d) preserves decidability
      e) preserves FO definability

  *)

  Hint Resolve finite_t_pos finite_t_vec.

  (** Monotonicity *)
 
  Let fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof. unfold fom_op, fom_op1, fom_op2; intros ? ? ? []; split; intros; auto. Qed.

  (** Reflexivity, symmetry & transitivity *) 

  Let fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. unfold fom_op, fom_op1, fom_op2; intros []; split; auto; tauto. Qed.

  Let fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof. unfold fom_op, fom_op1, fom_op2; intros []; split; intros; auto; symmetry; auto. Qed.

  Let fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    unfold fom_op, fom_op1, fom_op2.
    intros (y & H1 & H2); split; intros s Hs v p.
    + exists (fom_syms M s (v[y/p])); split; [ apply H1 | apply H2 ]; auto.
    + transitivity (fom_rels M s (v[y/p])); [ apply H1 | apply H2 ]; auto.
  Qed.

  (* ω-continuity *)

  Let fom_op_continuous R : gfp_continuous fom_op.
  Proof.
    intros f Hf x y H; split; intros s Hs v p.
    + intros n.
      generalize (H n); intros (H1 & H2).
      apply H1; auto.
    + apply (H 0); auto.
  Qed.

  (* Decidability, a bit more complicated but we have all the tools to do it
     in an efficient way *)

  Let fom_op1_dec R : (forall x y, { R x y } + { ~ R x y })
                   -> (forall x y, { fom_op1 R x y } + { ~ fom_op1 R x y }).
  Proof.
    unfold fom_op1.
    intros HR x y.
    apply forall_list_sem_dec; intros.
    do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
  Qed.

  Let fom_op2_dec : (forall x y, { fom_op2 x y } + { ~ fom_op2 x y }).
  Proof.
    unfold fom_op2.
    intros x y.
    apply forall_list_sem_dec; intros.
    do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
    apply (fol_bin_sem_dec fol_conj); 
      apply (fol_bin_sem_dec fol_imp); auto.
  Qed.

  Let fom_op_dec R : (forall x y, { R x y } + { ~ R x y })
                  -> (forall x y, { fom_op R x y } + { ~ fom_op R x y }).
  Proof. intros; apply (fol_bin_sem_dec fol_conj); auto. Qed.

  (* FO definability, also more complicated but we have all the
     needed closure properties *)

  Tactic Notation "solve" "with" "proj" constr(t) :=
    apply fot_def_equiv with (f := fun φ => φ t); fol def; intros; rew vec.

  Let fol_def_fom_op1 R : fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
                       -> fol_definable ls lr M (fun ψ => fom_op1 R (ψ 0) (ψ 1)).
  Proof.
    intros H.
    apply fol_def_list_fa; intros s Hs.
    apply fol_def_vec_fa.
    apply fol_def_finite_fa; auto; intro p.
    apply fol_def_subst2; auto.
    * apply fot_def_comp; auto; intro q.
      destruct (pos_eq_dec p q); subst.
      - solve with proj (ar_syms Σ s).
      - solve with proj (pos2nat q).
    * apply fot_def_comp; auto; intro q.
      destruct (pos_eq_dec p q); subst.
      - solve with proj (ar_syms Σ s+1).
      - solve with proj (pos2nat q).
  Qed.

  Let fol_def_fom_op2 : fol_definable ls lr M (fun ψ => fom_op2 (ψ 0) (ψ 1)).
  Proof.
    apply fol_def_list_fa; intros r Hr.
    apply fol_def_vec_fa.
    apply fol_def_finite_fa; auto; intro p.
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

  Let fol_def_fom_op R : fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
                      -> fol_definable ls lr M (fun ψ => fom_op R (ψ 0) (ψ 1)).
  Proof. intro; apply fol_def_conj; auto. Qed.

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

  Fact fom_eq_fix x y : fom_op fom_eq x y <-> x ≡ y.
  Proof. apply gfp_fix; auto. Qed.

  Fact fom_eq_incl R : (forall x y, R x y -> fom_op R x y)
                    -> (forall x y, R x y -> x ≡ y).
  Proof. apply gfp_greatest; auto. Qed.

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

  Section fol_characterization.

    (** We show that the greatest bisimulation is equivalent to FOL undistinguishability. 
        This result is purely for the sake of completeness of the description of fom_eq,
        it is not used in the reduction below 

        It states that x and y are bisimilar iff there is no interpretation of a 
        FO formula that can distinguish x from y *)

    Hint Resolve fom_eq_syms_full fom_eq_rels_full.

    Let f : fo_simulation ls lr M M.
    Proof. exists fom_eq; auto; intros a; exists a; auto. Defined.

    Let fom_eq_fol_charac1 A phi psi : 
            (forall n, In n (fol_vars A) -> phi n ≡ psi n)
         -> incl (fol_syms A) ls
         -> incl (fol_rels A) lr
         -> fol_sem M phi A <-> fol_sem M psi A.
    Proof. intros; apply fo_model_simulation with (R := f); auto. Qed.

    (** By fom_eq_form_sem above, we know there is a FO formula
        A(.,.) in two free variables such that x ≡ y <-> A(x,y).

        One obvious follow up question is can we show

           x ≡ y <-> A(x) <-> A(y) for any A(.) with one free variable

        Another obvious follow up question is, for a given x in the
        model, can one characterize the class of { y | x ≡ y } with
        a formula Ax(.) with one free variable.

        Both questions have a negative answer proved in the counter
        example to be found below. There is a model of Σ = {ø,{=²}}
        with two distinct values where =² is interpreted by identity
        and such that A(x) <-> A(y) for any formula with at most one
        free variable. See theorem FO_does_not_characterize_classes.

      *)

    Local Fact fom_eq_fo_bisimilar x y : x ≡ y -> fo_bisimilar M x y.
    Proof.
      intros H A phi.
      apply fom_eq_fol_charac1.
      intros [ | n ] _; simpl; auto.
    Qed.

    Local Fact fo_bisimilar_fom_eq x y : fo_bisimilar M x y -> x ≡ y.
    Proof.
      revert x y; apply gfp_greatest; auto.
      intros x y H; split.
      * intros s Hs v p A phi H1 H2.
        destruct (fot_vec_env Σ p) as (w & Hw1 & Hw2).
        set (B := fol_subst (fun n => 
               match n with
                 | 0   => in_fot s w 
                 | S n => £ (S n + ar_syms Σ s)
               end) A).
        assert (HB : forall z, fol_sem M (z·(env_vlift phi v)) B 
                           <-> fol_sem M (fom_syms M s (v[z/p]))·phi A).
        { intros z; unfold B; rewrite fol_sem_subst; apply fol_sem_ext.
          intros [ | n] _; rew fot; simpl; f_equal.
          * apply vec_pos_ext; intros q; rewrite vec_pos_map; apply Hw1.
          * rewrite env_vlift_fix1; auto. }
        rewrite <- !HB; apply H.
        - red; apply Forall_forall, fol_syms_subst.
          intros [ | n ]; rew fot.
          + intros _; apply Forall_forall.
            intros s' [ <- | Hs' ]; auto; apply H1; revert Hs'.
            rewrite in_flat_map; intros (z & H3 & H4).
            apply vec_list_inv in H3; destruct H3 as (q & ->).
            rewrite Hw2 in H4; destruct H4.
          + constructor.
          + apply Forall_forall, H1.
        - unfold B; rewrite fol_rels_subst; auto.
      * intros r Hr v p; red in H.
        destruct (fot_vec_env Σ p) as (w & Hw1 & Hw2).
        set (B := fol_atom r w).
        assert (HB : forall z, fol_sem M (z·(env_vlift (fun _ => x) v)) B 
                           <-> fom_rels M r (v[z/p])).
        { intros z; unfold B; simpl; apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros q; rewrite vec_pos_map; apply Hw1. }
        rewrite <- !HB; apply H.
        - unfold B; simpl; intros z; rewrite in_flat_map.
          intros (t & H3 & H4).
          apply vec_list_inv in H3.
          destruct H3 as (q & ->).
          rewrite Hw2 in H4; destruct H4.
        - unfold B; simpl; intros ? [ <- | [] ]; auto.
    Qed.

    Theorem fom_eq_fol_characterization x y : 
            x ≡ y <-> fo_bisimilar M x y.
     Proof.
      split.
      + apply fom_eq_fo_bisimilar.
      + apply fo_bisimilar_fom_eq.
    Qed.

  End fol_characterization.

  (** And because the signature is finite (ie the symbols and relations) 
                  the model M is finite and composed of decidable relations 

      We do have a decidable equivalence here *) 

  Fact fom_eq_dec : forall x y, { x ≡ y } + { ~ x ≡ y }.
  Proof. apply gfp_decidable; auto. Qed.

  Definition fo_congruence_upto R := 
                 ( (equivalence _ R)
                 * (forall s v w, In s ls -> (forall p, R (v#>p) (w#>p)) -> R (fom_syms M s v) (fom_syms M s w))
                 * (forall r v w, In r lr -> (forall p, R (v#>p) (w#>p)) -> fom_rels M r v <-> fom_rels M r w) )%type.

  Theorem fo_bisimilar_dec_congr : fo_congruence_upto (@fo_bisimilar X M)
                                 * (forall x y, decidable (fo_bisimilar M x y)).
  Proof.
    split; [ split; [ split | ] | ].
    + split; red; [ intros ? | intros ? ? ? | intros ? ?]; rewrite <- !fom_eq_fol_characterization; auto.
      apply fom_eq_trans.
    + intros ? ? ? ? ?; apply fom_eq_fol_characterization, fom_eq_syms_full; auto.
      intro; apply fom_eq_fol_characterization; auto.
    + intros ? ? ? ? ?; apply fom_eq_rels_full; auto.
      intro; apply fom_eq_fol_characterization; auto.
    + intros x y.
      destruct (fom_eq_dec x y); [ left | right ]; rewrite <- fom_eq_fol_characterization; auto.
  Qed.

  (** But we have a much stronger statement: fom_eq is first order definable 
      which follows from the fact that X/M is finite *)

  Theorem fom_eq_finite : { n | forall x y, x ≡ y <-> iter fom_op (fun _ _ => True) n x y }.
  Proof. apply gfp_finite_t; auto. Qed.

  Theorem fom_eq_fol_def : fol_definable ls lr M (fun φ => φ 0 ≡ φ 1).
  Proof.
    destruct fom_eq_finite as (n & Hn).
    apply fol_def_equiv with (R := fun φ => iter fom_op (fun _ _ : X => True) n (φ 0) (φ 1)).
    + intro; rewrite <- Hn; tauto.
    + clear Hn; induction n as [ | n IHn ].
      * simpl; fol def.
      * rewrite iter_S; auto.
  Qed.

  Section fom_eq_form.

    (** We build a single FO formula with two variables A[.,.] 
        such that x ≡ y <-> A(x,y)  *)

    Let A := proj1_sig fom_eq_fol_def.

    (* Let use remove unused variables by mapping them to £0 *) 
    
    Definition fom_eq_form := fol_subst (fun n => match n with 0 => £1 | _ => £0 end) A.

    Fact fom_eq_form_sem φ x y : fol_sem M y·x·φ fom_eq_form <-> x ≡ y.
    Proof.
      unfold fom_eq_form; rewrite fol_sem_subst.
      apply (proj2_sig fom_eq_fol_def).
    Qed.

    Fact fom_eq_form_vars : incl (fol_vars fom_eq_form) (0::1::nil).
    Proof.
      unfold fom_eq_form; rewrite fol_vars_subst.
      intros n; rewrite in_flat_map; intros (? & _ & H).
      revert x H; intros [ | [] ]; simpl; tauto.
    Qed.

    Fact fom_eq_form_syms : incl (fol_syms fom_eq_form) ls.
    Proof.
      unfold fom_eq_form; red.
      apply Forall_forall, fol_syms_subst.
      + intros [ | []]; rew fot; auto.
      + apply Forall_forall, (proj2_sig fom_eq_fol_def).
    Qed.

    Fact fom_eq_form_rels : incl (fol_rels fom_eq_form) lr.
    Proof.
      unfold fom_eq_form; rewrite fol_rels_subst.
      apply (proj2_sig fom_eq_fol_def).
    Qed.

  End fom_eq_form.

  Hint Resolve fom_eq_form_vars fom_eq_form_syms fom_eq_form_rels fom_eq_dec.

  (** And now we can build a discrete model with this decidable 
      equivalence. There is a fo_projection from M to Md where
      Md is a Boolean model based on the ground type pos n.

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

    Let f : fo_projection ls lr M Md.
    Proof. exists cls repr; auto. Defined.

    Let H3 A phi : incl (fol_syms A) ls 
                -> incl (fol_rels A) lr
                -> fol_sem M phi A 
               <-> fol_sem Md (fun n => cls (phi n)) A.
    Proof. intros; apply fo_model_projection with (p := f); auto. Qed.

    Let H4 p q : fo_bisimilar Md p q <-> p = q.
    Proof.
      split.
      + intros H.
        rewrite <- (E1 q), <- (E1 p).
        apply E2, fom_eq_fol_characterization.
        intros A phi Hs Hr.
        specialize (H A (fun p => cls (phi p)) Hs Hr).
        revert H; apply fol_equiv_impl.
        all: rewrite H3; auto; apply fol_sem_ext; intros []; now simpl.
      + intros []; red; tauto.
    Qed.

    (** Every finite & decidable model can be projected to pos n
        with decidable relations and such that identity is exactly
        FO undistinguishability *)

    Theorem fo_fin_model_discretize : 
        { n : nat & 
        { Md : fo_model Σ (pos n) &
        { _ : fo_model_dec Md & 
        { _ : fo_projection ls lr M Md & 
          (forall p q, fo_bisimilar Md p q <-> p = q) } } } }.
    Proof.
      exists n, Md.
      exists; eauto. 
      intros x y; simpl; apply dec.
    Qed.

  End build_the_model.

End discrete_quotient.

Section counter_model_to_class_FO_definability.

  (** We show that there is a model over Σ = Σrel 2 = {ø,{=²}}
      where ≡ is identity but x ≡ _ is not definable by a
      FO formula with a single free variable 

      There are two non equivalent values that cannot be
      distinguished when using a single variable

      Even though ≡ is FO definable by a formula with two
      free variables, equivalences classes of ≡ are not 
      FO definable *)

  Let Σ := Σrel 2.

  Let M : fo_model Σ bool.
  Proof.
    exists.
    + intros [].
    + intros []; simpl.
      exact (rel2_on_vec eq).
  Defined.

  Let M_dec : fo_model_dec M.
  Proof. intros [] ?; apply bool_dec. Qed.

  (* A projection of M onto itself which swaps true <-> false *)

  Let f : @fo_projection Σ nil (tt::nil) _ M _ M.
  Proof.
    exists negb negb.
    + intros []; auto.
    + intros [].
    + intros [] v _; simpl.
      vec split v with x; vec split v with y; vec nil v; simpl.
      revert x y; now intros [] [].
  Defined.

  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).

  Let homeomorphism (A : fol_form Σ) phi : 
        ⟪A⟫ phi <-> ⟪A⟫ (fun x=> negb (phi x)).
  Proof.
    apply fo_model_projection with (p := f); auto.
    all: intros []; simpl; auto.
  Qed.

  Infix "≡" := (fom_eq (Σ := Σ) nil (tt::nil) M) (at level 70, no associativity).

  Hint Resolve finite_t_bool.

  Let true_is_not_false : ~ true ≡ false.
  Proof.
    intros H.
    apply fom_eq_fol_characterization in H; auto.
    specialize (H (@fol_atom Σ tt (£0##£1##ø)) (fun n => match n with 0 => true | _ => false end)).
    revert H; unfold M; simpl; rew fot; simpl.
    intros [H _]; cbv; auto.
    specialize (H eq_refl); discriminate.
  Qed.

  Let no_disctinct A phi : (forall n, In n (fol_vars A) -> n = 0)
                        -> ⟪A⟫ true·phi <-> ⟪A⟫ false·phi.
  Proof.
    intros H.
    set (psi n := negb (phi n)).
    rewrite homeomorphism with (phi := false·phi) at 1.
    apply fol_sem_ext.
    intros n Hn; apply H in Hn; subst; auto.
  Qed.

  (** There is a model over Σ2 with two values such that no
      FO formula with one free variable can distinguish those 
      two values, but there is a FO formula with 2 free variables
      that distinguishes them *)

  Theorem FO_does_not_characterize_classes :
     exists (M : fo_model Σ bool) (_ : fo_model_dec M) (x y : bool), 
            ~ fom_eq (Σ := Σ) nil (tt::nil) M x y
         /\ forall A φ, (forall n, In n (fol_vars A) -> n = 0) 
                     -> fol_sem M x·φ A <-> fol_sem M y·φ A.
  Proof. exists M, M_dec, true, false; auto. Qed.

End counter_model_to_class_FO_definability.
