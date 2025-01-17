(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Nat Lia Relations Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations decidable gfp fol_ops fo_sig fo_terms fo_logic fo_definable fo_sat.

Import fol_notations.

Set Implicit Arguments.

Local Notation " e '#>' x " := (vec_pos e x).
Local Notation " e [ v / x ] " := (vec_change e x v).

(* ∈ and ⊆ are already used for object level syntax at too low level 59 *)

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 

Local Notation "M , r ⊨ A" := (fol_sem M r A) (at level 70, format "M , r  ⊨  A").

Local Notation "f ∘ g" := (fun x => f (g x)) (at level 55, left associativity).

Section discrete_quotient.

  (* We show the FO bisimilarity/indistinguishability ≡ is both
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

  (* fo_bisimilar means no FO formula can distinguish x from y. Beware that
      two free variables might be needed, see the remarks and counter-example 
      below *)

  Definition fo_bisimilar X (M : fo_model Σ X) x y := 
         forall φ, fol_syms φ ⊑ ls -> fol_rels φ ⊑ lr
                -> forall ρ, M,x·ρ ⊨ φ <-> M,y·ρ ⊨ φ.

  (* Let us assume a finite and Boolean model m *)

  Variables (X : Type) 
            (fin : finite_t X) 
            (M : fo_model Σ X) 
            (dec : fo_model_dec M).

  Infix "≐" := (fo_bisimilar M) (at level 70).

  Fact fo_bisimilar_refl x : x ≐ x.
  Proof. intro; tauto. Qed.

  Fact fo_bisimilar_sym x y : x ≐ y -> y ≐ x.
  Proof. unfold fo_bisimilar; intros H ? ? ? ?; rewrite H; auto; tauto. Qed.

  Fact fo_bisimilar_trans x y z : x ≐ y -> y ≐ z -> x ≐ z.
  Proof. unfold fo_bisimilar; intros H ? ? ? ? ?; rewrite H; auto. Qed.

  Implicit Type (R T : X -> X -> Prop).

  (* Construction of the greatest fixpoint of the following operator fom_op.
      Any prefixpoint R ⊆ fom_op R is a simulation for the model *)

  Local Definition fom_op1 R x y := 
          forall s, s ∊ ls 
       -> forall (v : vec _ (ar_syms Σ s)) i, 
                 R (fom_syms M s (v[x/i])) (fom_syms M s (v[y/i])).

  Local Definition fom_op2 x y := 
          forall s, s ∊ lr 
       -> forall (v : vec _ (ar_rels Σ s)) i, 
                 fom_rels M s (v[x/i]) <-> fom_rels M s (v[y/i]).

  Local Definition fom_op R x y := fom_op1 R x y /\ fom_op2 x y.
  
  (* First we show properties of fom_op 

      a) Monotonicity
      b) preserves Reflexivity, Symmetry and Transitivity
      c) ω-continuous
      d) preserves decidability
      e) preserves FO definability

  *)

  Hint Resolve finite_t_pos finite_t_vec : core.

  (* Monotonicity *)
 
  Local Fact fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof. unfold fom_op, fom_op1, fom_op2; intros ? ? ? []; split; intros; auto. Qed.

  (* Reflexivity, symmetry & transitivity *) 

  Local Fact fom_op_id x y : x = y -> fom_op (@eq _) x y.
  Proof. unfold fom_op, fom_op1, fom_op2; intros []; split; auto; tauto. Qed.

  Local Fact fom_op_sym R x y : fom_op R y x -> fom_op (fun x y => R y x) x y.
  Proof. unfold fom_op, fom_op1, fom_op2; intros []; split; intros; auto; symmetry; auto. Qed.

  Local Fact fom_op_trans R x z : (exists y, fom_op R x y /\ fom_op R y z)
                        -> fom_op (fun x z => exists y, R x y /\ R y z) x z.
  Proof.
    unfold fom_op, fom_op1, fom_op2.
    intros (y & H1 & H2); split; intros s Hs v p.
    + exists (fom_syms M s (v[y/p])); split; [ apply H1 | apply H2 ]; auto.
    + transitivity (fom_rels M s (v[y/p])); [ apply H1 | apply H2 ]; auto.
  Qed.

  (* ω-continuity *)

  Local Fact fom_op_continuous : gfp_continuous fom_op.
  Proof.
    intros f Hf x y H; split; intros s Hs v p.
    + intros n.
      generalize (H n); intros (H1 & H2).
      apply H1; auto.
    + apply (H 0); auto.
  Qed.

  Section fom_op_dec.

    (* fom_op is closed under strong decidability, 
       a bit more complicated but we have all 
       the tools to do it the easy way *)

    Let fom_op1_dec R : 
          (forall x y, { R x y } + { ~ R x y })
       -> (forall x y, { fom_op1 R x y } + { ~ fom_op1 R x y }).
    Proof.
      unfold fom_op1.
      intros HR x y.
      apply forall_list_sem_dec; intros.
      do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
    Qed.

    Let fom_op2_dec x y : { fom_op2 x y } + { ~ fom_op2 x y }.
    Proof.
      unfold fom_op2.
      apply forall_list_sem_dec; intros.
      do 2 (apply (fol_quant_sem_dec fol_fa); auto; intros).
      apply (fol_bin_sem_dec fol_conj); 
        apply (fol_bin_sem_dec fol_imp); auto.
    Qed.

    Local Fact fom_op_dec R : 
            (forall x y, { R x y } + { ~ R x y })
         -> (forall x y, { fom_op R x y } + { ~ fom_op R x y }).
    Proof using fin dec. intros; apply (fol_bin_sem_dec fol_conj); auto. Qed.

  End fom_op_dec.

  Section fo_definability.

    (* fom_op is closed under FO definability, 
       more complicated but we have all the
       needed closure properties *)

    Tactic Notation "solve" "with" "proj" constr(t) :=
      apply fot_def_equiv with (f := fun φ => φ t); fol def; intros; rew vec.

    Let fol_def_fom_op1 R : 
           fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
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

    Let fol_def_fom_op2 : 
           fol_definable ls lr M (fun ψ => fom_op2 (ψ 0) (ψ 1)).
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

    Local Fact fol_def_fom_op R : 
            fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
         -> fol_definable ls lr M (fun ψ => fom_op R (ψ 0) (ψ 1)).
    Proof. intro; apply fol_def_conj; auto. Qed.

    Hint Resolve fol_def_fom_op : core. 

    Local Fact fol_def_iter_fom_op R n :
            fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
         -> fol_definable ls lr M (fun ψ => iter fom_op R n (ψ 0) (ψ 1)).
    Proof. revert R; induction n; simpl; auto. Qed.

  End fo_definability.

  (* Now we build the greatest fixpoint fom_eq and show its properties

      a) it is an equivalence relation
      b) it is a congruence wrt to the model functions and relations
      c) it is decidable and FO definable

      the reason is that it is obtained after finitely many iterations of fom_op

    *)

  (* We build the greatest bisimulation which is an equivalence 
      and a (pre-)fixpoint for the above operator *) 

  Definition fom_eq := gfp fom_op.

  Infix "≡" := fom_eq (at level 70, no associativity).

  Hint Resolve fom_op_mono fom_op_id fom_op_sym fom_op_trans 
               fom_op_continuous fom_op_dec : core.

  Local Fact fom_eq_equiv : equiv _ fom_eq.
  Proof. apply gfp_equiv; eauto. Qed.

  Local Fact fom_eq_refl x : x ≡ x.                         Proof. apply (proj1 fom_eq_equiv). Qed.
  Local Fact fom_eq_sym x y : x ≡ y -> y ≡ x.               Proof. apply fom_eq_equiv. Qed.
  Local Fact fom_eq_trans x y z : x ≡ y -> y ≡ z -> x ≡ z.  Proof. apply fom_eq_equiv. Qed.

  Local Fact fom_eq_fix x y : fom_op fom_eq x y <-> x ≡ y.
  Proof. apply gfp_fix; eauto. Qed.

  Local Fact fom_eq_incl R : 
           (forall x y, R x y -> fom_op R x y)
        -> (forall x y, R x y -> x ≡ y).
  Proof. apply gfp_greatest; eauto. Qed.

  (* It is a congruence wrt to the model *)

  Local Fact fom_eq_syms x y s v p : 
          s ∊ ls -> x ≡ y -> fom_syms M s (v[x/p]) ≡ fom_syms M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed. 
    
  Local Fact fom_eq_rels x y s v p : 
          s ∊ lr -> x ≡ y -> fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).
  Proof. intros; apply fom_eq_fix; auto. Qed.

  Hint Resolve fom_eq_refl fom_eq_sym fom_eq_trans fom_eq_syms fom_eq_rels : core.

  Local Theorem fom_eq_syms_full s v w : 
          s ∊ ls -> (forall p, v#>p ≡ w#>p) -> fom_syms M s v ≡ fom_syms M s w.
  Proof. intro; apply map_vec_pos_equiv; eauto. Qed.

  Local Theorem fom_eq_rels_full s v w : 
          s ∊ lr -> (forall p, v#>p ≡ w#>p) -> fom_rels M s v <-> fom_rels M s w.
  Proof. intro; apply map_vec_pos_equiv; eauto; tauto. Qed.

  (* And because the signature is finite (ie the symbols and relations) 
                  the model M is finite and composed of decidable relations 

      We do have a decidable equivalence here *) 

  Local Fact fom_eq_dec x y : { x ≡ y } + { ~ x ≡ y }.
  Proof using fin dec. apply gfp_decidable; eauto. Qed.

  Section fol_characterization.

    (* We show that the greatest bisimulation is equivalent to FOL undistinguishability. 
        This result is purely for the sake of completeness of the description of fom_eq,
        it is not used in the reduction below 

        It states that x and y are bisimilar iff there is no interpretation of a 
        FO formula that can distinguish x from y *)

    Hint Resolve fom_eq_syms_full fom_eq_rels_full : core.

    Let f : fo_simulation ls lr M M.
    Proof. exists fom_eq; abstract eauto. Defined.

    Let fom_eq_fol_charac1 φ : 
            fol_syms φ ⊑ ls
         -> fol_rels φ ⊑ lr
         -> forall ρ δ, (forall n, n ∊ fol_vars φ -> ρ n ≡ δ n) -> M,ρ ⊨ φ <-> M,δ ⊨ φ.
    Proof. intros; apply fo_model_simulation with (R := f); auto. Qed.

    (* By fom_eq_form_sem above, we know there is a FO formula
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

    Let fom_eq_fo_bisimilar x y : x ≡ y -> x ≐ y.
    Proof.
      intros ? ? ? ? ?; apply fom_eq_fol_charac1; auto.
      intros [] _; auto.
    Qed.

    Let fo_bisimilar_fom_eq x y : x ≐ y -> x ≡ y.
    Proof.
      revert x y; apply gfp_greatest; eauto.
      intros x y H; split.
      * intros s Hs v p A H1 H2 phi.
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

    Hint Resolve fom_eq_fo_bisimilar fo_bisimilar_fom_eq : core.

    Theorem fom_eq_fol_characterization x y : x ≡ y <-> x ≐ y.
    Proof. split; auto. Qed.

  End fol_characterization.

  (** R is an equivalence relation and a congruence for the interpretations
      of all the symbols in ls and lr *)

  Definition fo_congruence_upto R := 
      ( (equivalence _ R)
    * (forall s v w, s ∊ ls -> (forall p, R (v#>p) (w#>p)) -> R (fom_syms M s v) (fom_syms M s w))
    * (forall r v w, r ∊ lr -> (forall p, R (v#>p) (w#>p)) -> fom_rels M r v <-> fom_rels M r w) )%type.

  Theorem fo_bisimilar_dec_congr : 
            fo_congruence_upto (fun x y => x ≐ y)
         * (forall x y, decidable (x ≐ y)).
  Proof using fin dec.
    lsplit 3.
    + split; red; [ intros ? | intros ? ? ? | intros ? ?]; 
        rewrite <- !fom_eq_fol_characterization; eauto.
    + intros ? ? ? ? ?; apply fom_eq_fol_characterization, fom_eq_syms_full; auto.
      intro; apply fom_eq_fol_characterization; auto.
    + intros ? ? ? ? ?; apply fom_eq_rels_full; auto.
      intro; apply fom_eq_fol_characterization; auto.
    + intros x y.
      destruct (fom_eq_dec x y); [ left | right ]; 
        rewrite <- fom_eq_fol_characterization; auto.
  Qed.

  Section build_the_discrete_model.

    (* And now we can build a discrete model with this decidable 
      equivalence. There is a fo_projection from M to Md where
      Md is a Boolean model based on the ground type pos n.

     *)

    Let l := proj1_sig fin.
    Let Hl : forall x, x ∊ l := proj2_sig fin.

    Hint Resolve fom_eq_dec : core.

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

    Let H1 s v : s ∊ ls -> cls (fom_syms M s v) = fom_syms Md s (vec_map cls v).
    Proof.
      intros Hs; simpl.
      apply E2.
      apply fom_eq_syms_full; auto.
      intros p; rewrite vec_map_map, vec_pos_map.
      apply E2; rewrite E1; auto.
    Qed.

    Let H2 r v : r ∊ lr -> fom_rels M r v <-> fom_rels Md r (vec_map cls v).
    Proof.
      intros Hs; simpl.
      apply fom_eq_rels_full; auto.
      intros p; rewrite vec_map_map, vec_pos_map.
      apply E2; rewrite E1; auto.
    Qed.

    Let f : fo_projection ls lr M Md.
    Proof. exists cls repr; abstract auto. Defined.

    Let H3 φ ρ :   fol_syms φ ⊑ ls 
                -> fol_rels φ ⊑ lr
                -> M,ρ ⊨ φ <-> Md,cls∘ρ ⊨ φ.
    Proof. intros; apply fo_model_projection with (p := f); auto. Qed.

    Let H4 p q : fo_bisimilar Md p q <-> p = q.
    Proof.
      split.
      + intros H.
        rewrite <- (E1 q), <- (E1 p).
        apply E2, fom_eq_fol_characterization.
        intros A Hs Hr phi.
        specialize (H A Hs Hr (fun p => cls (phi p))).
        revert H; apply fol_equiv_impl.
        all: rewrite H3; auto; apply fol_sem_ext; intros []; now simpl.
      + intros []; red; tauto.
    Qed.

    (* Every finite & decidable model can be projected to pos n
        with decidable relations and such that identity is exactly
        FO undistinguishability *)

    Theorem fo_fin_model_discretize : 
        { n : nat & 
        { Md : fo_model Σ (pos n) &
        { _ : fo_model_dec Md & 
        { _ : fo_projection ls lr M Md & 
          (forall p q, fo_bisimilar Md p q <-> p = q) } } } }.
    Proof using E1.
      exists n, Md.
      exists; eauto.
      red; simpl; auto.
    Qed.

  End build_the_discrete_model.

  (** Additional results on FO definability *)

  Section FO_definability.

    (* Because the fixpoint is reached after finitely many iterations, it is FO definable *)

    Local Fact fom_eq_finite : { n | forall x y, x ≡ y <-> iter fom_op (fun _ _ => True) n x y }.
    Proof using fin dec. apply gfp_finite_t; eauto. Qed.

    Theorem fo_bisimilar_fol_def : fol_definable ls lr M (fun φ => φ 0 ≐ φ 1).
    Proof using fin dec.
      destruct fom_eq_finite as (n & Hn).
      apply fol_def_equiv with (R := fun φ => iter fom_op (fun _ _ : X => True) n (φ 0) (φ 1)).
      + intro; rewrite <- fom_eq_fol_characterization, <- Hn; tauto.
      + apply fol_def_iter_fom_op; fol def.
    Qed.

  End FO_definability.

  (** We have a much stronger statement than the decidability of ≐.
      In fact ≐ is first order definable and this follows from the 
      fact that X/M is finite *)

  Section fo_bisimilar_formula.

    (* We build a single FO formula with two variables 
        such that:
          a) ξ(.,.) only has two free variables, 0 and 1 
          b) ξ is built using only symbols in ls and lr
          c) ξ characterize bisimilarity upto ls/lr 

                  x ≐ y <-> x ≡ y <-> ξ(x,y) 
     *)

    Let A := proj1_sig fo_bisimilar_fol_def.

    (* Let use remove unused variables by mapping them to £0 *) 
    
    Definition fo_bisimilar_formula := fol_subst (fun n => match n with 0 => £1 | _ => £0 end) A.

    Notation ξ := fo_bisimilar_formula.

    Fact fo_bisimilar_formula_vars : fol_vars ξ ⊑ 0::1::nil.
    Proof.
      unfold fo_bisimilar_formula; rewrite fol_vars_subst.
      intros n; rewrite in_flat_map; intros (? & _ & H).
      revert x H; intros [ | [] ]; simpl; tauto.
    Qed.

    Fact fo_bisimilar_formula_syms : fol_syms ξ ⊑ ls.
    Proof.
      unfold fo_bisimilar_formula; red.
      apply Forall_forall, fol_syms_subst.
      + intros [ | []]; rew fot; auto.
      + apply Forall_forall, (proj2_sig fo_bisimilar_fol_def).
    Qed.

    Fact fo_bisimilar_formula_rels : fol_rels ξ ⊑ lr.
    Proof.
      unfold fo_bisimilar_formula; rewrite fol_rels_subst.
      apply (proj2_sig fo_bisimilar_fol_def).
    Qed.

    Fact fo_bisimilar_formula_sem φ x y : M,y·x·φ ⊨ ξ <-> x ≐ y.
    Proof.
      unfold fo_bisimilar_formula; rewrite fol_sem_subst.
      apply (proj2_sig fo_bisimilar_fol_def).
    Qed.

  End fo_bisimilar_formula.

End discrete_quotient.

Import ListNotations.

Section counter_model_to_class_FO_definability.

  (* Even though ≐ is FO definable, its equivalence classes are not *)

  (* We show that there is a model over Σ = Σrel 2 = {ø,{=²}}
      where bisimulation ≐ is identity but x ≐ _ is not definable 
      by a FO formula with a single free variable 

      There are two non-equivalent values that cannot be
      distinguished when using a single variable

      Even though ≐ is FO definable by a formula with two
      free variables, equivalences classes of ≐ are not 
      FO definable *)

  Let Σ := Σrel 2.

  Let M : fo_model Σ bool.
  Proof.
    exists; simpl.
    + intros [].
    + exact (fun _ => rel2_on_vec eq).
  Defined.

  Let M_dec : fo_model_dec M.
  Proof. intros [] ?; apply bool_dec. Qed.

  Notation α := true.
  Notation β := false.

  (* A projection of M onto itself which swaps α/β *)

  Let f : @fo_projection Σ [] [tt] _ M _ M.
  Proof.
    exists negb negb; simpl.
    + abstract now intros [].
    + abstract intros [].
    + abstract (intros [] v _;
      vec split v with x; vec split v with y; vec nil v; simpl;
      revert x y; now intros [] []).
  Defined.

  Let homeomorphism φ ρ : M,ρ ⊨ φ <-> M,negb∘ρ ⊨ φ.
  Proof.
    apply fo_model_projection with (p := f); auto.
    all: intros []; simpl; auto.
  Qed.

  Infix "≐" := (fo_bisimilar (Σ := Σ) nil [tt] M) (at level 70, no associativity).

  Hint Resolve finite_t_bool : core.

  Let bisim_is_identity x y : x ≐ y <-> x = y.
  Proof.
    split.
    + intros H.
      now apply (H (@fol_atom Σ tt (£0##£1##ø)))
        with (ρ := fun n => match n with 0 => y | _ => x end).
    + intros ->; apply fo_bisimilar_refl.
  Qed.

 (* α/true and β/false are not bisimilar *) 

  Let true_is_not_false : ~ α ≐ β.
  Proof. now rewrite bisim_is_identity. Qed.

  (* No formula using only variable 0 can distinguish α from β *)

  Let no_distinct φ ρ x y : fol_vars φ ⊑ [0] -> M,x·ρ ⊨ φ <-> M,y·ρ ⊨ φ.
  Proof.
    revert x y; intros [] [] H; try tauto; [ | symmetry ];
      rewrite homeomorphism with (ρ := β·ρ) at 1;
      apply fol_sem_ext; intros n Hn; now apply H in Hn as [ [] | [] ].
  Qed.

  (** There is a (discrete, finite, decidable) model M over Σ2 with 
      two values α and β such that:
       1) FO bisimilarity (up to all symbols) is equivalent to identity
       2) no FO formula with one free variable can distinguish the elements
          of M, in particular distinguish α from β;
       3) there is a FO ξ(.,.) with 2 free variables that distinguishes
          α from β, i.e. ξ(α,α) and not ξ(β,α) (hence particular, α <> β).
   *)

  Theorem FO_does_not_characterize_classes :
     exists (M : fo_model Σ bool) (_ : fo_model_dec M) (a b : bool), 
              (forall x y, fo_bisimilar (Σ := Σ) nil [tt] M x y <-> x = y)
           /\ (forall x y φ ρ, fol_vars φ ⊑ [0] -> M,x·ρ ⊨ φ <-> M,y·ρ ⊨ φ)
           /\ exists ξ, fol_vars ξ ⊑ [0;1] /\ forall ρ, M,a·a·ρ ⊨ ξ /\ ~ M,b·a·ρ ⊨ ξ.
  Proof. 
    exists M, M_dec, true, false; msplit 2; auto. 
    exists (fo_bisimilar_formula (Σ := Σ) nil [tt] finite_t_bool M_dec); split.
    + apply fo_bisimilar_formula_vars.
    + intro; rewrite !fo_bisimilar_formula_sem; split; auto; intro; tauto.
  Qed.

End counter_model_to_class_FO_definability.
