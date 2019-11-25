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

  Let fom_op1 R x y := forall s, In s ls -> forall (v : vec _ (ar_syms Σ s)) p, R (fom_syms M s (v[x/p])) (fom_syms M s (v[y/p])).
  Let fom_op2 x y := forall s, In s lr -> forall (v : vec _ (ar_rels Σ s)) p, fom_rels M s (v[x/p]) <-> fom_rels M s (v[y/p]).

  Let fom_op R x y := fom_op1 R x y /\ fom_op2 x y.
  
  (** First we show properties of fom_op 

      a) Monotonicity
      b) preserves Reflexivity, Symmetry and Transitivity
      c) preserves Decidability
      d) preserves FO definability
*)

  Hint Resolve finite_t_pos finite_t_vec.
 
  Let fom_op_mono R T : (forall x y, R x y -> T x y) -> (forall x y, fom_op R x y -> fom_op T x y).
  Proof. unfold fom_op, fom_op1, fom_op2; intros ? ? ? []; split; intros; auto. Qed. 

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

  Tactic Notation "solve" "with" "proj" constr(t) :=
    apply fot_def_equiv with (f := fun φ => φ t); fol def; intros; rew vec.

  Let fol_def_fom_op1 R : fol_definable ls lr M (fun ψ => R (ψ 0) (ψ 1))
                       -> fol_definable ls lr M (fun ψ => fom_op1 R (ψ 0) (ψ 1)).
  Proof.
    intros H.
    apply fol_def_list_fa; intros s Hs;
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

  (** This involves the w-continuity of fom_op *)

  Fact fom_eq_fix x y : fom_op fom_eq x y <-> x ≡ y.
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

    Let A := proj1_sig fom_eq_fol_def. 
    
    Definition fom_eq_form := fol_subst (fun n => match n with 0 => £1 | _ => £0 end) A.

    Fact fom_eq_form_sem φ x y : fol_sem M φ↑x↑y fom_eq_form <-> x ≡ y.
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

  (** First order indistinguishability upto formulae built with functions and constants in 
      ls and relations in ls *)

  Section fol_characterization.

    (** We show that the greatest bisimulation is equivalent to FOL undistinguishability ie 
        This result is purely for the sake of completeness of the description of fom_eq,
        it is not used in the reduction below 

        It state that x and y are bisimilar iff the is no interpretation of a FO formula 
        with one free variable that can distinguish x from y *)

    Hint Resolve fom_eq_syms_full fom_eq_rels_full.

    Let fos : fo_simulation ls lr M M.
    Proof. exists fom_eq; auto; intros a; exists a; auto. Defined.

    Let fom_eq_fol_charac1 A phi psi : 
            (forall n, In n (fol_vars A) -> phi n ≡ psi n)
         -> incl (fol_syms A) ls
         -> incl (fol_rels A) lr
         -> fol_sem M phi A <-> fol_sem M psi A.
    Proof.
      intros; apply  fo_model_simulation with (R := fos); auto.
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

       One idea is to show that formulas of arity n are finitary
       up to equivalence and then define

             C_x [.] = /\ { A[.] | A[x] is true } U { ~ A[.] | A[x] is false }

       One can then show C_x[y] is true iff forall A[.], A[x] <-> A[y] iff x ≡ y
       The problem is to show that n-ary formulas are finitary upto equivalence
       Maybe one does not need to consider arities above the size of the model ?

       THE ANSWER IS NO WE CANNOT, SEE THE COUNTER-MODEL BELOW

       Theorem FO_does_not_characterize_classes

      *)

    Theorem fom_eq_fol_characterization x y : 
            x ≡ y <-> fo_bisimilar M x y.
    Proof.
      split.
      + intros H A phi.
        apply fom_eq_fol_charac1.
        intros [ | n ] _; simpl; auto.
      + intros H.
        set (phi (_ : nat) := x).
        apply fom_eq_form_sem with (φ := phi), H,
              fom_eq_form_sem with (φ := phi); auto.
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

    Let f : fo_projection ls lr M Md.
    Proof. exists cls repr; auto. Defined.

    Let H3 A phi : incl (fol_syms A) ls 
                -> incl (fol_rels A) lr
                -> fol_sem M phi A 
               <-> fol_sem Md (fun n => cls (phi n)) A.
    Proof.
      intros Hs Hr.
      apply fo_model_projection with (p := f); auto.
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

    Theorem fo_fin_model_discretize : 
        { n : nat & 
        { Md : fo_model Σ (pos n) &
        { _ : fo_model_dec Md & 
        { _ : fo_projection ls lr M Md & 
          (forall p q, fo_bisimilar Md p q -> p = q) } } } }.
    Proof.
      exists n, Md.
      exists; eauto. 
      intros x y; simpl; apply dec.
    Qed.

  End build_the_model.

End discrete_quotient.

Check fo_fin_model_discretize.
Print Assumptions fo_fin_model_discretize.

Section counter_model_to_class_FO_definability.

  (** We show that there is a model over Σ = Σrel 2 = {ø,{=_2}}
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

  Let R : @fo_simulation Σ nil (tt::nil) _ M _ M.
  Proof.
    exists (fun a b => a <> b); auto.
    2,3: intros x; exists (negb x); now destruct x.
    intros [] v w _; simpl.
    vec split v with x1; vec split v with x2; vec nil v.
    vec split w with y1; vec split w with y2; vec nil w; intros H1.
    generalize (H1 pos0) (H1 pos1); clear H1; intros H1 H2; simpl in H1, H2.
    unfold M; simpl.
    red in H1, H2.
    revert x1 y1 x2 y2 H1 H2.
    intros [] [] [] []; tauto.
  Defined.

  Infix "⋈" := R (at level 70, no associativity). 
  Notation "⟪ A ⟫" := (fun φ => fol_sem M φ A).

  Let homeomorphism (A : fol_form Σ) phi psi : 
        (forall n, phi n ⋈ psi n) -> ⟪A⟫ phi <-> ⟪A⟫ psi.
  Proof.
    intros H.
    apply fo_model_simulation with (R := R); auto.
    all: intros []; simpl; auto.
  Qed.

  Check fom_eq.

  Infix "≡" := (fom_eq (Σ := Σ) nil (tt::nil) M) (at level 70, no associativity).

  Hint Resolve finite_t_bool.

  Let true_is_not_false : ~ true ≡ false.
  Proof.
    intros H.
    apply fom_eq_fol_characterization in H; auto.
    specialize (H (fol_atom Σ tt (£0##£1##ø)) (fun n => match n with 0 => true | _ => false end)).
    revert H; unfold M; simpl; rew fot; simpl.
    intros [H _]; cbv; auto.
    specialize (H eq_refl); discriminate.
  Qed.

  Let no_disctinct A phi : incl (fol_vars A) (0::nil)
                        -> ⟪A⟫ phi↑true <-> ⟪A⟫ phi↑false.
  Proof.
    intros H.
    assert (H0 : forall b, b ⋈ negb b) by (intros []; discriminate).
    assert (H1 : forall b, negb b ⋈ b) by (intros []; discriminate).
    set (psi n := negb (phi n)).
    assert (G1 : forall n, phi n ⋈ psi n) by (intro; apply H0).
    assert (G2 : forall n, psi n ⋈ phi n) by (intro; apply H1).
    clear H0 H1.
    rewrite homeomorphism with (psi := psi↑false) at 1.
    + apply fol_sem_ext.
      intros n Hn; apply H in Hn; revert Hn.
      intros [ <- | [] ]; auto.
    + intros [ | n ]; simpl; try discriminate; apply G1.
  Qed.

  Theorem FO_does_not_characterize_classes :
     exists (M : fo_model Σ bool) (_ : fo_model_dec M) (x y : bool), 
            ~ fom_eq (Σ := Σ) nil (tt::nil) M x y
         /\ forall A φ, incl (fol_vars A) (0::nil) 
                     -> fol_sem M φ↑x A <-> fol_sem M φ↑y A.
  Proof.
    exists M, M_dec, true, false; auto.
  Qed.

End counter_model_to_class_FO_definability.

Check FO_does_not_characterize_classes.

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
      as (n & Md & Mdec & f & E).
    set (psy n := f (phi n)).
    exists n, (@pos_eq_dec _), Md, (finite_t_pos _) , Mdec, psy.
    revert HA.
    apply fo_model_projection with (p := f); 
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
