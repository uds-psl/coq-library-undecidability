(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

From Undecidability.ILL
  Require Import ILL.

Set Implicit Arguments.

Section obvious_links_between_fragments.

  Notation "P ⇒ Q" := (forall Γ A, P Γ A -> Q Γ A) (at level 70).

  Fact S_ill_restr_restr_wc : S_ill_restr ⇒ S_ill_restr_wc.
  Proof.
    induction 1.
    all: try now constructor.
    now constructor 3 with (Γ := Γ).
  Qed.

  Fact S_ill_full_wc : S_ill ⇒ S_ill_wc.
  Proof.
    induction 1.
    all: try now constructor.
    now constructor 3 with (Γ := Γ).
  Qed.

  Fact S_ill_restr_full : S_ill_restr ⇒ S_ill.
  Proof.
    induction 1.
    all: try now constructor.
    now constructor 2 with (Γ := Γ).
  Qed.

  Fact S_ill_restr_full_wc : S_ill_restr_wc ⇒ S_ill_wc.
  Proof.
    induction 1.
    all: try now constructor.
    + now constructor 2 with A.
    + now constructor 3 with (Γ := Γ).
  Qed.

End obvious_links_between_fragments.

Local Notation "Γ '⊢r' A" := (S_ill_restr Γ A) (at level 70, no associativity).
Local Notation "Γ '⊢' A" := (S_ill_wc Γ A) (at level 70, no associativity).

Fact S_ill_restr_weak Γ Δ B : Δ ⊢r B -> ‼Γ++Δ ⊢r B.
Proof. intro; induction Γ; simpl; auto; apply in_ill1_weak; auto. Qed.

Fact S_ill_wc_weak Γ Δ B : Δ ⊢ B -> ‼Γ++Δ ⊢ B.
Proof. intro; induction Γ; simpl; auto; apply in_ill4_weak; auto. Qed.

Fact S_ill_restr_cntr Γ Δ B : ‼Γ++‼Γ++Δ ⊢r B -> ‼Γ++ Δ ⊢r B.
Proof.
  revert Γ Δ; intros Ga.
  induction Ga as [ | A Ga IH ]; simpl; auto; intros De.
  intros H.
  apply in_ill1_cntr.
  apply in_ill1_perm with (map ll_ban Ga ++ (!A::!A::De)).
  + apply Permutation_sym.
    do 2 apply Permutation_cons_app; auto.
  + apply IH.
    revert H; apply in_ill1_perm.
    rewrite app_assoc.
    apply Permutation_cons_app.
    rewrite <- app_assoc.
    apply Permutation_app; auto.
    apply Permutation_cons_app; auto.
Qed.

Fact S_ill_wc_cntr Γ Δ B : ‼Γ++‼Γ++Δ ⊢ B -> ‼Γ++ Δ ⊢ B.
Proof.
  revert Γ Δ; intros Ga.
  induction Ga as [ | A Ga IH ]; simpl; auto; intros De.
  intros H.
  apply in_ill4_cntr.
  apply in_ill4_perm with (map ll_ban Ga ++ (!A::!A::De)).
  + apply Permutation_sym.
    do 2 apply Permutation_cons_app; auto.
  + apply IH.
    revert H; apply in_ill4_perm.
    rewrite app_assoc.
    apply Permutation_cons_app.
    rewrite <- app_assoc.
    apply Permutation_app; auto.
    apply Permutation_cons_app; auto.
Qed.

Theorem S_ill_restr_weak_cntr Σ Γ A B : In A Σ -> ‼Σ++Γ ⊢r B <-> !A::‼Σ++Γ ⊢r B.
Proof.
  revert Σ Γ; intros Si Ga.
  intros H.
  apply In_perm in H.
  destruct H as (Si' & H).
  split.
  + apply in_ill1_weak.
  + intros H1.
    apply in_ill1_perm with (‼(A :: Si') ++ Ga).
    * apply Permutation_app; auto.
      apply Permutation_map; auto.
    * simpl; apply in_ill1_cntr.
      revert H1; apply in_ill1_perm.
      simpl; apply Permutation_cons; auto.
      change (!A::‼Si'++Ga) with (‼(A::Si')++Ga).
      apply Permutation_app; auto.
      apply Permutation_map, Permutation_sym; auto.
Qed.

Theorem S_ill_wc_weak_cntr Σ Γ A B : In A Σ -> ‼Σ++Γ ⊢ B <-> !A::‼Σ++Γ ⊢ B.
Proof.
  revert Σ Γ; intros Si Ga.
  intros H.
  apply In_perm in H.
  destruct H as (Si' & H).
  split.
  + apply in_ill4_weak.
  + intros H1.
    apply in_ill4_perm with (‼(A :: Si') ++ Ga).
    * apply Permutation_app; auto.
      apply Permutation_map; auto.
    * simpl; apply in_ill4_cntr.
      revert H1; apply in_ill4_perm.
      simpl; apply Permutation_cons; auto.
      change (!A::‼Si'++Ga) with (‼(A::Si')++Ga).
      apply Permutation_app; auto.
      apply Permutation_map, Permutation_sym; auto.
Qed.

(* We prove soundness for the stronger system *)

Section trivial_phase_semantics.

  Variables (n : nat) (s : ll_vars -> vec nat n -> Prop).

  Reserved Notation "'⟦' A '⟧'" (at level 65).

  Definition ill_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
  Definition ill_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b. 
  
  Infix "**" := ill_tps_mult (at level 65, right associativity).
  Infix "-*" := ill_tps_imp (at level 65, right associativity).

  Fact ll_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : 
             (forall x, X1 x -> X2 x)
          -> (forall x, Y1 x -> Y2 x)
          -> (forall x, (X1**Y1) x -> (X2**Y2) x).
  Proof.
    intros H1 H2 x (a & b & H3 & H4 & H5); subst.
    exists a, b; auto.
  Qed.

  (* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ*)

  Fixpoint ill_tps A x : Prop :=
    match A with
      | £ X     => s X x
      | A ﹠ B  => ⟦A⟧ x /\ ⟦B⟧ x
      | !A      => ⟦A⟧ x /\ x = vec_zero
      | A ⊸ B   => (⟦A⟧ -* ⟦B⟧) x
      | A ⊗ B   => (⟦A⟧ ** ⟦B⟧) x
      | A ⊕ B   => ⟦A⟧ x \/ ⟦B⟧ x
      | ⟘              => False
      | ⟙              => True
      | 𝝐               => x = vec_zero
    end
  where "⟦ A ⟧" := (ill_tps A).

  Reserved Notation "'[[' Γ ']]'" (at level 0).

  Fixpoint ill_tps_list Γ :=
    match Γ with
      | ∅    => eq vec_zero
      | A::Γ => ⟦A⟧ ** [[Γ]]
    end
  where "[[ Γ ]]" := (ill_tps_list Γ).

  Fact ill_tps_app Γ Δ x : [[Γ++Δ]] x <-> ([[Γ]]**[[Δ]]) x.
  Proof.
    revert Γ Δ x; intros Ga De.
    induction Ga as [ | A Ga IH ]; intros x; simpl; split; intros Hx.
    + exists vec_zero, x; simpl; rew vec.
    + destruct Hx as (a & b & H1 & H2 & H3); subst; auto; rewrite vec_zero_plus; auto.
    + destruct Hx as (a & b & H1 & H2 & H3).
      apply IH in H3.
      destruct H3 as (c & d & H4 & H5 & H6).
      exists (vec_plus a c), d; split.
      * subst; apply vec_plus_assoc.
      * split; auto.
        exists a, c; auto.
    + destruct Hx as (y & d & H1 & H2 & H3).
      destruct H2 as (a & g & H2 & H4 & H5).
      exists a, (vec_plus g d); split.
      * subst; symmetry; apply vec_plus_assoc.
      * split; auto.
        apply IH.
        exists g, d; auto.
  Qed.

  Fact ill_tps_lbang Γ x : [[‼Γ]] x <-> [[Γ]] x /\ x = vec_zero.
  Proof.
    revert Γ x; intros Ga.
    induction Ga as [ | A Ga IH ]; intros x.
    + simpl; split; auto; tauto.
    + split.
      * intros (a & g & H1 & H2 & H3).
        split.
        - exists a, g; repeat split; auto.
          ** apply H2.
          ** apply IH; auto.
        - apply IH, proj2 in H3.
          apply proj2 in H2; subst; auto.
          apply vec_zero_plus.
      * intros ((a & g & H1 & H2 & H3) & H4).
        exists x, x.
        assert (a = vec_zero /\ g = vec_zero) as E.
        { apply vec_plus_is_zero; subst; auto. }
        destruct E; subst; repeat split; auto; rew vec.
        apply IH; auto.
  Qed.

  Fact ill_tps_list_bang_zero Γ : [[‼Γ]] vec_zero <-> forall A, In A Γ -> ⟦A⟧ vec_zero.
  Proof.
    induction Γ as [ | A Ga IH ].
    + split.
      * simpl; tauto.
      * intros _; simpl; auto.
    + split.
      * intros (u & v & H1 & H2 & H3).
        destruct H2 as [ H2 H4 ]; subst; auto.
        rewrite vec_zero_plus in H1; subst.
        rewrite IH in H3.
        intros B [ E | HB ]; subst; auto.
      * intros H.
        exists vec_zero, vec_zero.
        rewrite vec_zero_plus; repeat split; auto.
        - apply H; left; auto.
        - rewrite IH.
          intros; apply H; right; auto.
  Qed.

  (* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ*)
 
  Fact ill_tps_perm Γ Δ : Γ ~p Δ -> forall x, [[Γ]] x -> [[Δ]] x.
  Proof.
    induction 1 as [ | A Ga De H IH | A B Ga | ]; simpl; auto.
    + intros x (a & b & H1 & H2 & H3).
      exists a, b; repeat split; auto.
    + intros x (a & b & H1 & H2 & c & d & H3 & H4 & H5).
      exists c, (vec_plus a d); split.
      * subst; rewrite (vec_plus_comm c), vec_plus_assoc, (vec_plus_comm c); auto.
      * split; auto.
        exists a, d; auto.
  Qed.
  
  Definition ill_sequent_tps Γ A := [[Γ]] -* ⟦A⟧.

  Notation "'[<' Γ '|-' A '>]'" := (ill_sequent_tps Γ A).

  Fact ill_sequent_tps_mono Γ A B :
     (forall x, ⟦A⟧ x -> ⟦B⟧ x) -> forall x, [< Γ |- A >] x -> [< Γ |- B >] x.
  Proof.
    intros H x; simpl; unfold ill_sequent_tps.
    intros H1 a H2.
    apply H, H1; auto.
  Qed.

  Fact ill_perm_tps Γ Δ : Γ ~p Δ -> forall x A, [< Γ |- A >] x -> [< Δ |- A >] x.
  Proof.
    intros H1 x B; unfold ill_sequent_tps.
    intros H2 a H3.
    apply H2; revert H3. 
    apply ill_tps_perm, Permutation_sym; auto.
  Qed.

  Fact ill_sequent_tps_eq  Γ A : [< Γ |- A >] vec_zero <-> forall x, [[Γ]] x -> ⟦A⟧ x.
  Proof.
    split.
    * intros H x Hx.
      rewrite <- vec_zero_plus, vec_plus_comm.
      apply (H x); trivial.
    * intros H x Hx.
      rewrite vec_plus_comm, vec_zero_plus; auto.
  Qed.

  Theorem ill_tps_sound Γ A : Γ ⊢ A -> [< Γ |- A >] vec_zero.
  Proof.
    induction 1 as [ A 
                   | Γ Δ A B H1 IH1 H2 IH2
                   | Γ Δ A H1 H2 IH2
                   | Γ Δ A B C H1 IH1 H2 IH2
                   | Γ A B H1 IH1
                   | Γ A B C H1 IH1
                   | Γ A B C H1 IH1
                   | Γ A B H1 IH1 H2 IH2
                   | Γ A B H1 IH1 
                   | Γ A H1 IH1
                   | Γ A B H1 IH1
                   | Γ A B H1 IH1
                   | Γ A B C H1 IH1
                   | Γ Δ A B H1 IH1 H2 IH2
                   | Γ A B C H1 IH1 H2 IH2
                   | Γ A B H1 IH1
                   | Γ A B H1 IH1
                   | Γ A
                   | Γ
                   | Γ A H1 IH1
                   |
                   ]; unfold ill_sequent_tps in * |- *.

    + intros x; simpl; intros (a & b & H1 & H2 & H3); subst; eq goal H2.
      f_equal; do 2 rewrite vec_plus_comm, vec_zero_plus; auto.

    (* Cut Rule *)
 
    + intros x Hx.
      rewrite ill_tps_app in Hx.
      apply IH2.
      destruct Hx as (a & b & G1 & G2 & G3); subst.
      exists a, b; split; auto.
      split; auto.
      rewrite <- vec_zero_plus, vec_plus_comm.
      apply IH1; auto.

    + revert IH2; apply ill_perm_tps; auto.

    + intros x (y & z & H3 & H4 & H5); simpl.
      apply IH2.
      apply ill_tps_app in H5.
      destruct H5 as (g & d & H5 & H6 & H7).
      simpl in H4.
      apply IH1, H4 in H6.
      exists (vec_plus y g), d; repeat split; auto.
      * subst; apply vec_plus_assoc.
      * eq goal H6; f_equal; rew vec.

    + simpl; intros y Hy a Ha.
      rewrite vec_plus_assoc.
      apply IH1.
      exists a, y; repeat split; auto; lia.

    + intros x (a & b & H2 & H3 & H4); apply IH1.
      exists a, b; repeat split; auto; apply H3.

    + intros x (a & b & H2 & H3 & H4); apply IH1.
      exists a, b; repeat split; auto; apply H3.

    + intros x Hx; split.
      * apply IH1; auto.
      * apply IH2; auto.
   
    + intros x (a & g & H2 & H3 & H4).
      apply IH1; exists a, g; repeat split; auto.
      apply H3.

    + intros x Hx; split.
      apply IH1; auto.
      rew vec.
      apply ill_tps_lbang in Hx; tauto.

    + intros x (a & g & H2 & H3 & H4).
      apply IH1.
      apply proj2 in H3; subst; auto.
      rew vec; auto.
  
    + intros x (a & g & H2 & H3 & H4).
      apply IH1.
      exists a, g.
      repeat (split; auto).
      exists a, g.
      repeat (split; auto).
      apply proj2 in H3.
      subst; rew vec; auto.

    (* ⊗ left *)

    + intros x Hx.
      apply IH1.
      destruct Hx as (c & g & ? & (a & b & ? & H2 & H3) & H4); subst.
      exists a, (vec_plus b g); split; auto.
      * rewrite vec_plus_assoc; trivial.
      * split; auto; exists b, g; auto.

    (* ⊗ right *)

    + intros x Hx.
      apply ill_tps_app in Hx.
      destruct Hx as (a & b & ? & H3 & H4); subst.
      exists a, b; split.
      * rewrite vec_plus_comm, vec_zero_plus; auto.
      * split; rewrite <- vec_zero_plus, vec_plus_comm.
        - apply IH1; auto.
        - apply IH2; auto.

    (* ⊕ left & ⊕ right 1 & 2 *)

    + intros x Hx.
      destruct Hx as (u & g & ? & [ G1 | G1 ] & G2); subst.
      * apply IH1; exists u, g; auto.
      * apply IH2; exists u, g; auto.
    + intros x Hx; left; apply IH1; auto.
    + intros x Hx; right; apply IH1; auto.

    (* ⟘ left, ⟙ right *)

    + intros ? (? & _ & _ & [] & _).    
    + intros x _; red; trivial.

    (* 𝝐 unit left & right *)

    + intros x (i & g & ? & H2 & H3); subst.
      red in H2; subst.
      rewrite vec_zero_plus.
      apply IH1; auto.
    + intros x Hx; red in Hx; subst.
      rewrite vec_zero_plus; red; trivial.
  Qed.

  (* This semantics is NOT complete for ILL 
     or even the (!,&,-o) fragment but it is
     complete for the EILL fragment *)
  
End trivial_phase_semantics.
