(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Permutation Arith.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

From Undecidability.ILL Require Import ILL EILL ill.

Set Implicit Arguments.

Local Infix "~p" := (@Permutation _) (at level 70).

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ *)

Notation "⦑ c ⦒" := (eill_cmd_map c) (at level 0).

Notation "Σ ; Γ ⊦ u" := (G_eill Σ Γ u) (at level 70, no associativity).

Theorem g_eill_mono_Si Σ Σ' Γ u : incl Σ Σ' -> Σ; Γ ⊦ u -> Σ'; Γ ⊦ u.
Proof.
  revert Σ Σ' Γ; intros Si Si' Ga.
  intros H H1; revert H1 Si' H.
  induction 1 as [ u
                 | Ga De p H1 H2 IH2 
                 | Ga a p q H1 H2 IH2
                 | Ga De p q r H1 H2 IH2 H3 IH3
                 | Ga p q r H1 H2 IH2 H3 IH3
                 ]; intros Si' HSi.
  + apply in_geill_ax.
  + apply in_geill_perm with (1 := H1); auto.
  + apply in_geill_inc with (1 := HSi _ H1); auto.
  + apply in_geill_dec with (1 := HSi _ H1); auto.
  + apply in_geill_fork with (1 := HSi _ H1); auto.
Qed.

(* G_eill is sound wrt. the S_ill 

   this proof only uses somes of the rules of
   the cut-free (!,&,-o) fragment
*)

Notation "Γ ⊢ A" := (S_ill_restr Γ A) (at level 70, no associativity).

Theorem G_eill_sound Σ Γ p : Σ; Γ ⊦ p -> map (fun c => !⦑c⦒) Σ ++ map £ Γ ⊢ £ p.
Proof.
  revert Σ; intros Si.
  induction 1 as [ u
                 | Ga De p H1 H2 IH2 
                 | Ga a p q H1 H2 IH2
                 | Ga De p q r H1 H2 IH2 H3 IH3
                 | Ga p q r H1 H2 IH2 H3 IH3
                 ].
  + rewrite <- map_map; apply S_ill_restr_weak; apply in_ill1_ax.
  + revert IH2; apply in_ill1_perm.
    apply Permutation_app; auto.
    apply Permutation_map; auto.
  + rewrite <- map_map; apply S_ill_restr_weak_cntr with (1 := in_map _ _ _ H1); simpl.
    rewrite map_map.
    apply in_ill1_bang_l.
    apply in_ill1_perm with (((£ a ⊸ £ p) ⊸ £ q) :: ((map (fun c => !⦑c⦒) Si ++ map £ Ga) ++ nil)).
    * rewrite app_nil_r; auto.
    * apply in_ill1_limp_l.
      2: apply in_ill1_ax.
      apply in_ill1_limp_r.
      revert IH2; apply in_ill1_perm.
      simpl; apply Permutation_sym, Permutation_cons_app; auto.
  + rewrite <- map_map.
    apply S_ill_restr_cntr.
    rewrite map_map.
    rewrite <- map_map; apply S_ill_restr_weak_cntr with (1 := in_map _ _ _ H1); simpl; rewrite map_map.
    apply in_ill1_bang_l.
    rewrite map_app.
    apply in_ill1_perm with (£ p ⊸ £ q ⊸ £ r :: (map (fun c => !⦑c⦒) Si ++ map £ Ga) 
                                             ++ (map (fun c => !⦑c⦒) Si ++ map £ De)).
    * apply Permutation_cons; auto.
      rewrite <- app_assoc; apply Permutation_app; auto.
      do 2 rewrite app_assoc; apply Permutation_app; auto.
      apply Permutation_app_comm.
    * apply in_ill1_limp_l; auto.
      apply in_ill1_perm with (£ q ⊸ £ r :: ((map (fun c => !⦑c⦒) Si ++ map £ De) ++ nil)).
      - rewrite app_nil_r; auto.
      - apply in_ill1_limp_l; auto.
        apply in_ill1_ax.
  + rewrite <- map_map; apply S_ill_restr_weak_cntr with (1 := in_map _ _ _ H1); simpl.
    rewrite map_map.
    apply in_ill1_bang_l.
    apply in_ill1_perm with (£ p & £ q ⊸ £ r :: ((map (fun c => !⦑c⦒) Si ++ map £ Ga) ++ nil)).
    * rewrite app_nil_r; auto.
    * apply in_ill1_limp_l.
      - apply in_ill1_with_r; auto.
      - apply in_ill1_ax.
Qed.

Section TPS.

  Variables (n : nat) (s : ill_vars -> vec nat n -> Prop) (rx : pos n -> ill_vars).

  Fact ill_tps_vec_map_list_mono : 
       (forall (p : pos n), s (rx p) (vec_one p)) 
     -> forall v, ill_tps_list s (map £ (vec_map_list v rx)) v.
  Proof.
    intros H v; rewrite map_vec_map_list.
    induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n).
    + rewrite vec_map_list_zero; simpl; tauto.
    + rewrite vec_map_list_one; simpl.
      exists (vec_one p), vec_zero; rew vec; repeat split; auto.
    + apply ill_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
      apply ill_tps_app.
      exists v, w; repeat split; auto.
  Qed.

  Fact ill_tps_vec_map_list : 
       (forall (p : pos n) (v : vec nat n), s (rx p) v <-> v = vec_one p) 
     -> forall v w, ill_tps_list s (map £ (vec_map_list v rx)) w <-> v = w.
  Proof.
    intros H v; rewrite map_vec_map_list.
    induction v as [ | p | v w Hv Hw ] using (@vec_nat_induction n); intros z.
    + rewrite vec_map_list_zero; simpl; tauto.
    + rewrite vec_map_list_one; simpl.
      split.
      * intros (a & b & H1 & H2 & H3).
        apply H in H2; subst; rew vec.
      * intros [].
        exists (vec_one p), vec_zero; rew vec; repeat split; auto.
        apply H; auto.
    + split.
      * intros Hz.
        apply ill_tps_perm with (1 := vec_map_list_plus _ _ _) in Hz.
        apply ill_tps_app in Hz.
        destruct Hz as (a & b & H1 & H2 & H3).
        apply Hv in H2.
        apply Hw in H3.
        subst; auto.
      * intros [].
        apply ill_tps_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
        apply ill_tps_app.
        exists v, w; repeat split; auto.
        - apply Hv; auto.
        - apply Hw; auto.
  Qed.

End TPS.

Section g_eill_complete_bound.
 
  Variable (Σ : list eill_cmd) (Γ : list eill_vars) (n : nat).

  Notation vars := (flat_map eill_cmd_vars Σ ++ Γ).

  (* This is a surjection from [0,n-1] into the vars of Si,Ga *)

  Hypothesis (w : vec eill_vars n)
             (w_surj : forall u, In u vars -> exists p, u = vec_pos w p).

  Let rx p := vec_pos w p.

  Let Hrx l : incl l (flat_map eill_cmd_vars Σ ++ Γ) -> exists v, l ~p vec_map_list v rx.
  Proof.
    induction l as [ | x l IHl ]; intros H.
    + exists vec_zero; rewrite vec_map_list_zero; auto.
    + destruct IHl as (v & Hv).
      { intros ? ?; apply H; right; auto. }
      assert (In x vars) as Hx.
      {  apply H; left; auto. }
      destruct w_surj with (u := x)
        as (p & ?); subst; auto. 
      exists (vec_plus (vec_one p) v).
      apply Permutation_sym.
      apply Permutation_trans with (1 := vec_map_list_plus _ _ _).
      rewrite vec_map_list_one.
      apply perm_skip, Permutation_sym; auto.
  Qed.

  Let s x v := Σ; vec_map_list v rx ⊦ x.

  Notation "⟦ A ⟧" := (ill_tps s A) (at level 65).
  Notation "'[<' Γ '|-' A '>]'" := (ill_sequent_tps s Γ A) (at level 65).

  Theorem G_eill_complete_bound x : 
            [< map (fun c => !⦑c⦒) Σ ++ map £ Γ |- £ x >] vec_zero 
         -> Σ; Γ ⊦ x.
  Proof using w_surj.
    intros H.
    do 2 red in H.
    destruct (@Hrx Γ) as (v & Hv).
    1: { intros ? ?; apply in_or_app; right; auto. }
    apply in_geill_perm with (1 := Permutation_sym Hv).
    fold (s x v).
    rewrite <- (vec_zero_plus v), vec_add_comm.
    apply H.
    rewrite ill_tps_app.
    exists vec_zero, v.
    repeat split; auto; try (rew vec; fail).
    2:{ apply ill_tps_perm with (map £ (vec_map_list v (fun p => rx p))).
        apply Permutation_map, Permutation_sym; auto.
        apply ill_tps_vec_map_list_mono; auto.
        intros p.
        red.
        rewrite vec_map_list_one.
        apply in_geill_ax. }

    rewrite <- map_map.
    apply ill_tps_list_bang_zero.
    intros A HA.
    apply in_map_iff in HA.
    destruct HA as (c & H1 & H2); subst.
    destruct c as [ a p q | a p q | p q r ]; simpl.

    (* (_ -o _) -o _ *) 

    + intros y Hy; rew vec; unfold s.
      apply in_geill_inc with a p; auto.
      destruct (@Hrx (a::nil)) as (z & Hz).
      intros ? [ [] | [] ]; apply in_or_app; left.
      * apply in_flat_map; exists (LL_INC a p q); simpl; auto.
      * apply in_geill_perm with (vec_map_list (vec_plus z y) rx).
        - apply Permutation_trans with (1 := vec_map_list_plus _ _ _).
          change (a::vec_map_list y rx) with ((a::nil)++vec_map_list y rx).
          apply Permutation_app; auto.
          apply Permutation_sym; auto.
        - apply Hy; red.
          apply in_geill_perm with (1 := Hz), in_geill_ax.

    (* _ -o (_ -o _) *)

    + intros u Hu y Hy.
      rew vec.
      rewrite vec_add_comm.
      apply in_geill_perm with (1 := Permutation_sym (vec_map_list_plus _ _ _)).
      apply in_geill_dec with a p; auto.

    (* (_ & _) -o _ *)
    
    + intros u (H3 & H4).
      rew vec.
      apply in_geill_fork with p q; auto.
  Qed.

End g_eill_complete_bound.

Section g_eill_complete.
 
  Variable (Σ : list eill_cmd) (Γ : list eill_vars).

  Notation vars := (flat_map eill_cmd_vars Σ ++ Γ).

  Let vv := nat_sort vars.

  Let Hvv1 : list_injective vv.
  Proof. apply nat_sorted_injective, nat_sort_sorted. Qed.

  Let Hvv2 : incl vv (flat_map eill_cmd_vars Σ ++ Γ) 
          /\ incl (flat_map eill_cmd_vars Σ ++ Γ) vv.
  Proof. apply nat_sort_eq. Qed.

  Let n := length vv.
  Let w : vec eill_vars n := proj1_sig (list_vec_full vv).
  Let Hw : vec_list w = vv.
  Proof. apply (proj2_sig (list_vec_full vv)). Qed.

  Let w_surj : forall u, In u vars -> exists p, u = vec_pos w p.
  Proof.
    intros u Hu.
    apply Hvv2 in Hu; rewrite <- Hw in Hu.
    revert Hu; apply vec_list_inv.
  Qed.

  Variables (x : eill_vars)
            (Hvalid : forall n s, @ill_sequent_tps n s (map (fun c => !⦑c⦒) Σ ++ map £ Γ) (£ x) vec_zero).

  Theorem G_eill_complete : Σ; Γ ⊦ x.
  Proof using Hvalid.
    apply G_eill_complete_bound with (1 := w_surj), Hvalid.
  Qed.

End g_eill_complete.

From Undecidability.ILL Require Import CLL ill_cll schellinx.

Fact eill_no_bot c : ~ ill_has_bot ⦑ c ⦒.
Proof. induction c; simpl; tauto. Qed.

(* eill is a fragment of ILL and G-eill is sound and complete for it *)

Section correctness_results_for_the_reduction.

  Variables (Σ : list eill_cmd) (Γ : list eill_vars) (u : nat).

  Notation Σi := (map (fun c => ill_ban ⦑c⦒) Σ).
  Notation Γi := (map ill_var Γ).
  Notation ui := (ill_var u).

  Notation Σc := (map (fun c => cll_una cll_bang [⦑c⦒]) Σ).
  Notation Γc := (map cll_var Γ).
  Notation uc := (cll_var u). 

  Theorem G_eill_correct : (Σ; Γ ⊦ u -> S_ill_restr (Σi++Γi) ui)
                        /\ (S_ill_restr (Σi++Γi) ui -> S_ill_restr_wc (Σi++Γi) ui)
                        /\ (S_ill_restr (Σi++Γi) ui -> S_ill (Σi++Γi) ui)
                        /\ (S_ill_restr_wc (Σi++Γi) ui -> S_ill_wc (Σi++Γi) ui)
                        /\ (S_ill (Σi++Γi) ui -> S_ill_wc (Σi++Γi) ui)
                        /\ (S_ill_wc (Σi++Γi) ui -> Σ; Γ ⊦ u).
  Proof.
    msplit 5.
    + apply G_eill_sound.
    + apply S_ill_restr_restr_wc.
    + apply S_ill_restr_full.
    + apply S_ill_restr_full_wc.
    + apply S_ill_full_wc.
    + intro; apply G_eill_complete.
      intros; now apply ill_tps_sound.
  Qed.

  Tactic Notation "solve" "with" int(i) int(j) :=
    let H := fresh in split; [ intro; now do i apply G_eill_correct 
                             | intros H; now do j apply G_eill_correct in H ].
 
   (* The reduction is correct for the cut-free (!,&,-o) fragment of ILL *)

  Corollary G_eill_S_ill_restr : Σ; Γ ⊦ u <-> S_ill_restr (Σi++Γi) ui.
  Proof. solve with 1 3. Qed.

  (* The reduction is correct for the (!,&,-o) fragment of ILL with cut *)

  Corollary G_eill_S_ill_restr_wc : Σ; Γ ⊦ u <-> S_ill_restr_wc (Σi++Γi) ui.
  Proof. solve with 2 2. Qed.

  (* The reduction is correct for cut-free ILL *)

  Corollary G_eill_S_ill : Σ; Γ ⊦ u <-> S_ill (Σi++Γi) ui.
  Proof. solve with 2 2. Qed.

  (* The reduction is correct for ILL *)

  Corollary G_eill_S_ill_wc : Σ; Γ ⊦ u <-> S_ill_wc (Σi++Γi) ui.
  Proof. solve with 3 1. Qed.

  Let not_bot f : In f (ui :: Σi ++ Γi) -> ~ ill_has_bot f.
  Proof.
    simpl; rewrite in_app_iff, !in_map_iff.
    intros [ <- | [ (? & <- & ?) | (? & <- & ?) ] ];
      simpl; auto; apply eill_no_bot.
  Qed.

  Theorem G_eill_S_cll : Σ; Γ ⊦ u <-> S_cll (Σc++Γc) (uc::nil).
  Proof.
    split.
    + rewrite G_eill_S_ill.
      intros H.
      rewrite ill_cll_equiv in H; auto.
      eq goal H; f_equal.
      now rewrite map_app, !map_map.
    + intros H.
      apply G_eill_S_ill, ill_cll_equiv; auto.
      eq goal H; f_equal.
      now rewrite map_app, !map_map.
  Qed.

End correctness_results_for_the_reduction.