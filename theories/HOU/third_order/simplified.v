Set Implicit Arguments.
Require Import RelationClasses Morphisms List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus unification.unification.
From Undecidability.HOU Require Import third_order.pcp third_order.encoding.
Import ListNotations ArsInstances.

Definition MPCP' '(c, C) :=
  exists I, I ⊆ nats (length C) /\
       hd c ++ @concat symbol (select I (heads C)) = tl c ++ concat (select I (tails C)).

Lemma MPCP_MPCP' c C: MPCP (c, C) <-> MPCP' (c, c::C).
Proof. firstorder. Qed.

(* * Simplified Reduction *)
Section SimplifiedReduction.

  Variable (X: Const).

  Definition redtm (w: word) (W: list word): exp X :=
    lambda lambda (enc 0 1 w) (AppR (var 2) (Enc 0 1 W)).
  Definition redctx (n: nat)  := [Arr (repeat (alpha → alpha) n) alpha].

  Lemma redtm_typing w W:
    redctx (length W) ⊢(3) redtm w W : (alpha → alpha) → (alpha → alpha) →  alpha.
  Proof.
    unfold redctx; do 3 econstructor.
    - eapply enc_typing; eauto.
    - eapply AppR_ordertyping;[ eapply Enc_typing|]; simplify;
        econstructor; cbn; simplify; eauto.
  Qed.

  (* ** Reduction Function *)
  Program Instance MPCP'_to_U P : orduni 3 X :=
    { 
      Gamma₀ :=  redctx (length (snd P));
      s₀ :=  redtm (hd (fst P)) (heads (snd P));
      t₀ :=  redtm (tl (fst P)) (tails (snd P));
      A₀ := (alpha → alpha) → (alpha → alpha) →  alpha;
      H1₀ := redtm_typing (hd (fst P)) (heads (snd P));
      H2₀ := redtm_typing (tl (fst P)) (tails (snd P));
    }.
  Next Obligation. now simplify. Qed.
  Next Obligation. now simplify. Qed.


  (* ** Forward Direction *)
  Lemma MPCP'_U3 P: MPCP' P -> OU 3 X (MPCP'_to_U P).
  Proof.
    destruct P as [c C]; intros (I & Sub & EQ).
    exists [alpha]. exists (finst I (length C) .: var); split.
    - intros x A. destruct x as [| [|]]; try discriminate; cbn.
      injection 1 as ?; subst. 
      eapply finst_typing; eauto.
    - cbn -[enc]. rewrite !enc_subst_id; trivial. 
      rewrite !AppR_subst, !Enc_subst_id; trivial.
      cbn; rewrite !ren_plus_base, !ren_plus_combine;
        change (1 + 1) with 2.
      erewrite <-map_length at 1. symmetry.
      erewrite <-map_length at 1. erewrite !finst_equivalence.
      all: simplify; trivial.
      now rewrite <-!enc_app, EQ. 
  Qed.  

  (* ** Backward Direction *)
  Lemma U3_MPCP' P:
    OU 3 X (MPCP'_to_U P) -> MPCP' P.
  Proof.
    destruct P as [c C].
    intros (Delta & sigma & T1 & EQ).
    specialize (T1 0 (Arr (repeat (alpha → alpha) (length C)) alpha)); mp T1; trivial.
    eapply ordertyping_preservation_under_renaming with (delta := add 2) (Delta := alpha :: alpha :: Delta) in T1.
    2: intros ??; cbn; eauto. 
    eapply main_lemma with (u := 0) (v := 1) in T1 as (I & S & H); trivial.
    2, 3: intros (?&?&?) % vars_ren; discriminate. 
    exists I. intuition idtac.
    revert EQ. cbn -[enc]. rewrite !enc_subst_id; trivial. 
    rewrite !AppR_subst; rewrite ?Enc_subst_id; trivial; cbn -[add].
    all: unfold funcomp; cbn -[add]; rewrite !ren_plus_base, !ren_plus_combine;
      change (1 + 1) with 2.
    specialize (H (heads C)) as H1; mp H1; simplify; trivial.
    specialize (H (tails C)) as H2; mp H2; simplify; trivial.
    destruct H1 as [t' [-> H1]], H2 as [t'' [-> H2]].
    rewrite <-!select_map, !enc_concat, <-!enc_app.
    intros EQ % equiv_lam_elim % equiv_lam_elim.
    eapply enc_eq in EQ. 1 - 2: intuition idtac. lia.
    all: intros s; try eapply H1; try eapply H2.
  Qed.


End SimplifiedReduction.


Lemma MPCP_U3 X: MPCP ⪯ OU 3 X.
Proof.
  exists (fun '(c, C) => MPCP'_to_U X (c, c::C)). intros [c C]; rewrite MPCP_MPCP'; split.
  all: eauto using MPCP'_U3, U3_MPCP'.
Qed.  
