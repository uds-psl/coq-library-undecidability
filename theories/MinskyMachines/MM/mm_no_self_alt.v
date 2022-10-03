(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* * Minsky machines to FRACTRAN programs *)
(* ** Removal of self-loops in MMAs using syntactic and semantic
      properties of the generic compiler *)

Require Import List Arith Lia.

Import ListNotations.

From Undecidability.Shared.Libs.DLW
  Require Import utils pos vec subcode sss compiler compiler_correction.

From Undecidability.MinskyMachines.MM
  Require Import mm_defs.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v). (* clashes with ListNotations below *)

Local Notation "I // s -1> t" := (mm_sss I s t).
Local Notation "P // s -+> t" := (sss_progress (@mm_sss _) P s t).
Local Notation "P // s ->> t" := (sss_compute (@mm_sss _) P s t).
Local Notation "P // s ~~> t" := (sss_output (@mm_sss _) P s t).
Local Notation "P // s ↓" := (sss_terminates (@mm_sss _) P s). 

Section no_self_loops.

  Variables (n : nat).

  Definition mm_no_self_loops (Q : nat * list (mm_instr (pos n))) := 
    forall i x, ~ (i,[DEC x i]) <sc Q.

  Implicit Types (P Q : list (mm_instr (pos n))).

  Fact mm_no_self_loops_app i P Q : mm_no_self_loops (i,P) 
                                 -> mm_no_self_loops (length P+i,Q)
                                 -> mm_no_self_loops (i,P++Q).
  Proof.
    intros H1 H2 j x H.
    apply subcode_app_invert_right in H.
    destruct H as [ H | H ]; revert H.
    + apply H1.
    + apply H2.
  Qed.

  Fact mm_no_self_loops_cons_inv i ρ P :
         mm_no_self_loops (i,ρ::P)
      -> mm_no_self_loops (1+i,P).
  Proof.
    intros H j x Hj.
    now apply (H j x), subcode_cons.
  Qed.

End no_self_loops.

Section remove_self_loops.

  Variable (n : nat).

  Implicit Type ρ : mm_instr (pos n).

  Local Definition il ρ :=
    match ρ with
      | INC x   => 1
      | DEC x j => 3
    end.

  Section instr_compiler.

    Variable (lnk : nat -> nat).

    Local Definition ic i ρ :=
      match ρ with
        | INC x   => [ INC (pos_nxt x) ]
        | DEC x j => [ DEC (pos_nxt x) (2+lnk i) ;
                       DEC  pos0 (3+lnk i) ;
                       DEC  pos0 (lnk j) ]
      end.

    Local Fact il_ic_length i ρ : length (ic i ρ) = il ρ.
    Proof. now destruct ρ. Qed.

    Local Fact il_le ρ : 1 <= il ρ.
    Proof. destruct ρ; simpl; lia. Qed.

  End instr_compiler.

  Hint Resolve subcode_refl : core.

  Let simul (v : vec nat n) (w : vec nat (S n)) := w#>pos0 = 0 /\ v = vec_tail w.

  Local Fact ic_correct : instruction_compiler_sound ic (@mm_sss _) (@mm_sss _) simul.
  Proof.
    intros lnk I i1 v1 i2 v2 w1.
    change i1 with (fst (i1,v1)) at 2 3 4 5 6 7.
    change i2 with (fst (i2,v2)) at 2.
    change v1 with (snd (i1,v1)) at 5.
    change v2 with (snd (i2,v2)) at 3.
    generalize (i1,v1) (i2,v2); intros st1 st2; clear i1 v1 i2 v2.
    induction 1 as [ i x v | i x k v H | i x k v u H ]; simpl.
    + intros -> [H1 ->]; rew vec. 
      exists (vec_change w1 (pos_nxt x) (S (w1#>(pos_nxt x)))); msplit 2; rew vec; auto.
      * mm sss INC with (pos_nxt x).
        mm sss stop.
      * clear H1; vec split w1 with y; rew vec.
    + vec split w1 with y; intros H1 [H2 H3].
      revert H2 H3; simpl; rew vec; intros -> ->.
      exists (0##w1); msplit 2; auto.
      mm sss DEC zero with (pos_nxt x) (S (S (lnk i))).
      mm sss DEC zero with pos0 (lnk k).
      mm sss stop.
    + vec split w1 with y; intros H1 [H2 H3].
      revert H2 H3; simpl; rew vec; intros -> ->.
      exists (0##vec_change w1 x u); msplit 2; auto.
      mm sss DEC S with (pos_nxt x) (S (S (lnk i))) u.
      mm sss DEC zero with pos0 (S (S (S (lnk i)))).
      mm sss stop.
      now simpl; rew vec; f_equal.
  Qed.

  Section no_self_loops. 

    Let gc := generic_syntactic_compiler _ _ il_le il_ic_length.

    Variables (P : list (mm_instr (pos n))).

    Let Q := cs_code gc (1,P) 1.

    Local Fact gc_no_self_loops : mm_no_self_loops (1,Q).
    Proof.
      generalize (cs_not_between gc).
      destruct gc as [ lnk code H0 H1 H2 H3 H4 H5 H6 ]; simpl; clear gc; intro H7.
      intros j x H.
      apply H6 in H as (k & [ x' | x' j' ] & G1 & G2); simpl ic in G2.
      + apply subcode_cons_invert_right in G2 as [ (_ & ?) | G2 ]; try easy.
        now apply subcode_nil_invert in G2.
      + repeat apply subcode_cons_invert_right in G2 as [ (E1 & E2) | G2 ].
        * inversion E2; lia.
        * inversion E2; lia.
        * inversion E2; clear E2.
          specialize (H7 (1,P) 1 j' k).
          apply H2 with (i := 1) in G1; simpl in G1; lia.
        * now apply subcode_nil_invert in G2.
      Qed.

    Local Fact gc_bounded i x j : (i,DEC x j::nil) <sc (1,Q) -> j < 1+length Q.
    Proof.
      destruct gc as [ lnk code H0 H1 H2 H3 H4 H5 H6 ]; clear gc.
      simpl in Q.
      intros H.
      apply H6 in H as (k' & [ x' | x' j' ] & G1 & G2); simpl ic in G2.
      + apply subcode_cons_invert_right in G2 as [ (_ & ?) | G2 ]; try easy.
        now apply subcode_nil_invert in G2.
      + generalize G1; intros G0.
        apply H5 with (i := i) in G0; fold Q in G0; apply subcode_length' in G0; simpl in G0.
        apply subcode_in_code with (i := k') in G1.
        2: simpl; lia.
        apply H1 with (i := i) in G1; fold Q in G1; red in G1; unfold code_end, code_start in G1.
        unfold fst, snd in G1.
        admit.
    Admitted.

    Hint Resolve il_ic_length ic_correct mm_sss_total_ni : core.

    Let lnk := cs_link gc (1,P) 1.

    Theorem mm_remove_self_loops_strong : { Q | mm_no_self_loops (1,Q)
                                     /\ (forall i x j, (i,DEC x j::nil) <sc (1,Q) -> j < 1+length Q)
                                     /\ (forall v w, (exists j, (1,P) // (1,v) ~~> (j, w)) -> (exists j, (1,Q) // (1,0##v) ~~> (j, 0 ## w))) 
                                     /\ (forall v,  (1,Q) // (1,0##v) ↓ -> (1,P) // (1,v) ↓)}.
    Proof.
      destruct (eq_nat_dec (length P) 0) as [ HlP | HlP ].
      + (** This is the case where P is empty *)
        exists nil; msplit 2.
        * intros i rho ([ | ] & ? & ? & ?); discriminate.
        * intros i x j ([ | ] & ? & ? & ?); discriminate.
        * destruct P; try discriminate.
          split.
          - exists 1. 
            split; simpl; try lia; mm sss stop; do 2 f_equal.
            destruct H as [j [[i Hj] ?]].
            eapply sss_steps_stall in Hj as [_ [=]]; auto.
            simpl; lia.
          - intros v [(j, w) H]. 
            exists (1,v);split; simpl; try lia; mm sss stop.
      + exists Q; msplit 3.
        * apply gc_no_self_loops.
        * apply gc_bounded.
        * intros v w (j & Hw).
          destruct ((compiler_syntactic_sound_output il_ic_length gc ic_correct (P := (1,P)) 1) 1 v j w (0##v)) as (w' & (H1 & H2) & H3). 
          - split; auto; split; rew vec.
          - revert H1 H2 H3; vec split w' with y; simpl; intros -> <- H3.
            exists (cs_link gc (1,P) 1 j).
            now rewrite <- (cs_fst gc (1,P) 1) at 2.
        * intros v.
          apply (compiler_syntactic_term_equiv il_ic_length gc (@mm_sss_total_ni _) (@mm_sss_fun _) ic_correct 1 P 1). 
          split; rew vec.
    Qed.

    Theorem mm_remove_self_loops : { Q |  mm_no_self_loops (1,Q)
                                       /\ (forall i x j, (i,DEC x j::nil) <sc (1,Q) -> j < 1+length Q)
                                       /\ forall v, (1,P) // (1,v) ↓ <-> (1,Q) // (1,0##v) ↓ }.
    Proof.
      destruct mm_remove_self_loops_strong as (Q' & H1 & H2 & H3 & H4).
      exists Q'; msplit 2; auto.
      intros v; split; auto.
      intros ((j,w) & Hw).
      destruct (H3 v w) as (j' & Hj'); eauto.
      now exists (j',0##w).
    Qed.

  End no_self_loops.

End remove_self_loops.