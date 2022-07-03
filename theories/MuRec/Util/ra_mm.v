(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Max.

From Undecidability.Shared.Libs.DLW
  Require Import utils pos vec subcode sss.

From Undecidability.MinskyMachines 
  Require Import env mm_defs mme_defs mme_utils.

From Undecidability.MuRec.Util 
  Require Import recalg ra_mm_env.

Set Implicit Arguments.

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "i /e/ s '-1>' t" := (mm_sss_env eq_nat_dec i s t)  (at level 70, no associativity).
Local Notation "P /e/ s ->> t" := (sss_compute (mm_sss_env eq_nat_dec) P s t) (at level 70, no associativity).
Local Notation "P /e/ s ~~> t" := (sss_output (mm_sss_env eq_nat_dec) P s t) (at level 70, no associativity).
Local Notation "P /e/ s -[ k ]-> t" := (sss_steps (mm_sss_env eq_nat_dec) P k s t) (at level 70, no associativity).
Local Notation "P /e/ s ↓" := (sss_terminates (mm_sss_env eq_nat_dec) P s) (at level 70, no associativity).

Local Notation "i /v/ s '-1>' t" := (@mm_sss _ i s t)  (at level 70, no associativity).
Local Notation "P /v/ s ->> t" := (sss_compute (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P /v/ s ~~> t" := (sss_output (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P /v/ s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /v/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity). 

Local Notation " e ⇢ x " := (@get_env _ _ e x).
Local Notation " e ⦃  x ⇠ v ⦄ " := (@set_env _ _ eq_nat_dec e x v).

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Section mm_nat_pos.

  Definition mm_var_map (X Y : Set) (f : X -> Y) (i : mm_instr X) :=
    match i with
      | INC x   => INC (f x)
      | DEC x p => DEC (f x) p
    end.

  Definition mm_instr_var X (i : mm_instr X) :=
    match i with
      | INC x => x
      | DEC x _ => x
    end.

  Definition mm_linstr_vars X := map (@mm_instr_var X).

  Definition mm_pos_nat n := map (mm_var_map (@pos2nat n)).
  
  Definition mm_nat_pos_full n l : Forall (fun x => x < n) (mm_linstr_vars l) -> { m | l = @mm_pos_nat n m }.
  Proof.
    induction l as [ | [ x | x p ] l IHl ]; simpl; intros H.
    { exists nil; auto. }
    1,2: rewrite Forall_cons_inv in H; destruct H as [ H1 H2 ];
         destruct (IHl H2) as (m & Hm).
    + exists (INC (nat2pos H1) :: m); simpl; f_equal; auto; f_equal.
      rewrite pos2nat_nat2pos; auto.
    + exists (DEC (nat2pos H1) p :: m); simpl; f_equal; auto; f_equal.
      rewrite pos2nat_nat2pos; auto.
  Qed.

  Definition mm_nat_bound l := S (lmax (mm_linstr_vars l)).

  Fact mm_nat_bound_spec l : Forall (fun x => x < mm_nat_bound l) (mm_linstr_vars l).
  Proof.
    cut (Forall (fun x => x <= lmax (mm_linstr_vars l)) (mm_linstr_vars l)).
    + apply Forall_impl; intros; unfold mm_nat_bound; lia.
    + apply lmax_spec; auto.
  Qed.

  Definition mm_nat_pos n l : mm_nat_bound l <= n -> { m | l = @mm_pos_nat n m }.
  Proof.
    intros H; apply mm_nat_pos_full.
    generalize (mm_nat_bound_spec l).
    apply Forall_impl; intros; lia.
  Qed.

End mm_nat_pos.

Section mm_pos_nat_sem.

  Variable (n : nat).

  Implicit Types (e : nat -> nat) (v : vec nat n).

  Ltac dest x y := destruct (pos_eq_dec x y) as [ | ]; [ subst x | ]; rew env.

  Notation "v '⋈' e" := (forall p, vec_pos v p = e⇢pos2nat p) (at level 70, no associativity).

  Fact sss_mm_pos_nat rho st1 st2 e1 :
            snd st1 ⋈ e1
         -> rho /v/ st1 -1> st2
         -> exists e2, snd st2 ⋈ e2
                    /\ mm_var_map (@pos2nat n) rho /e/ (fst st1,e1) -1> (fst st2,e2). 
  Proof.
    revert st1 st2; intros (j1,v1) (j2,v2); simpl.
    intros H1 H2.
    destruct rho as [ x | x p ]; simpl in *;
      [ | case_eq (vec_pos v1 x); [ intros He1 | intros q Hq ] ].
    - exists (e1⦃pos2nat x ⇠ S (e1⇢pos2nat x)⦄).
      apply mm_sss_INC_inv in H2.
      destruct H2 as (? & ?); subst; split.
      2: constructor.
      intros p.
      destruct (pos_eq_dec x p) as [ -> | C ]; rew vec; rew env. 
      rewrite H1; assert (pos2nat x <> pos2nat p); rew env.
      contradict C; revert C; apply pos2nat_inj.
    - exists e1. 
      apply mm_sss_DEC0_inv in H2; destruct H2; subst; auto.
      split; auto; constructor; rewrite <- H1; auto.
    - exists (e1⦃pos2nat x ⇠ q⦄).
      apply mm_sss_DEC1_inv with (1 := Hq) in H2.
      destruct H2; subst; split.
      2: constructor; rewrite <- H1; auto.
      intros j. 
      destruct (pos_eq_dec x j) as [ -> | C ]; rew vec; rew env.
      rewrite H1; assert (pos2nat x <> pos2nat j); rew env.
      contradict C; revert C; apply pos2nat_inj.
  Qed.

  Fact sss_mm_pos_nat_inv rho st1 st2 v1 :
            v1 ⋈ snd st1
         -> mm_var_map (@pos2nat n) rho /e/ st1 -1> st2 
         -> exists v2, v2 ⋈ snd (st2)
                    /\ rho /v/ (fst st1,v1) -1> (fst st2,v2).
  Proof.
    revert st1 st2; intros (j1,e1) (j2,e2); simpl.
    intros H1 H2.
    destruct rho as [ x | x p ]; simpl in *;
      [ | case_eq (e1⇢pos2nat x); [ intros He1 | intros q Hq ] ].
    - exists (vec_change v1 x (S (vec_pos v1 x))).
      apply mm_sss_env_INC_inv in H2.
      destruct H2 as (? & ?); subst; split.
      2: constructor.
      intros p.
      destruct (pos_eq_dec x p) as [ -> | C ]; rew vec; rew env. 
      rewrite H1; assert (pos2nat x <> pos2nat p); rew env.
      contradict C; revert C; apply pos2nat_inj.
    - exists v1. 
      apply mm_sss_env_DEC0_inv in H2; destruct H2; subst; auto.
      split; auto; constructor; rewrite H1; auto.
    - exists (vec_change v1 x q).
      apply mm_sss_env_DEC1_inv with (1 := Hq) in H2.
      destruct H2; subst; split.
      2: constructor; rewrite H1; auto.
      intros j. 
      destruct (pos_eq_dec x j) as [ -> | C ]; rew vec; rew env.
      rewrite H1; assert (pos2nat x <> pos2nat j); rew env.
      contradict C; revert C; apply pos2nat_inj.
  Qed.

  Fact sss_steps_mm_pos_nat i P k st1 st2 e1 :
            snd st1 ⋈ e1
         -> (i,P) /v/ st1 -[k]-> st2
         -> exists e2, snd st2 ⋈ e2
                    /\ (i,@mm_pos_nat n P) /e/ (fst st1,e1) -[k]-> (fst st2,e2). 
  Proof.
    intros H1 H2; revert H2 e1 H1.
    induction 1 as [ (j,v) | k (j1,v1) (j2,v2) (j3,v3) H1 H2 IH2 ];
      simpl; intros e1 H3.
    + exists e1; split; auto; constructor.
    + destruct H1 as (q & l & rho & r & e & [= <- G2] & [= -> <-] & G3).
      destruct sss_mm_pos_nat with (2 := G3) (1 := H3) as (e2 & G4 & G5); simpl in *.
      destruct IH2 with (1 := G4) as (e3 & G6 & G7).
      exists e3; split; auto.
      constructor 2 with (st2 := (j2,e2)); auto.
      exists i, (mm_pos_nat l), (mm_var_map (@pos2nat _) rho), (mm_pos_nat r), e1; msplit 2; auto.
      * f_equal; subst P; unfold mm_pos_nat; repeat (rewrite map_app; simpl); auto.
      * unfold mm_pos_nat; rew length; auto.
  Qed. 
 
  Fact sss_steps_mm_pos_nat_inv i P k st1 st2 v1 :
            v1 ⋈ snd st1
         -> (i,@mm_pos_nat n P) /e/ st1 -[k]-> st2 
         -> exists v2, v2 ⋈ snd (st2)
                    /\ (i,P) /v/ (fst st1,v1) -[k]-> (fst st2,v2).
  Proof.
    intros H1 H2; revert H2 v1 H1.
    induction 1 as [ (j,e) | k (j1,e1) (j2,e2) (j3,e3) H1 H2 IH2 ];
      simpl; intros v1 H3.
    + exists v1; split; auto; constructor.
    + destruct H1 as (q & l & rho & r & e & [= <- G2] & [= -> <-] & G3).
      unfold mm_pos_nat in G2; apply map_middle_inv in G2.
      destruct G2 as (l' & rho' & r' & G2 & G4 & G5 & G6).
      subst rho l r.
      destruct sss_mm_pos_nat_inv with (2 := G3) (1 := H3) as (v2 & G7 & G8); simpl in *.
      destruct IH2 with (1 := G7) as (v3 & G9 & G10).
      exists v3; split; auto.
      constructor 2 with (st2 := (j2,v2)); auto.
      exists i, l', rho', r', v1; msplit 2; subst; auto; rew length; auto.
  Qed.

End mm_pos_nat_sem.

Section ra_mm_comp.

  Theorem ra_mm_compiler (n : nat) (f : recalg n) :
      { m & { P : list (mm_instr (pos (n+S m))) 
            |  (forall x v, ⟦f⟧ v x -> (1,P) /v/ (1,vec_app v vec_zero) ->> (1+length P,vec_app v (x##vec_zero)))
            /\ (forall v, (1,P) /v/ (1,vec_app v vec_zero) ↓ -> ex (⟦f⟧ v)) } }.
  Proof.
    destruct ra_mm_env_simulator with (f := f) as (P & HP).
    set (k := max (S n) (mm_nat_bound P)).
    assert (S n <= k) as H3 by apply le_max_l.
    assert { m | k = n+S m } as H4.
    { exists (k-S n); lia. }
    clear H3.
    destruct H4 as (m & Hm).
    exists m.
    destruct mm_nat_pos with (n := k) (l := P) as (Q & HQ).
    + apply le_max_r.
    + revert Q HQ; rewrite Hm; clear k Hm; intros Q HQ.
      exists Q; split.
      * intros x v H.
        destruct (HP v (fun j => match le_lt_dec n j with left _ => 0 | right Hj => vec_pos v (nat2pos Hj) end))
          as [ H1 _ ].
        - intros p; generalize (pos2nat_prop p); intros H0; unfold get_env.
          destruct (le_lt_dec n (pos2nat p)); try lia.
          f_equal; apply nat2pos_pos2nat.
        - intros j Hj; unfold get_env.
          destruct (le_lt_dec n j); lia.
        - destruct (H1 _ H) as (e' & G1 & k & G2); auto.
          exists k.
          rewrite HQ in G2 at 1.
          apply sss_steps_mm_pos_nat_inv with (v1 := vec_app v vec_zero) in G2.
          ++ destruct G2 as (v2 & G2 & G3); simpl in G3.
             eq goal G3; do 2 f_equal.
             { rewrite HQ; unfold mm_pos_nat; rewrite map_length; auto. }
             apply vec_pos_ext, pos_left_right_rect.
             ** intros p; rewrite G2, vec_pos_app_left, G1; simpl.
                rewrite pos2nat_left.
                generalize (pos2nat_prop p); intros G4.
                rewrite get_set_env_neq; try lia.
                unfold get_env.
                destruct (le_lt_dec n (pos2nat p)); try lia.
                f_equal; apply nat2pos_pos2nat.
             ** intros p.
                rewrite vec_pos_app_right, G2, pos2nat_right; simpl snd.
                rewrite plus_comm.
                analyse pos p.
                -- rewrite pos2nat_fst; simpl.
                   rewrite G1; rew env.
                -- rewrite pos2nat_nxt; simpl.
                   unfold vec_zero; rewrite vec_pos_set.
                   rewrite G1, get_set_env_neq; try lia.
                   unfold get_env; simpl.
                   destruct (le_lt_dec n (S (pos2nat p+n))); lia.
          ++ simpl; apply pos_left_right_rect.
             ** intros p; rewrite vec_pos_app_left, pos2nat_left.
                unfold get_env.
                generalize (pos2nat_prop p); intros.
                destruct (le_lt_dec n (pos2nat p)); try lia; f_equal.
                rewrite nat2pos_pos2nat; auto.
             ** intros p; rewrite vec_pos_app_right, pos2nat_right.
                unfold vec_zero; rewrite vec_pos_set.
                unfold get_env.
                destruct (le_lt_dec n (n+pos2nat p)); try lia.
      * intros v ((j,w) & (k & G1) & G2); simpl in G2.
        set (e1 := fun j => match le_lt_dec n j with left _ => 0 | right Hj => vec_pos v (nat2pos Hj) end).
        apply sss_steps_mm_pos_nat with (e1 := e1) in G1.
        destruct G1 as (e2 & G1 & G3); simpl in G3.
        apply HP with e1.
        - intros p; unfold e1, get_env.
          generalize (pos2nat_prop p); intros.
          destruct (le_lt_dec n (pos2nat p)); try lia.
          rewrite nat2pos_pos2nat; auto.
        - intros p Hp.
          unfold e1, get_env.
          destruct (le_lt_dec n p); lia.
        - rewrite HQ; exists (j,e2); split.
          ++ exists k; auto.
          ++ simpl; unfold mm_pos_nat; rew length; auto.
        - simpl; apply pos_left_right_rect.
          ++ intros p; rewrite vec_pos_app_left, pos2nat_left.
             unfold e1, get_env.
             generalize (pos2nat_prop p); intros.
             destruct (le_lt_dec n (pos2nat p)); try lia.
             rewrite nat2pos_pos2nat; auto.
          ++ intros p; rewrite vec_pos_app_right, pos2nat_right, vec_zero_spec.
             unfold e1, get_env.
             destruct (le_lt_dec n (n+pos2nat p)); try lia.
  Qed.

End ra_mm_comp.
