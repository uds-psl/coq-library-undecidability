(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith Lia Relations.

From Undecidability.Shared.Libs.DLW 
  Require Import utils pos vec.

Set Implicit Arguments.

(** * Intuionistic Multiplicative Linear Logic with several exponentials *)

Local Infix "~p" := (@Permutation _) (at level 70).

(** We consider  IMSELL:
    - the (!^*,-o) fragment with or without cut
*)

Notation eimsell_vars := nat.

Inductive eimsell_cmd : Set :=
  | eimsell_cmd_stop  : eimsell_vars -> eimsell_cmd
  | eimsell_cmd_inc  : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd
  | eimsell_cmd_dec  : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd
  | eimsell_cmd_zero : bool -> eimsell_vars -> eimsell_vars -> eimsell_cmd.

Notation LL_STOP := eimsell_cmd_stop.
Notation LL_INC  := eimsell_cmd_inc.
Notation LL_DEC  := eimsell_cmd_dec.
Notation LL_ZERO := eimsell_cmd_zero.

Definition eimsell_cmd_vars c := 
  match c with
    | LL_STOP p     => p::nil
    | LL_INC  _ p q => p::q::nil
    | LL_DEC  _ p q => p::q::nil
    | LL_ZERO _ p q => p::q::nil
  end.

Section GeIMSELL.

  Reserved Notation "Σ ; a ⊕ b ⊦ u" (at level 70, no associativity).

  Inductive G_eimsell (Σ : list eimsell_cmd) : nat -> nat -> eimsell_vars -> Prop :=
    | in_geimsell_stop  : forall p,         In (LL_STOP p) Σ         ->  Σ; 0 ⊕ 0 ⊦ p

    | in_geimsell_inc_1 : forall a b p q,   In (LL_INC true p q) Σ   ->  Σ; 1+a ⊕ b  ⊦ p
                                                                     ->  Σ;   a ⊕ b  ⊦ q
    | in_geimsell_inc_0 : forall a b p q,   In (LL_INC false p q) Σ  ->  Σ; a ⊕ 1+b  ⊦ p
                                                                     ->  Σ; a ⊕ b    ⊦ q

    | in_geimsell_dec_1 : forall a b p q,   In (LL_DEC true p q) Σ   ->  Σ;   a ⊕ b  ⊦ p
                                                                     ->  Σ; 1+a ⊕ b  ⊦ q
    | in_geimsell_dec_0 : forall a b p q,   In (LL_DEC false p q) Σ  ->  Σ; a ⊕   b  ⊦ p
                                                                     ->  Σ; a ⊕ 1+b  ⊦ q

    | in_geimsell_zero_1 : forall b p q,    In (LL_ZERO true p q) Σ  ->  Σ;   0 ⊕ b  ⊦ p
                                                                     ->  Σ;   0 ⊕ b  ⊦ q
    | in_geimsell_zero_0 : forall a p q,    In (LL_ZERO false p q) Σ ->  Σ;   a ⊕ 0  ⊦ p
                                                                     ->  Σ;   a ⊕ 0  ⊦ q

  where "Σ ; a ⊕ b ⊦ u" := (G_eimsell Σ a b u).

End GeIMSELL.

Local Notation "Σ ; a ⊕ b ⊦e u" := (G_eimsell Σ a b u) (at level 70, no associativity).

Notation imsell_vars := nat.

From Undecidability.MinskyMachines Require Import MM2.

Section MM2_GeIMSEL.

  (* Encoding of MM2 termination on zero in G_eimsell *)

  Variable q : eimsell_vars -> nat.

  Definition mm2_instr_enc i ρ :=
    match ρ with
      | mm2_inc_a   => LL_INC true  (q (1+i)) (q i) :: nil
      | mm2_inc_b   => LL_INC false (q (1+i)) (q i) :: nil
      | mm2_dec_a j => LL_DEC true  (q j) (q i) :: LL_ZERO true  (q (1+i)) (q i) :: nil
      | mm2_dec_b j => LL_DEC false (q j) (q i) :: LL_ZERO false (q (1+i)) (q i) :: nil
    end.

  Fact mm2_instr_enc_sound Σ ρ s1 s2 : mm2_atom ρ s1 s2 ->
          match s1, s2 with (i,(a,b)), (j,(a',b')) =>
            incl (mm2_instr_enc i ρ) Σ -> G_eimsell Σ a' b' (q j) -> G_eimsell Σ a b (q i)
          end.
  Proof.
    induction 1 as [ i a b | i a b | i j a b | i j a b | i j b | i j a ]; simpl; intros HΣ H.
    + constructor 2 with (q (S i)); auto; apply HΣ; simpl; auto.
    + constructor 3 with (q (S i)); auto; apply HΣ; simpl; auto.
    + constructor 4 with (q j); auto; apply HΣ; simpl; auto.
    + constructor 5 with (q j); auto; apply HΣ; simpl; auto.
    + constructor 6 with (q (1+i)); auto; apply HΣ; simpl; auto.
    + constructor 7 with (q (1+i)); auto; apply HΣ; simpl; auto.
  Qed.

  Fixpoint mm2_linstr_enc i l :=
    match l with
      | nil => nil
      | ρ::l => mm2_instr_enc i ρ ++ mm2_linstr_enc (1+i) l
    end.

  Fact mm2_linstr_enc_app i l m : mm2_linstr_enc i (l++m) = mm2_linstr_enc i l ++ mm2_linstr_enc (length l+i) m.
  Proof.
    revert i; induction l as [ | ? l IHl ]; intros ?; simpl; auto.
    rewrite app_ass, IHl; do 3 f_equal; auto.
  Qed.

  Fact mm2_linstr_enc_In i P c : 
          In c (mm2_linstr_enc i P) 
       -> exists l r ρ, P = l++ρ::r /\ In c (mm2_instr_enc (length l+i) ρ).
  Proof.
    revert i; induction P as [ | ρ P IH ]; intros i.
    + intros [].
    + simpl; rewrite in_app_iff; intros [ H | H ].
      * exists nil, P, ρ; split; auto.
      * destruct (IH (1+i)) as (l & r & ρ' & H1 & H2); auto.
        exists (ρ::l), r, ρ'; split; auto.
        - simpl; f_equal; auto.
        - eq goal H2; do 2 f_equal; simpl; lia.
  Qed.

  Lemma mm2_step_linstr_sound Σ P s1 s2 : mm2_step P s1 s2 -> 
          match s1, s2 with (i,(a,b)), (j,(a',b')) =>
            incl (mm2_linstr_enc 1 P) Σ -> G_eimsell Σ a' b' (q j) -> G_eimsell Σ a b (q i)
          end.
  Proof.
    intros (ρ & (l&r&H1&H2) & H3).
    apply mm2_instr_enc_sound with (Σ := Σ) in H3; revert s1 s2 H2 H3.
    intros (i,(a,b)) (j,(a',b')); simpl; intros H2 H3 H4 H5.
    apply H3; auto.
    apply incl_tran with (2 := H4).
    rewrite H1, mm2_linstr_enc_app.
    apply incl_appr; simpl.
    apply incl_appl.
    rewrite <- H2, plus_comm.
    apply incl_refl.
  Qed.

  Variable P : list mm2_instr.

  Notation "x ↠ y" := (clos_refl_trans _ (mm2_step P) x y) (at level 70).

  Definition mm2_prog_enc := LL_STOP (q 0) :: mm2_linstr_enc 1 P.

  Notation Σ := mm2_prog_enc.

  Lemma mm2_prog_enc_compute s1 s2 : s1 ↠ s2 ->
          match s1, s2 with (i,(a,b)), (j,(a',b')) =>
             G_eimsell Σ a' b' (q j) -> G_eimsell Σ a b (q i)
          end.
  Proof.
    induction 1 as [ (?,(?,?)) (?,(?,?)) H
                   | (?,(?,?)) 
                   | (?,(?,?)) (?,(?,?)) (?,(?,?))  ]; eauto.
    apply mm2_step_linstr_sound with (Σ := Σ) in H.
    apply H, incl_tl, incl_refl.
  Qed.

  Lemma mm2_prog_enc_stop : G_eimsell Σ 0 0 (q 0).
  Proof. constructor 1; simpl; auto. Qed.

  Hint Resolve mm2_prog_enc_stop : core.

  Theorem mm2_prog_enc_correct a b : 
             MM2_HALTS_ON_ZERO (P,a,b) 
          -> G_eimsell Σ a b (q 1).
  Proof.
    intros H; apply mm2_prog_enc_compute in H; auto.
  Qed.

  Hypothesis Hq : forall u v, q u = q v -> u = v.

  Theorem mm2_prog_enc_complete a b p : 
             G_eimsell Σ a b p 
          -> forall i, p = q i 
          -> (i,(a,b)) ↠ (0,(0,0)).
  Proof.
    induction 1 as [ u H 
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | b p u H H1 IH1
                   | a p u H H1 IH1 ]; intros i Hi.
    + destruct H as [ H | H ]. 
      * inversion H.
        rewrite Hi in H1.
        apply Hq in H1 as <-.
        constructor 2.
      * apply mm2_linstr_enc_In in H
          as (l & r & [ | | | ] & H1 & H2); simpl in H2.
        1-2: now destruct H2.
        1-2: now destruct H2 as [ | [] ].
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      2: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (length l+2, (S a,b)).
      * constructor 1.
        exists mm2_inc_a; split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ].
      inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (length l+2, (a,S b)).
      * constructor 1.
        exists mm2_inc_b; split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (n, (a,b)).
      * constructor 1.
        exists (mm2_dec_a n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (n, (a,b)).
      * constructor 1.
        exists (mm2_dec_b n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (length l+2, (0,b)).
      * constructor 1.
        exists (mm2_dec_a n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2.
      rewrite Hi in H4; apply Hq in H4; subst i.
      constructor 3 with (length l+2, (a,0)).
      * constructor 1.
        exists (mm2_dec_b n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * apply IH1; subst; f_equal; lia.
  Qed.

  Theorem MM2_GeIMSELL_reduction a b : MM2_HALTS_ON_ZERO (P,a,b) <-> G_eimsell Σ a b (q 1).
  Proof.
    split.
    + apply mm2_prog_enc_correct.
    + intros H; now apply mm2_prog_enc_complete with (q 1).
  Qed.

End MM2_GeIMSEL.

Local Notation "X ⊆ Y" := (forall a, X a -> Y a : Prop) (at level 70).

Local Reserved Notation "'⟦' A '⟧'" (at level 65, format "⟦ A ⟧").
Local Reserved Notation "A ⊸ B" (at level 51, right associativity).
Local Reserved Notation "'![' u ']' x" (at level 52, format "![ u ] x").

Section IMSELL.

  Variable bang : Type.

  Inductive imsell_form : Type :=
    | imsell_var  : imsell_vars -> imsell_form
    | imsell_ban  : bang -> imsell_form -> imsell_form
    | imsell_imp  : imsell_form -> imsell_form -> imsell_form.

  (* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  !   ‼  ∅  ⊢ *)

  Infix "⊸" := imsell_imp.

  Notation "![ u ] x" := (imsell_ban u x).

  Notation "£" := imsell_var.

  Reserved Notation "‼ x" (at level 60, format "‼ x").
  Reserved Notation "l '⊢' x" (at level 70, no associativity).

  Fixpoint imsell_lban (l : list (bang * imsell_form)) : list imsell_form :=
    match l with 
      | nil      => nil
      | (u,A)::l => (![u] A)::‼l
    end
  where "'‼' l" := (imsell_lban l).

  Fact imsell_lban_map l : imsell_lban l = map (fun '(u,A) => ![u]A) l.
  Proof. induction l as [ | [] ]; simpl; f_equal; auto. Qed.

  Fact imsell_lban_perm Σ Γ : Σ ~p Γ -> ‼Σ ~p ‼Γ.
  Proof.
    induction 1 as [ | [] | [] [] | ]; simpl; auto.
    + constructor.
    + eapply perm_trans; eauto.
  Qed. 

  Variable (bang_le : bang -> bang -> Prop) (bang_U : bang -> Prop).

  Notation "u ≼ l" := (forall c, In c l -> bang_le u (fst c)) (at level 70). 

  Inductive S_imsell : _ -> _ -> Prop :=

    | in_imsell_ax     : forall A,                        A::nil ⊢ A

    | in_imsell_perm   : forall Γ Δ A,              Γ ~p Δ     ->   Γ ⊢ A 
                                           (*-----------------------------*)
                                        ->                 Δ ⊢ A

    | in_imsell_limp_l : forall Γ Δ A B C,         Γ ⊢ A      ->   B::Δ ⊢ C
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Δ ⊢ C

    | in_imsell_limp_r : forall Γ A B,                  A::Γ ⊢ B
                                           (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B

    | in_imsell_bang_l : forall u Γ A B,                 A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->           ![u]A::Γ ⊢ B

    | in_imsell_bang_r : forall u Γ A,            u ≼ Γ    ->     ‼Γ ⊢ A
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ ![u]A

    | in_imsell_weak : forall u Γ A B,          bang_U u    ->   Γ ⊢ B
                                           (*-----------------------------*)
                                      ->             ![u]A::Γ ⊢ B

    | in_imsell_cntr : forall u Γ A B,        bang_U u  -> ![u]A::![u]A::Γ ⊢ B
                                           (*-----------------------------*)
                                      ->               ![u]A::Γ ⊢ B

  where "Γ ⊢ A" := (S_imsell Γ A).

  Fact S_imsell_weak Γ Δ B : Forall (fun '(u,_) => bang_U u) Γ -> Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof. 
    intros H1 H2; revert H1. 
    induction 1 as [ | (u,A) Γ H1 IH1 ]; simpl; auto.
    apply in_imsell_weak; auto. 
  Qed.

  Fact S_imsell_cntr Γ Δ B : Forall (fun '(u,_) => bang_U u) Γ -> ‼Γ++‼Γ++Δ ⊢ B -> ‼Γ++Δ ⊢ B.
  Proof.
    intros H; revert H Δ.
    induction 1 as [ | (u,A) Γ H1 H2 IH2 ]; simpl; auto; intros Δ H.
    apply in_imsell_cntr; auto.
    apply in_imsell_perm with (‼Γ ++ (![u]A::![u]A::Δ)).
    + apply Permutation_sym.
      do 2 apply Permutation_cons_app; auto.
    + apply IH2.
      revert H; apply in_imsell_perm.
      rewrite app_assoc.
      apply Permutation_cons_app.
      rewrite <- app_assoc.
      apply Permutation_app; auto.
      apply Permutation_cons_app; auto.
  Qed.

  Theorem S_imsell_weak_cntr Σ Γ u A B : In (u,A) Σ -> bang_U u -> ‼Σ++Γ ⊢ B <-> ![u]A::‼Σ++Γ ⊢ B.
  Proof.
    intros H H1; apply In_perm in H as (Σ' & H).
    split.
    + apply in_imsell_weak; auto.
    + intros H2.
      apply in_imsell_perm with (‼((u,A) :: Σ') ++ Γ).
      * apply Permutation_app; auto.
        apply imsell_lban_perm; auto.
      * simpl; apply in_imsell_cntr; auto.
        revert H2; apply in_imsell_perm.
        simpl; apply Permutation_cons; auto.
        change (![u]A::‼Σ'++Γ) with (‼((u,A)::Σ')++Γ).
        apply Permutation_app; auto.
        apply imsell_lban_perm, Permutation_sym; auto.
  Qed.

  Variable (a b i : bang).

  Notation "∞" := i. 

  Hypothesis (Hai : bang_le a ∞) (Hbi : bang_le b ∞) (Hi : bang_U ∞) (Hbang : forall x, bang_le x x).

  Definition bool2form x := 
    match x with 
      | true  => ![a]£0
      | false => ![b]£1
    end.

  Definition bool2bang_op x :=
    match x with 
      | true  => b
      | false => a
    end.

  Definition eimsell_map_imsell c :=
  match c with
    | LL_STOP p     => (£(2+p) ⊸ £(2+p)) ⊸ £(2+p) 
    | LL_INC  x p q => (bool2form x ⊸ £(2+p)) ⊸ £(2+q)
    | LL_DEC  x p q => bool2form x ⊸ £(2+p) ⊸ £(2+q)
    | LL_ZERO x p q  => (![bool2bang_op x]£(2+p)) ⊸ £(2+q)
  end.

  Check repeat.

  Definition eimsell_imsell Σ x y := map (fun c => ![∞](eimsell_map_imsell c)) Σ ++ repeat (![a]£0) x ++ repeat (![b]£1) y. 

  Fact eimsell_map_imsell_eq Σ :  map (fun c => ![∞](eimsell_map_imsell c)) Σ
                            = ‼(map (fun c => (∞,eimsell_map_imsell c)) Σ).
  Proof. induction Σ; simpl; f_equal; auto. Qed.

  Fact eimsell_map_imsell_eq2 Σ x y :  eimsell_imsell Σ x y
                            = ‼(map (fun c => (∞,eimsell_map_imsell c)) Σ ++ repeat (a,£0) x ++ repeat (b,£1) y).
  Proof.
    unfold eimsell_imsell.
    rewrite imsell_lban_map, !map_app, map_map; f_equal.
    induction x; simpl; f_equal; auto.
    induction y; simpl; f_equal; auto.
  Qed.

  Theorem G_eimsell_weak c Σ x y u :
            In c Σ
        ->  eimsell_imsell Σ x y ⊢ £u 
       <-> ![∞](eimsell_map_imsell c)::eimsell_imsell Σ x y ++ nil ⊢ £u.
  Proof.
    intros H; rewrite <- app_nil_end.
    unfold eimsell_imsell.
    rewrite !eimsell_map_imsell_eq.
    apply S_imsell_weak_cntr with (u := ∞) (A := eimsell_map_imsell c); auto.
    apply in_map_iff; eauto.
  Qed.

  Theorem G_eimsell_sound Σ x y u : Σ ; x ⊕ y ⊦e u -> eimsell_imsell Σ x y ⊢ £(2+u) .
  Proof.
    induction 1 as [ p H1 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2 
                   | x y p q H1 H2 IH2 | x y p q H1 H2 IH2
                   | y p q H1 H2 IH2 | x p q H1 H2 IH2 ].
    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        apply in_imsell_perm with (1 := Permutation_sym (Permutation_cons_append _ _)).
        unfold eimsell_imsell.
        rewrite eimsell_map_imsell_eq; simpl; rewrite <- app_nil_end.
        apply S_imsell_weak.
        - apply Forall_forall; intros ?; rewrite in_map_iff.
          intros (? & <- & ?); auto.
        - apply in_imsell_ax.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold eimsell_imsell.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite app_ass.
      * apply in_imsell_ax.
    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l, in_imsell_limp_l.
      * apply in_imsell_limp_r.
        revert IH2; apply in_imsell_perm.
        unfold eimsell_imsell.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        rewrite !app_ass; repeat apply Permutation_app; auto.
        simpl; apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![a]£0) ⊸ £(2+p) ⊸ £(2+q) :: (![a]£0 :: nil) ++ eimsell_imsell Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold eimsell_imsell; simpl; rewrite !app_ass.
        apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _).
        now rewrite !app_ass.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := eimsell_imsell Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_perm with (Γ := (![b]£1) ⊸ £(2+p) ⊸ £(2+q) :: (![b]£1 :: nil) ++ eimsell_imsell Σ x y).
      * apply perm_skip; rewrite <- app_nil_end.
        simpl; apply perm_trans with (1 := Permutation_cons_append _ _).
        unfold eimsell_imsell; simpl; rewrite !app_ass.
        repeat apply Permutation_app; auto.
        apply Permutation_sym, perm_trans with (1 := Permutation_cons_append _ _); auto.
      * apply in_imsell_limp_l.
        - apply in_imsell_ax.
        - rewrite app_nil_end with (l := eimsell_imsell Σ x y).
          apply in_imsell_limp_l; auto.
          apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_limp_l.
      * rewrite eimsell_map_imsell_eq2.
        apply in_imsell_bang_r.
        - intros z; simpl; rewrite !in_app_iff, in_map_iff.
          intros [ (c & <- & Hc) | H ]; simpl; auto.
          apply repeat_spec in H as ->; simpl; auto.
        - now rewrite eimsell_map_imsell_eq2 in IH2.
      * apply in_imsell_ax.

    + apply G_eimsell_weak with (1 := H1); simpl.
      apply in_imsell_bang_l.
      apply in_imsell_limp_l.
      * rewrite eimsell_map_imsell_eq2.
        apply in_imsell_bang_r.
        - intros z; simpl; rewrite !in_app_iff, in_map_iff.
          intros [ (c & <- & Hc) | [ H | [] ] ]; simpl; auto.
          apply repeat_spec in H as ->; simpl; auto.
        - now rewrite eimsell_map_imsell_eq2 in IH2.
      * apply in_imsell_ax.
  Qed.

  Section sem.

  Variables (n : nat) (s : imsell_vars -> vec nat n -> Prop)
            (K : bang -> vec nat n -> Prop).

  Hypothesis HK_le : forall u v, bang_le u v -> K v ⊆ K u.

  Notation ø := vec_zero.

  Definition imsell_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
  Definition imsell_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b.
 
  Infix "**" := imsell_tps_mult (at level 65, right associativity).
  Infix "-*" := imsell_tps_imp (at level 65, right associativity).

  Fact imsell_tps_imp_zero X Y : (X -* Y) ø <-> X ⊆ Y.
  Proof.
    split.
    + intros ? ? ?; rewrite <- vec_zero_plus, vec_plus_comm; auto.
    + intros ? ?; rewrite vec_plus_comm, vec_zero_plus; auto.
  Qed.

  Hypothesis HK_unit0 : forall u, K u ø.
  Hypothesis HK_plus  : forall u, (K u)**(K u) ⊆ K u.
  Hypothesis HK_unit1 : forall u, bang_U u -> forall x, K u x -> x = ø.

  Fact imsell_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : 
             X1 ⊆ X2 -> Y1 ⊆ Y2 -> X1**Y1 ⊆ X2**Y2.
  Proof.
    intros H1 H2 x (y & z & H3 & H4 & H5); subst.
    exists y, z; auto.
  Qed.

  Fixpoint imsell_tps A x : Prop :=
    match A with
      | £ X     => s X x
      | ![u]A   => ⟦A⟧ x /\ K u x
      | A ⊸ B   => (⟦A⟧ -* ⟦B⟧) x
    end
  where "⟦ A ⟧" := (imsell_tps A).

  Fact imsell_tps_bang_zero u A : ⟦![u]A⟧ ø <-> ⟦A⟧ ø.
  Proof. simpl; split; auto; tauto. Qed.

  Fact imsell_tps_bang_U u A : bang_U u -> (forall v, ⟦![u]A⟧ v <-> v = ø) <-> ⟦A⟧ ø.
  Proof.
    intros Hu; split.
    + intros H; rewrite <- imsell_tps_bang_zero, H; auto.
    + intros H v; split; simpl.
      * intros (_ & H1); revert H1; eauto.
      * intros ->; auto.
  Qed.

  Reserved Notation "⟪ Γ ⟫" (at level 0, format "⟪ Γ ⟫").

  Fixpoint imsell_tps_list Γ :=
    match Γ with
      | nil  => eq vec_zero
      | A::Γ => ⟦A⟧ ** ⟪Γ⟫
    end
  where "⟪ Γ ⟫" := (imsell_tps_list Γ).

  Fact imsell_tps_app Γ Δ x : ⟪Γ++Δ⟫ x <-> (⟪Γ⟫**⟪Δ⟫) x.
  Proof.
    revert Γ Δ x; intros Ga De.
    induction Ga as [ | A Ga IH ]; intros x; simpl; split; intros Hx.
    + exists vec_zero, x; simpl; rew vec.
    + destruct Hx as (? & ? & H1 & H2 & H3); subst; auto; rewrite vec_zero_plus; auto.
    + destruct Hx as (y & z & H1 & H2 & H3).
      apply IH in H3.
      destruct H3 as (c & d & H4 & H5 & H6).
      exists (vec_plus y c), d; split.
      * subst; apply vec_plus_assoc.
      * split; auto.
        exists y, c; auto.
    + destruct Hx as (y & d & H1 & H2 & H3).
      destruct H2 as (z & g & H2 & H4 & H5).
      exists z, (vec_plus g d); split.
      * subst; symmetry; apply vec_plus_assoc.
      * split; auto.
        apply IH.
        exists g, d; auto.
  Qed.

  Fact imsell_tps_list_zero Γ : (forall A, In A Γ -> ⟦A⟧ ø) -> ⟪Γ⟫ ø.
  Proof.
    induction Γ as [ | A Γ IH ]; simpl; auto; intros H.
    exists ø, ø; msplit 2; auto; now rewrite vec_zero_plus.
  Qed.

  Fact imsell_tps_lbang u Γ : u ≼ Γ -> ⟪‼Γ⟫ ⊆ K u.
  Proof.
    rewrite <- Forall_forall.
    induction 1 as [ | (v,A) Γ H1 H2 IH2 ]; intros x; simpl.
    + intros <-; auto.
    + intros (y & z & -> & (G1 & G2) & G3).
      apply HK_plus; exists y, z; msplit 2; auto.
      revert G2; apply HK_le; auto.
  Qed.

  Fact imsell_tps_perm Γ Δ : Γ ~p Δ -> ⟪Γ⟫ ⊆ ⟪Δ⟫.
  Proof.
    induction 1 as [ | A Ga De H IH | A B Ga | ]; simpl; auto.
    + intros x (y & z & H1 & H2 & H3).
      exists y, z; repeat split; auto.
    + intros x (y & z & H1 & H2 & c & d & H3 & H4 & H5).
      exists c, (vec_plus y d); split.
      * subst; rewrite (vec_plus_comm c), vec_plus_assoc, (vec_plus_comm c); auto.
      * split; auto.
        exists y, d; auto.
  Qed.
  
  Definition imsell_sequent_tps Γ A := ⟪Γ⟫ -* ⟦A⟧.

  Notation "'[<' Γ '|-' A '>]'" := (imsell_sequent_tps Γ A).

  Fact imsell_sequent_tps_mono Γ A B :
         ⟦A⟧ ⊆ ⟦B⟧ -> [< Γ |- A >] ⊆ [< Γ |- B >].
  Proof.
    intros H x; simpl; unfold imsell_sequent_tps.
    intros H1 ? H2.
    apply H, H1; auto.
  Qed.

  Fact imsell_perm_tps Γ Δ : Γ ~p Δ -> forall A, [< Γ |- A >] ⊆ [< Δ |- A >].
  Proof.
    intros H1 B x; unfold imsell_sequent_tps.
    intros H2 ? H3.
    apply H2; revert H3. 
    apply imsell_tps_perm, Permutation_sym; auto.
  Qed.

  Fact imsell_sequent_tps_eq Γ A : [< Γ |- A >] vec_zero <-> ⟪Γ⟫ ⊆ ⟦A⟧.
  Proof.
    split.
    * intros H x Hx.
      rewrite <- vec_zero_plus, vec_plus_comm.
      apply (H x); trivial.
    * intros H x Hx.
      rewrite vec_plus_comm, vec_zero_plus; auto.
  Qed.

  Theorem imsell_tps_sound Γ A : Γ ⊢ A -> [< Γ |- A >] vec_zero.
  Proof.
    induction 1 as [ A 
                   | Γ Δ A H1 H2 IH2
                   | Γ Δ A B C H1 IH1 H2 IH2
                   | Γ A B H1 IH1
                   | u Γ A B H1 IH1
                   | u Γ A H1 H2 IH2
                   | u Γ A B H1 H2 IH2
                   | u Γ A B H1 H2 IH2
                   ]; unfold imsell_sequent_tps in * |- *.

    + intros x; simpl; intros (y & z & H1 & H2 & H3); subst; eq goal H2.
      f_equal; do 2 rewrite vec_plus_comm, vec_zero_plus; auto.

    + revert IH2; apply imsell_perm_tps; auto.

    + intros x (y & z & H3 & H4 & H5); simpl.
      apply IH2.
      apply imsell_tps_app in H5 as (g & d & H5 & H6 & H7).
      simpl in H4.
      apply IH1, H4 in H6.
      exists (vec_plus y g), d; repeat split; auto.
      * subst; apply vec_plus_assoc.
      * eq goal H6; f_equal; rew vec.

    + simpl; intros y Hy x Hx.
      rewrite vec_plus_assoc.
      apply IH1.
      exists x, y; repeat split; auto; lia.

    + intros x (y & z & H2 & H3 & H4).
      apply IH1; exists y, z; repeat split; auto.
      apply H3.

    + intros x Hx; split.
      * apply IH2; auto.
      * rew vec.
        revert Hx; apply imsell_tps_lbang; auto. 

    + intros x (y & z & -> & H3 & H4); rew vec.
      apply proj2, HK_unit1 in H3; auto; subst.
      rewrite vec_plus_comm.
      now apply IH2.
  
    + intros x (y & z & G2 & G3 & G4).
      apply IH2.
      exists y, z; repeat (split; auto).
      exists y, z; repeat (split; auto).
      apply proj2, HK_unit1 in G3; auto.
      subst; rew vec; auto.
  Qed.

  End sem.

End IMSELL.

Section completeness.

    Notation ø := vec_zero.

    Variable Σ : list eimsell_cmd.

    Let bang := option bool.

    Let a := Some true.
    Let b := Some false.
    Let i : bang := None.

    Notation "∞" := i. 

    Let bang_le (u v : bang) := 
      match v with
        | None   => True
        | Some _ => u = v
      end.

    Let bang_U := eq ∞.

    Local Definition Hai : bang_le a ∞ := I.
    Local Definition Hbi : bang_le b ∞ := I. 
    Local Definition Hi : bang_U ∞ := eq_refl.
    Local Fact Hbang : forall x, bang_le x x.
    Proof. intros [ [] | ]; simpl; auto. Qed. 

    Let K (u : bang) (v : vec nat 2) := 
      let x := vec_head v in
      let y := vec_head (vec_tail v) in
        match u with 
          | None       => x = 0 /\ y = 0
          | Some true  => y = 0
          | Some false => x = 0
        end. 

    Tactic Notation "pair" "split" hyp(v) "as" ident(x) ident(y) :=
      vec split v with x; vec split v with y; vec nil v; clear v.

    Local Fact HK1 u v : bang_le u v -> K v ⊆ K u.
    Proof.
      intros Huv w; pair split w as x y.
      revert u v Huv; intros [[]|] [[]|]; simpl; try discriminate; tauto.
    Qed.

    Local Fact HK2 : forall u, K u ø.
    Proof. intros [[]|]; simpl; auto. Qed.

    Local Fact pair_plus x1 y1 x2 y2 : vec_plus (x1##y1##vec_nil) (x2##y2##vec_nil) = (x1+x2)##(y1+y2)##vec_nil.
    Proof. reflexivity. Qed.

    Local Fact HK3 u w : imsell_tps_mult (K u) (K u) w -> K u w.
    Proof.
      pair split w as x y.
      revert u; intros [[]|]; simpl; 
        intros (u & v & H1 & H2 & H3);
        simpl in H2, H3; revert H1 H2 H3;
        pair split u as x1 y1; pair split v as x2 y2; simpl;
        rewrite pair_plus; inversion 1; lia.
    Qed.

    Local Fact HK4 u : bang_U u -> forall w, K u w -> w = ø.
    Proof. 
      revert u; intros [[]|]; simpl; try discriminate.
      intros _ w; pair split w as x y; simpl.
      intros (-> & ->); auto.
    Qed.
 
    Check imsell_tps_sound.

    Let sem u (v : vec nat 2) := 
      let x := vec_head v in
      let y := vec_head (vec_tail v) in
        match u with
          | 0 => x = 1 /\ y = 0
          | 1 => x = 0 /\ y = 1
          | S (S i) => Σ ; x ⊕ y ⊦e i
        end.

    Local Fact sem_0 x y : sem 0 (x##y##vec_nil) <-> x = 1 /\ y = 0.
    Proof. simpl; tauto. Qed.
 
    Local Fact sem_1 x y : sem 1 (x##y##vec_nil) <-> x = 0 /\ y = 1.
    Proof. simpl; tauto. Qed.

    Local Fact sem_2 u x y : sem (2+u) (x##y##vec_nil) <-> Σ ; x ⊕ y ⊦e u.
    Proof. simpl; tauto. Qed.

    Infix "⊸" := imsell_imp.

    Notation "![ u ] x" := (imsell_ban u x).

    Notation "£" := imsell_var.

    Notation "⟦ A ⟧" := (imsell_tps sem K A).
    Notation "⟪ Γ ⟫" := (imsell_tps_list sem K Γ).

    Tactic Notation "intro" "pair" "as" ident(x) ident (y) :=
       let v := fresh in intro v; pair split v as x y.

    Check mm2_instr_enc.

    Local Lemma sem_Σ  c : In c Σ -> ⟦eimsell_map_imsell a b c⟧ ø.
    Proof.
      intros H.
      destruct c as [ p | [] p q | [] p q | [] p q ]; simpl; 
        apply imsell_tps_imp_zero; intro pair as x y; simpl; intros H1.
      + specialize (H1 ø); rewrite vec_zero_plus in H1.
        apply H1; constructor; auto.
      + constructor 2 with (1 := H).
        apply (H1 (1##0##vec_nil)); auto.
      + constructor 3 with (1 := H).
        apply (H1 (0##1##vec_nil)); auto.
      + destruct H1 as ((-> & ->) & _); simpl.
        intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
        constructor 4 with p; auto.
      + destruct H1 as ((-> & ->) & _); simpl.
        intro pair as x y; simpl; rewrite (plus_comm x), (plus_comm y).
        constructor 5 with p; auto.
      + destruct H1 as (H1 & ->).
        constructor 6 with p; auto.
      + destruct H1 as (H1 & ->).
        constructor 7 with p; auto.
    Qed.

    Hint Resolve HK1 HK2 HK3 HK4 sem_Σ : core.

    Local Fact sem_Σ_zero : ⟪map (fun c => ![∞](eimsell_map_imsell a b c)) Σ⟫ ø.
    Proof.
      apply imsell_tps_list_zero.
      intros A; rewrite in_map_iff.
      intros (c & <- & Hc); simpl; auto. 
    Qed.

    Section completeness.

      Variable (x y : nat).
      Hypothesis Hxy : S_imsell bang_le bang_U (eimsell_imsell a b ∞ Σ x y) (imsell_var _ 3).

      Theorem completeness : Σ ; x ⊕ y ⊦e 1.
      Proof.
        apply imsell_tps_sound with (s := sem) (K := K) in Hxy; eauto.
        specialize (Hxy (x##y##vec_nil)).
        rewrite vec_plus_comm, vec_zero_plus in Hxy.
        apply Hxy.
        unfold eimsell_imsell.
        apply imsell_tps_app.
        exists ø, (x##y##vec_nil).
        rewrite vec_zero_plus; msplit 2; auto.
        + apply sem_Σ_zero; auto.
        + apply imsell_tps_app.
          clear Hxy.
          exists (x##0##vec_nil), (0##y##vec_nil); msplit 2; auto.
          * rewrite pair_plus; f_equal; lia.
          * generalize x; clear x y; intros n. 
            induction n as [ | n IHn ]; simpl; auto.
            exists (1##0##vec_nil), (n##0##vec_nil); auto.
          * generalize y; clear x y; intros n. 
            induction n as [ | n IHn ]; simpl; auto.
            exists (0##1##vec_nil), (0##n##vec_nil); auto.
      Qed.

   End completeness.

   Hint Resolve Hai Hbi Hi Hbang : core.

   Theorem reduction x y : Σ ; x ⊕ y ⊦e 1 <-> S_imsell bang_le bang_U (eimsell_imsell a b ∞ Σ x y) (imsell_var _ 3).
   Proof.
     split.
     + intros; apply G_eimsell_sound; eauto.
     + apply completeness.
   Qed.

End completeness.


Section completeness.

    Notation ø := vec_zero.

    Variable P : list mm2_instr.

    Notation "x ↠ y" := (clos_refl_trans _ (mm2_step P) x y) (at level 70).

    Let Σ := mm2_prog_enc (fun i => 2+i) P.

    Let bang := option bool.

    Let a := Some true.
    Let b := Some false.
    Let i : bang := None.

    Notation "∞" := i. 

    Let bang_le (u v : bang) := 
      match v with
        | None   => True
        | Some _ => u = v
      end.

    Let bang_U := eq ∞.

    Local Definition Hai : bang_le a ∞ := I.
    Local Definition Hbi : bang_le b ∞ := I. 
    Local Definition Hi : bang_U ∞ := eq_refl.
    Local Fact Hbang : forall x, bang_le x x.
    Proof. intros [ [] | ]; simpl; auto. Qed. 

    Let K (u : bang) (v : vec nat 2) := 
      let x := vec_head v in
      let y := vec_head (vec_tail v) in
        match u with 
          | None       => x = 0 /\ y = 0
          | Some true  => y = 0
          | Some false => x = 0
        end. 

    Tactic Notation "pair" "split" hyp(v) "as" ident(x) ident(y) :=
      vec split v with x; vec split v with y; vec nil v; clear v.

    Local Fact HK1 u v : bang_le u v -> K v ⊆ K u.
    Proof.
      intros Huv w; pair split w as x y.
      revert u v Huv; intros [[]|] [[]|]; simpl; try discriminate; tauto.
    Qed.

    Local Fact HK2 : forall u, K u ø.
    Proof. intros [[]|]; simpl; auto. Qed.

    Local Fact pair_plus x1 y1 x2 y2 : vec_plus (x1##y1##vec_nil) (x2##y2##vec_nil) = (x1+x2)##(y1+y2)##vec_nil.
    Proof. reflexivity. Qed.

    Local Fact HK3 u w : imsell_tps_mult (K u) (K u) w -> K u w.
    Proof.
      pair split w as x y.
      revert u; intros [[]|]; simpl; 
        intros (u & v & H1 & H2 & H3);
        simpl in H2, H3; revert H1 H2 H3;
        pair split u as x1 y1; pair split v as x2 y2; simpl;
        rewrite pair_plus; inversion 1; lia.
    Qed.

    Local Fact HK4 u : bang_U u -> forall w, K u w -> w = ø.
    Proof. 
      revert u; intros [[]|]; simpl; try discriminate.
      intros _ w; pair split w as x y; simpl.
      intros (-> & ->); auto.
    Qed.
 
    Check imsell_tps_sound.

    Let sem u (v : vec nat 2) := 
      let x := vec_head v in
      let y := vec_head (vec_tail v) in
        match u with
          | 0 => x = 1 /\ y = 0
          | 1 => x = 0 /\ y = 1
          | S (S i) => (i,(x,y)) ↠ (0,(0,0)) 
        end.

    Local Fact sem_0 x y : sem 0 (x##y##vec_nil) <-> x = 1 /\ y = 0.
    Proof. simpl; tauto. Qed.
 
    Local Fact sem_1 x y : sem 1 (x##y##vec_nil) <-> x = 0 /\ y = 1.
    Proof. simpl; tauto. Qed.

    Local Fact sem_2 u x y : sem (2+u) (x##y##vec_nil) <-> (u,(x,y)) ↠ (0,(0,0)).
    Proof. simpl; tauto. Qed.

    Infix "⊸" := imsell_imp.

    Notation "![ u ] x" := (imsell_ban u x).

    Notation "£" := imsell_var.

    Notation "⟦ A ⟧" := (imsell_tps sem K A).
    Notation "⟪ Γ ⟫" := (imsell_tps_list sem K Γ).

    Tactic Notation "intro" "pair" "as" ident(x) ident (y) :=
       let v := fresh in intro v; pair split v as x y.

    Check mm2_instr_enc.

    Local Fact sem_at_2 : ⟦eimsell_map_imsell a b (LL_STOP 2)⟧ ø.
    Proof.
      simpl; apply imsell_tps_imp_zero.
      intro pair as x y; simpl; intros H.
      apply (H ø); simpl; constructor 2.
    Qed.

    Local Fact sem_at ρ j c : mm2_instr_at ρ j P
                        -> In c (mm2_instr_enc (fun j => 2+j) j ρ) 
                        -> ⟦eimsell_map_imsell a b c⟧ ø.
    Proof.
      destruct ρ as [ | | q | q ]; simpl; intros H1.
      + intros [ <- | [] ].
        simpl; apply imsell_tps_imp_zero.
        intro pair as x y; simpl; intros H.
        specialize (H (1##0##vec_nil)); simpl in H.
        constructor 3 with (S j,(S x,y)). 
        * constructor 1.
          exists mm2_inc_a; split; auto.
          constructor.
        * apply H; auto.
      + intros [ <- | [] ].
        simpl; apply imsell_tps_imp_zero.
        intro pair as x y; simpl; intros H.
        specialize (H (0##1##vec_nil)); simpl in H.
        constructor 3 with (S j,(x,S y)). 
        * constructor 1.
          exists mm2_inc_b; split; auto.
          constructor.
        * apply H; auto.
      + intros [ <- | [ <- | [] ] ].
        * simpl; apply imsell_tps_imp_zero.
          intro pair as x y; simpl. 
          intros ((-> & ->) & _); simpl.
          intro pair as x y; simpl; intros H.
          do 2 (rewrite plus_comm; simpl).
          constructor 3 with (2 := H). 
          constructor 1.
          exists (mm2_dec_a q); split; auto.
          constructor.
        * simpl; apply imsell_tps_imp_zero.
          intro pair as x y; simpl. 
          intros (H & ->); simpl.
          constructor 3 with (2 := H). 
          constructor 1.
          exists (mm2_dec_a q); split; auto.
          constructor.
      + intros [ <- | [ <- | [] ] ].
        * simpl; apply imsell_tps_imp_zero.
          intro pair as x y; simpl. 
          intros ((-> & ->) & _); simpl.
          intro pair as x y; simpl; intros H.
          do 2 (rewrite plus_comm; simpl).
          constructor 3 with (2 := H). 
          constructor 1.
          exists (mm2_dec_b q); split; auto.
          constructor.
        * simpl; apply imsell_tps_imp_zero.
          intro pair as x y; simpl. 
          intros (H & ->); simpl.
          constructor 3 with (2 := H). 
          constructor 1.
          exists (mm2_dec_b q); split; auto.
          constructor.
    Qed.

    Local Lemma sem_Σ c : In c Σ -> ⟦eimsell_map_imsell a b c⟧ ø.
    Proof.
      unfold Σ, mm2_prog_enc; intros [ <- | H ].
      + apply sem_at_2.
      + apply mm2_linstr_enc_In in H.
        destruct H as (l & r & ρ & H1 & H2).
        apply sem_at with (2 := H2).
        exists l, r; split; auto; lia.
    Qed.

    Check Σ.

    Hint Resolve HK1 HK2 HK3 HK4 sem_Σ : core.

    Local Fact sem_Σ_zero x : ⟪map (fun c => ![∞](eimsell_map_imsell a b c)) Σ⟫ x <-> x = ø.
    Proof.
      apply imsell_tps_list_zero.
      intros A; rewrite in_map_iff.
      intros (c & <- & Hc).
      rewrite imsell_tps_bang_U with (bang_U := bang_U); eauto.
      reflexivity.
    Qed.

    Section completeness.

      Variable (x y : nat).
      Hypothesis Hxy : S_imsell bang_le bang_U (eimsell_imsell a b ∞ Σ x y) (imsell_var _ 3).

      Theorem completeness : MM2_HALTS_ON_ZERO (P,x,y).
      Proof.
        apply imsell_tps_sound with (s := sem) (K := K) in Hxy; eauto.
        specialize (Hxy (x##y##vec_nil)).
        rewrite vec_plus_comm, vec_zero_plus in Hxy.
        apply Hxy.
        unfold eimsell_imsell.
        apply imsell_tps_app.
        exists ø, (x##y##vec_nil).
        rewrite vec_zero_plus; msplit 2; auto.
        + apply sem_Σ_zero; auto.
        + apply imsell_tps_app.
          clear Hxy.
          exists (x##0##vec_nil), (0##y##vec_nil); msplit 2; auto.
          * rewrite pair_plus; f_equal; lia.
          * generalize x; clear x y; intros n. 
            induction n as [ | n IHn ]; simpl; auto.
            exists (1##0##vec_nil), (n##0##vec_nil); auto.
          * generalize y; clear x y; intros n. 
            induction n as [ | n IHn ]; simpl; auto.
            exists (0##1##vec_nil), (0##n##vec_nil); auto.
      Qed.

   End completeness.

   Hint Resolve Hai Hbi Hi Hbang : core.

   Theorem reduction x y : MM2_HALTS_ON_ZERO (P,x,y) <-> S_imsell bang_le bang_U (eimsell_imsell a b ∞ Σ x y) (imsell_var _ 3).
   Proof.
     split.
     + intros; apply G_eimsell_sound; eauto.
       apply mm2_prog_enc_correct; auto.
     + apply completeness.
   Qed.

End completeness.

Check reduction.



    


