(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

From Undecidability.Shared.Libs.DLW 
  Require Import utils.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

(* Small inversion lemma *)

Fact app_eq_single_inv X (l m : list X) x :
       l++m = x::nil 
    -> l = nil /\ m = x::nil 
    \/ l = x::nil /\ m = nil.
Proof.
  intros H.
  destruct l as [ | y l ]; auto.
  right.
  inversion H.
  destruct l; destruct m; auto; discriminate.
Qed.

Tactic Notation "app" "inv" "singleton" "in" hyp(H) :=
  apply app_eq_single_inv in H as [ (-> & ->) | (-> & ->) ].

Tactic Notation "app" "inv" "nil" "in" hyp(H) :=
  apply app_eq_nil in H as (-> & ->).

(** * Classical Linear Logic vs Intuitionnisitc Linear Logic 

       derived from the work of H. Schellinx JLC 91 *)

Local Infix "~p" := (@Permutation _) (at level 70).

Inductive cll_connective := cll_with | cll_plus | cll_limp | cll_times | cll_par.
Inductive cll_constant := cll_1 | cll_0 | cll_bot | cll_top.
Inductive cll_modality := cll_bang | cll_qmrk | cll_neg.

Inductive cll_form : Set :=
  | cll_var  : ll_vars -> cll_form
  | cll_cst  : cll_constant  -> cll_form
  | cll_una  : cll_modality -> cll_form -> cll_form
  | cll_bin  : cll_connective -> cll_form -> cll_form -> cll_form.

Section mapping_ill_to_cll.

  (* Syntatic translations from/to ILL and CLL formulas *)

  Reserved Notation "[ f ]" (at level 1).
  Reserved Notation "⟨ f ⟩" (at level 1).

  Fixpoint ill_cll f :=
    match f with
      | £ v  => cll_var v
      | ⟘ => cll_cst cll_bot
      | ⟙ => cll_cst cll_top
      | 𝟙 => cll_cst cll_1
      | !f => cll_una cll_bang [f]
      | f⊗g => cll_bin cll_times [f] [g]
      | f&g => cll_bin cll_with [f] [g]
      | f⊕g => cll_bin cll_plus [f] [g]
      | f⊸g => cll_bin cll_limp [f] [g]
    end
  where "[ f ]" := (ill_cll f).

  Fixpoint cll_ill f :=
    match f with
      | cll_var v => £ v
      | cll_cst cll_bot => ⟘
      | cll_cst cll_top => ⟙
      | cll_cst cll_1 => 𝟙
      | cll_una cll_bang f => !⟨f⟩
      | cll_bin cll_times f g => ⟨f⟩ ⊗ ⟨g⟩
      | cll_bin cll_with  f g => ⟨f⟩ & ⟨g⟩
      | cll_bin cll_plus  f g => ⟨f⟩ ⊕ ⟨g⟩
      | cll_bin cll_limp  f g => ⟨f⟩ ⊸ ⟨g⟩
      | _ => ⟘  (* arbitrary value *)
    end
  where "⟨ f ⟩" := (cll_ill f).

  Fixpoint from_ill f := 
    match f with
      | cll_var _ => True
      | cll_cst cll_bot => True
      | cll_cst cll_top => True
      | cll_cst cll_1 => True
      | cll_una cll_bang f => from_ill f
      | cll_bin cll_times f g => from_ill f /\ from_ill g
      | cll_bin cll_with  f g => from_ill f /\ from_ill g
      | cll_bin cll_plus  f g => from_ill f /\ from_ill g
      | cll_bin cll_limp  f g => from_ill f /\ from_ill g
      | _ => False
    end.

  Fact ill_cll_ill f : ⟨[f]⟩ = f.
  Proof. induction f as [ | [] | | [] ]; simpl; f_equal; auto. Qed.

  Fact cll_ill_cll f : from_ill f -> [⟨f⟩] = f.
  Proof.
    induction f as [ | [] | [] | [] ]; simpl; try tauto; intros; f_equal; tauto.
  Qed.

  Fact ill_cll_from_ill f : from_ill [f].
  Proof. induction f as [ | [] | | [] ]; simpl; tauto. Qed. 

  Fixpoint cll_has_bot_zero_neg f := 
    match f with
      | cll_var _ => False
      | cll_cst c => c = cll_bot \/ c = cll_0
      | cll_una m f => m = cll_neg \/ cll_has_bot_zero_neg f
      | cll_bin _ f g => cll_has_bot_zero_neg f \/ cll_has_bot_zero_neg g
    end.

  Fixpoint ill_has_bot f := 
    match f with
      | ll_var _ => False
      | ll_zero ll_bot => True
      | ll_ban f => ill_has_bot f
      | ll_bin _ f g => ill_has_bot f \/ ill_has_bot g
      | _ => False
    end.

  Fact cll_ill_has_bot f : cll_has_bot_zero_neg f -> ill_has_bot ⟨f⟩.
  Proof. 
    induction f as  [ | [] | [] | [] ]; simpl; try tauto.
    all: intros []; auto; discriminate. 
  Qed.

  Fact ill_cll_has_bot f : ill_has_bot f -> cll_has_bot_zero_neg [f].
  Proof. induction f as [ | [] | | [] ]; simpl; tauto. Qed.

  Fact ill_cll_has_bot_eq f : ill_has_bot f <-> cll_has_bot_zero_neg [f].
  Proof.
    split.
    + apply ill_cll_has_bot.
    + intros H.
      apply cll_ill_has_bot in H.
      now rewrite ill_cll_ill in H.
  Qed.

End mapping_ill_to_cll.

(* Symbols for cut&paste ⟙   ⟘  𝟙 ﹠ ⊗  ⊕  ⊸ ! ‼ ‽ ⁇ ∅  ⊢ *)

(* These notations replace the ILL notations *)

(* Variables *)

Notation "'£' x" := (cll_var x) (at level 1).

(* Constants *)

Notation "⟙" := (cll_cst cll_top).
Notation "⟘" := (cll_cst cll_bot).
Notation "𝟙" := (cll_cst cll_1).
Notation "𝟘" := (cll_cst cll_0).

(* Unary connectives: linear negation and modalities *)
(* ? cannot be used because it is reserved by Coq so we use ‽ instead *)

Notation "'⊖' x" := (cll_una cll_neg x) (at level 50, format "⊖ x").
Notation "'!' x" := (cll_una cll_bang x) (at level 52).
Notation "'‽' x" := (cll_una cll_qmrk x) (at level 52).

(* Binary connectives *)

Infix "&" := (cll_bin cll_with) (at level 50).
Infix "⅋" := (cll_bin cll_par) (at level 50).
Infix "⊗" := (cll_bin cll_times) (at level 50).
Infix "⊕" := (cll_bin cll_plus) (at level 50).
Infix "⊸" := (cll_bin cll_limp) (at level 51, right associativity).

(* Modalities iterated over lists *)

Notation "‼ x" := (map (cll_una cll_bang) x) (at level 60).
Notation "⁇ x" := (map (cll_una cll_qmrk) x) (at level 60).

(* The empty list *)

Notation "∅" := nil.

(* Some basic commutativity lemmas for the ILL <-> CLL translations over lists *)

Notation "[ f ]" := (ill_cll f).
Notation "⟨ f ⟩" := (cll_ill f).

Notation "⟦ Γ ⟧" := (map ill_cll Γ).
Notation "⟪ Γ ⟫" := (map cll_ill Γ).

Local Hint Resolve ill_cll_ill : core.

Fact ill_cll_ill_list Γ : ⟪⟦Γ⟧⟫ = Γ.
Proof. induction Γ; simpl; f_equal; auto. Qed.

Fact ill_cll_lbang Γ : ⟦map ll_ban Γ⟧ = ‼⟦Γ⟧.
Proof. induction Γ; simpl; f_equal; auto. Qed.

Fact cll_ill_lbang Γ : ⟪‼Γ⟫ = map ll_ban ⟪Γ⟫.
Proof. induction Γ; simpl; f_equal; auto. Qed.

Section cut_free_cll.

  (* All the rules of Cut-free CLL *)

  Reserved Notation "Γ ⊢ Δ" (at level 70, no associativity).

  Inductive S_cll : list cll_form -> list cll_form -> Prop :=

    | in_cll_ax    : forall A,                         A::∅ ⊢ A::∅

(*
    | in_cll_cut   : forall Γ Δ Γ' Δ' A,        Γ ⊢ A::Δ    ->   A::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->           Γ++Γ' ⊢ Δ++Δ'
*)

    | in_cll_perm  : forall Γ Δ Γ' Δ',        Γ ~p Γ'  ->  Δ ~p Δ'  ->  Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->              Γ' ⊢ Δ'

    | in_cll_neg_l :   forall Γ Δ A,                    Γ ⊢ A::Δ
                                             (*-----------------------------*)
                                        ->          ⊖A::Γ ⊢ Δ

    | in_cll_neg_r :   forall Γ Δ A,                 A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->              Γ ⊢ ⊖A::Δ


    | in_cll_limp_l : forall Γ Δ Γ' Δ' A B,   Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->         A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll_limp_r : forall Γ Δ A B,                 A::Γ ⊢ B::Δ
                                             (*-----------------------------*)
                                        ->            Γ ⊢ A ⊸ B::Δ

    | in_cll_with_l1 : forall Γ Δ A B,                  A::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->           A&B::Γ ⊢ Δ

    | in_cll_with_l2 : forall Γ Δ A B,                  B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->           A&B::Γ ⊢ Δ
 
    | in_cll_with_r : forall Γ Δ A B,          Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A&B::Δ

    | in_cll_times_l : forall Γ A B Δ,               A::B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->            A⊗B::Γ ⊢ Δ
 
    | in_cll_times_r : forall Γ Δ Γ' Δ' A B,   Γ ⊢ A::Δ    ->   Γ' ⊢ B::Δ'
                                             (*-----------------------------*)
                                        ->         Γ++Γ' ⊢ A⊗B::Δ++Δ'

    | in_cll_par_l : forall Γ Δ Γ' Δ' A B,     A::Γ ⊢ Δ    ->   B::Γ' ⊢ Δ'
                                             (*-----------------------------*)
                                        ->         A⅋B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll_par_r : forall Γ A B Δ,                   Γ ⊢ A::B::Δ 
                                             (*-----------------------------*)
                                        ->             Γ ⊢ A⅋B::Δ

    | in_cll_plus_l :  forall Γ A B Δ,          A::Γ ⊢ Δ  ->  B::Γ ⊢ Δ 
                                             (*-----------------------------*)
                                        ->          A⊕B::Γ ⊢ Δ

    | in_cll_plus_r1 : forall Γ A B Δ,                  Γ ⊢ A::Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A⊕B::Δ

    | in_cll_plus_r2 : forall Γ A B Δ,                  Γ ⊢ B::Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ A⊕B::Δ

    | in_cll_bot_l : forall Γ Δ,                     ⟘::Γ ⊢ Δ

    | in_cll_top_r : forall Γ Δ,                        Γ ⊢ ⟙::Δ

    | in_cll_unit_l : forall Γ Δ,                       Γ ⊢ Δ  
                                             (*-----------------------------*)
                                        ->           𝟙::Γ ⊢ Δ

    | in_cll_unit_r :                                   ∅ ⊢ 𝟙::∅

    | in_cll_zero_l :                        (*-----------------------------*)
                                             (* *)      𝟘::∅ ⊢ ∅

    | in_cll_zero_r : forall Γ Δ,                       Γ ⊢ Δ  
                                             (*-----------------------------*)
                                        ->              Γ ⊢ 𝟘::Δ


    | in_cll_bang_l : forall Γ A Δ,                    A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->            !A::Γ ⊢ Δ

    | in_cll_bang_r : forall Γ A Δ,                     ‼Γ ⊢ A::⁇Δ
                                             (*-----------------------------*)
                                        ->              ‼Γ ⊢ !A::⁇Δ

    | in_cll_qmrk_l : forall Γ A Δ,                     A::‼Γ ⊢ ⁇Δ
                                             (*-----------------------------*)
                                        ->              ‽A::‼Γ ⊢ ⁇Δ

    | in_cll_qmrk_r : forall Γ A Δ,                    Γ ⊢ A::Δ
                                             (*-----------------------------*)
                                        ->             Γ ⊢ ‽A::Δ

    | in_cll_weak_l : forall Γ A Δ,                      Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->           !A::Γ ⊢ Δ

    | in_cll_weak_r : forall Γ A Δ,                      Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->               Γ ⊢ ‽A::Δ

    | in_cll_cntr_l : forall Γ A Δ,                !A::!A::Γ ⊢ Δ
                                             (*-----------------------------*)
                                        ->             !A::Γ ⊢ Δ

    | in_cll_cntr_r : forall Γ A Δ,                    Γ ⊢ ‽A::‽A::Δ
                                             (*-----------------------------*)
                                        ->             Γ ⊢ ‽A::Δ

  where "Γ ⊢ Δ" := (S_cll Γ Δ).

End cut_free_cll.

(* Γ ⊢i A stands for the sequent Γ ⊢ A is cut-free ILL provable *)
(* Γ ⊢c Δ stands for the sequent Γ ⊢ Δ is cut-free CLL provable *)

Notation "Γ '⊢i' A" := (S_ill Γ A) (at level 70, no associativity).
Notation "Γ '⊢c' Δ" := (S_cll Γ Δ) (at level 70, no associativity).

Section ill_cll_is_sound.

  Hint Resolve Permutation_map : core.

  Theorem ill_cll_soundness Γ A : Γ ⊢i A -> ⟦Γ⟧ ⊢c [A]::∅.
  Proof.
    induction 1; simpl in *.
    + apply in_cll_ax.
    + apply (@in_cll_perm ⟦Γ⟧ ([A]::nil)); auto.
    + rewrite map_app. 
      now apply in_cll_limp_l with (Δ := ∅) (Δ' := _::_).
    + now apply in_cll_limp_r with (Δ := ∅).
    + now apply in_cll_with_l1.
    + now apply in_cll_with_l2.
    + now apply in_cll_with_r with (Δ := ∅).
    + now apply in_cll_bang_l.
    + rewrite ill_cll_lbang in *.
      now apply in_cll_bang_r with (Δ := ∅).
    + now apply in_cll_weak_l.
    + now apply in_cll_cntr_l.
    + now apply in_cll_times_l.
    + rewrite map_app.
      now apply in_cll_times_r with (Δ := ∅) (Δ' := ∅).
    + now apply in_cll_plus_l.
    + now apply in_cll_plus_r1.
    + now apply in_cll_plus_r2.
    + apply in_cll_bot_l.
    + apply in_cll_top_r.
    + now apply in_cll_unit_l.
    + apply in_cll_unit_r.
  Qed.

End ill_cll_is_sound.

Section Schellinx_observation.

  (** This is an observation purely about cut-free CLL 

      One cannot get a cut-free CLL proof of Γ ⊢ ∅ 
      unless ⟘ or 𝟘 or a negation occurs in Γ *)

  Let schellinx_rec Γ Δ : 
               Γ ⊢c Δ 
            -> Δ = ∅ 
            -> exists f, In f Γ /\ cll_has_bot_zero_neg f.
  Proof.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ A H1 IH1 | Γ Δ A H1 IH1                              (* negation *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2             (* * *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ A B Δ H1 IH1             (* par *)
                   | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1  (* + *)
                   | |                                                        (* bot, top *)
                   | Γ Δ H1 IH1 |                                             (* unit *)
                   | |                                                        (* zero *) 
                   | Γ A Δ H1 IH1 | Γ A Δ H1 IH1                              (* bang *)
                   | Γ A Δ H1 IH1 |                                           (* qmrk *)
                   | Γ A Δ H1 IH1 |                                           (* weak *)
                   | Γ A Δ H1 IH1 | ];                                        (* cntr *)
              try discriminate.
    + intros ->.
      apply Permutation_sym, Permutation_nil in H2 as ->; auto.
      destruct IH3 as (f & G1 & G2); auto.
      exists f; split; auto.
      revert G1; now apply Permutation_in.
    + intros ->; exists (⊖A); simpl; auto.
    + intros H.
      app inv nil in H.
      destruct IH2 as (f & [ <- | ] & ?); auto.
      * exists (A ⊸ B); simpl; split; auto.
      * exists f; split; auto.
        right; apply in_or_app; tauto.
    + intros ->.
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (A&B); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (A&B); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & [ <- | [ <- | ] ] & ?); auto.
      * exists (A⊗B); simpl; auto.
      * exists (A⊗B); simpl; auto.
      * exists f; simpl; auto.
    + intros H.
      app inv nil in H.
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (A⅋B); simpl; auto.
      * exists f; simpl; split; auto.
        rewrite in_app_iff; auto.
    + intros ->. 
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (A⊕B); simpl; auto.
      * exists f; simpl; auto.
    + exists ⟘; simpl; auto.
    + intros ->.
      destruct IH1 as (f & ? & ?); auto.
      exists f; simpl; auto.
    + exists 𝟘; simpl; auto.
    + intros ->.
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (!A); simpl; auto.
      * exists f; simpl; auto.
    + destruct Δ; try discriminate; intros _ ; simpl in *.
      destruct IH1 as (f & [ <- | ] & ?); auto.
      * exists (‽A); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & ? & ?); auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & [ <- | [ <- | ] ] & ?); auto.
      * exists (!A); simpl; auto.
      * exists (!A); simpl; auto.
      * exists f; simpl; auto.
  Qed.

  Lemma Schellinx_observation Γ : 
          Γ ⊢c ∅ -> exists f, In f Γ /\ cll_has_bot_zero_neg f.
  Proof. intros; now apply schellinx_rec with (2 := eq_refl). Qed.

End Schellinx_observation.

Section cll_ill_soundness.

  (** If an ILL sequent Γ ⊢ A is cut-free CLL provable then 
     it is also cut-free ILL provable unless it contains ⟘ *)

  (* A handy tactic for Forall goals ... *)

  Tactic Notation "solve" "Forall" :=
    repeat rewrite Forall_cons_inv in *;
    repeat rewrite Forall_app in *; simpl in *; tauto.

  Let cll_ill_rec Γ Δ A : 
               Γ ⊢c Δ 
            -> Δ = A::∅ 
            -> Forall from_ill (A::Γ) 
            -> ⟪Γ⟫ ⊢i ⟨A⟩ 
            \/ cll_has_bot_zero_neg A 
            \/ exists f, In f Γ /\ cll_has_bot_zero_neg f.
  Proof.
    intros H; revert H A.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ A H1 IH1 | Γ Δ A H1 IH1                              (* negation *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2             (* * *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ A B Δ H1 IH1             (* par *)
                   | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1  (* + *)
                   | |                                                        (* bot, top *)
                   | Γ Δ H1 IH1 |                                             (* unit *)
                   | |                                                        (* zero *) 
                   | Γ A Δ H1 IH1 | Γ A Δ H1 IH1                              (* bang *)
                   | Γ A Δ H1 IH1 |                                           (* qmrk *)
                   | Γ A Δ H1 IH1 |                                           (* weak *)
                   | Γ A Δ H1 IH1 | ];                                        (* cntr *)
               intros C HΔ HΓ.
    + inversion HΔ; left; simpl; constructor.
    + subst.
      apply Permutation_sym, Permutation_length_1_inv in H2 as ->.
      destruct (IH3 _ eq_refl) as [ H | [ | (f & H & ?) ] ]; auto.
      * rewrite Forall_cons_inv in *.
        destruct HΓ as (? & HΓ); split; auto.
        revert HΓ; apply Permutation_Forall, Permutation_sym; auto.
      * left; apply in_ill3_perm with (2 := H).
        now apply Permutation_map.
      * do 2 right; exists f; split; auto.
        revert H; now apply Permutation_in.
    + contradict HΓ; solve Forall.
    + inversion HΔ; subst; contradict HΓ; solve Forall.
    + app inv singleton in HΔ.
      * destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; auto.
        - solve Forall.
        - destruct (IH2 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; auto.
          ++ solve Forall.
          ++ left; simpl; rewrite map_app; constructor; auto.
          ++ do 2 right; exists (A⊸B); simpl; tauto.
          ++ do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
        - do 2 right; exists (A⊸B); simpl; tauto.
        - do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
      * apply Schellinx_observation in H2 as (f & [ <- | ] & ?).
        - do 2 right; exists (A⊸B); simpl; tauto.
        - do 2 right; exists f; split; auto; right; apply in_or_app; tauto.
    + inversion HΔ; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; constructor; auto.
      * do 2 right; exists f; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; apply in_ill3_with_l1; auto.
      * do 2 right; exists (A&B); simpl; tauto.
      * do 2 right; exists f; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; apply in_ill3_with_l2; auto.
      * do 2 right; exists (A&B); simpl; tauto.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst; clear HΔ.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * destruct (IH2 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
        - solve Forall.
        - left; simpl; constructor; auto.
        - do 2 right; exists f; simpl; tauto.
      * do 2 right; exists f; simpl; tauto. 
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | [ <- | ] ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; constructor; auto.
      * do 2 right; exists (A⊗B); simpl; tauto.
      * do 2 right; exists (A⊗B); simpl; tauto.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst.
      app inv nil in H3.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * destruct (IH2 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
        - solve Forall.
        - left; rewrite map_app; constructor; auto.
        - do 2 right; exists f; split; auto.
          apply in_or_app; auto.
      * do 2 right; exists f; split; auto.
        apply in_or_app; auto.
    + contradict HΓ; solve Forall.
    + inversion HΔ; subst; contradict HΓ; solve Forall.
    + subst. 
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * destruct (IH2 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
        - solve Forall. 
        - left; simpl; now constructor.
        - do 2 right; exists (A⊕B); simpl; tauto.
        - do 2 right; exists f; auto.
      * do 2 right; exists (A⊕B); simpl; tauto.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now apply in_ill3_plus_r1.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now apply in_ill3_plus_r2.
      * do 2 right; exists f; auto.
    + left; constructor.
    + inversion HΔ; subst; left; constructor.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now constructor.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst; left; constructor.
    + discriminate.
    + inversion HΔ; subst; contradict HΓ; solve Forall.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now constructor.
      * do 2 right; exists (!A); simpl; auto.
      * do 2 right; exists f; auto.
    + destruct Δ; try discriminate.
      inversion HΔ; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; rewrite cll_ill_lbang in *; now constructor.
      * do 2 right; exists f; auto.
    + destruct Δ as [ |  D [ ] ]; try discriminate.
      inversion HΔ; subst; contradict HΓ; solve Forall.
    + inversion HΔ; subst; contradict HΓ; solve Forall.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & ? & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now constructor.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst.
      rewrite Forall_cons_inv in HΓ; simpl in HΓ; tauto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ | (f & [ <- | [ <- | ] ] & ?) ] ]; simpl; auto.
      * solve Forall.
      * left; now constructor.
      * do 2 right; exists (!A); simpl; auto.
      * do 2 right; exists (!A); simpl; auto.
      * do 2 right; exists f; auto.
    + inversion HΔ; subst; contradict HΓ; solve Forall.
  Qed.

  Lemma cll_ill_soundness Γ A : 
             ⟦Γ⟧ ⊢c [A]::∅ 
          -> Γ ⊢i A 
          \/ ill_has_bot A 
          \/ exists f, In f Γ /\ ill_has_bot f.
  Proof.
    intros H.
    apply cll_ill_rec with (2 := eq_refl) in H.
    * rewrite ill_cll_ill_list, ill_cll_ill, <- ill_cll_has_bot_eq in H.
      destruct H as [ | [ | (f & G1 & G2) ] ]; auto.
      do 2 right.
      apply in_map_iff in G1.
      destruct G1 as (g & <- & ?).
      exists g; rewrite ill_cll_has_bot_eq; auto.
    * rewrite -> Forall_map with (f := ill_cll) (ll := A::Γ), Forall_forall.
      intros; apply ill_cll_from_ill.
  Qed.

End cll_ill_soundness.

(* If the ILL sequent Γ ⊢ A does not contain any occurences of ⟘   then 
   it is provable in ILL iff it is provable in CLL 

   Which gives a direct reduction for CLL undecidability *)

Theorem ill_cll_equiv Γ A  : 
          (forall f, In f (A::Γ) -> ~ ill_has_bot f) 
       -> Γ ⊢i A <-> ⟦Γ⟧ ⊢c [A]::∅.
Proof.
  intros H; split.
  + apply ill_cll_soundness.
  + intros H1. 
    apply cll_ill_soundness in H1 as [ | [ ? | (f & ? & ?) ] ]; auto.
    * destruct (H A); simpl; auto.
    * destruct (H f); simpl; auto.
Qed.
