(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation Arith.

From Undecidability.ILL Require Import ILL.

Set Implicit Arguments.

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

Local Infix "~p" := (@Permutation _) (at level 70).

(* Symbols for cut&paste ⟙   ⟘   𝝐  ﹠ ⊗  ⊕  ⊸  ❗   ‼  ∅  ⊢ ⟦ ⟧ Γ Δ Σ *)

Section S_cll_restr_without_cut.

  (** CLL rules restricted to the (!,&,-o) fragment without cut *)

  Inductive S_cll_restr : list ll_form -> list ll_form -> Prop :=

    | in_cll1_ax     : forall A,                        A::∅ ⊢ A::∅

    | in_cll1_perm  : forall Γ Δ Γ' Δ',      Γ ~p Γ' -> Δ ~p Δ' ->   Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->                 Γ' ⊢ Δ'

    | in_cll1_limp_l : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll1_limp_r : forall Γ Δ A B,               A::Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A ⊸ B::Δ

    | in_cll1_with_l1 : forall Γ Δ A B,               A::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ

    | in_cll1_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ
 
    | in_cll1_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B::Δ

    | in_cll1_bang_l : forall Γ A Δ,                 A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->            !A::Γ ⊢ Δ

    | in_cll1_bang_r : forall Γ A,                    ‼Γ ⊢ A::nil               (* since ? is absent, only ??Δ = nil works *)
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A::nil

    | in_cll1_weak_l : forall Γ A Δ,                   Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->           !A::Γ ⊢ Δ

    | in_cll1_cntr_l : forall Γ A Δ,             !A::!A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ Δ

  where "l ⊢ m" := (S_cll_restr l m).

End S_cll_restr_without_cut.

Section S_cll_without_cut.

  (** CLL rules restricted to the (𝟘,?,⅋) free fragment without cut 
      which shares the same formula language as ILL, but of course 
      not the same rules *)

  Inductive S_cll : list ll_form -> list ll_form -> Prop :=

    | in_cll2_ax     : forall A,                        A::∅ ⊢ A::∅

    | in_cll2_perm  : forall Γ Δ Γ' Δ',      Γ ~p Γ' -> Δ ~p Δ' ->   Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->                 Γ' ⊢ Δ'

    | in_cll2_limp_l : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ      ->   B::Γ' ⊢ Δ'
                                           (*-----------------------------*)    
                                      ->           A ⊸ B::Γ++Γ' ⊢ Δ++Δ'

    | in_cll2_limp_r : forall Γ Δ A B,               A::Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->            Γ ⊢ A ⊸ B::Δ

    | in_cll2_with_l1 : forall Γ Δ A B,               A::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ

    | in_cll2_with_l2 : forall Γ Δ A B,              B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->           A﹠B::Γ ⊢ Δ
 
    | in_cll2_with_r : forall Γ Δ A B,        Γ ⊢ A::Δ     ->   Γ ⊢ B::Δ
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A﹠B::Δ

    | in_cll2_times_l : forall Γ A B Δ,            A::B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->            A⊗B::Γ ⊢ Δ
 
    | in_cll2_times_r : forall Γ Δ Γ' Δ' A B,  Γ ⊢ A::Δ    ->   Γ' ⊢ B::Δ'
                                           (*-----------------------------*)
                                      ->          Γ++Γ' ⊢ A⊗B::Δ++Δ'

    | in_cll2_plus_l :  forall Γ A B Δ,         A::Γ ⊢ Δ  ->  B::Γ ⊢ Δ 
                                           (*-----------------------------*)
                                      ->            A⊕B::Γ ⊢ Δ

    | in_cll2_plus_r1 : forall Γ A B Δ,               Γ ⊢ A::Δ  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B::Δ

    | in_cll2_plus_r2 : forall Γ A B Δ,               Γ ⊢ B::Δ  
                                           (*-----------------------------*)
                                      ->              Γ ⊢ A⊕B::Δ

    | in_cll2_bot_l : forall Γ Δ,                     ⟘::Γ ⊢ Δ

    | in_cll2_top_r : forall Γ Δ,                      Γ ⊢ ⟙::Δ

    | in_cll2_unit_l : forall Γ Δ,                       Γ ⊢ Δ  
                                           (*-----------------------------*)
                                        ->           𝟙::Γ ⊢ Δ

    | in_cll2_unit_r :                                  ∅ ⊢ 𝟙::∅


    | in_cll2_bang_l : forall Γ A Δ,                 A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->            !A::Γ ⊢ Δ

    | in_cll2_bang_r : forall Γ A,                    ‼Γ ⊢ A::nil               (* since ? is absent, only ??Δ = nil works *)
                                           (*-----------------------------*)
                                      ->              ‼Γ ⊢ !A::nil

    | in_cll2_weak_l : forall Γ A Δ,                   Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->           !A::Γ ⊢ Δ

    | in_cll2_cntr_l : forall Γ A Δ,             !A::!A::Γ ⊢ Δ
                                           (*-----------------------------*)
                                      ->             !A::Γ ⊢ Δ

  where "l ⊢ m" := (S_cll l m).

End S_cll_without_cut.

Section S_ill_cll_restr.

  Notation "Γ '⊢i' A" := (S_ill_restr Γ A) (at level 70).
  Notation "Γ '⊢c' Δ" := (S_cll_restr Γ Δ) (at level 70).

  Theorem S_ill_cll_restr Γ A : Γ ⊢i A -> Γ ⊢c A::∅.
  Proof.
    induction 1.
    + apply in_cll1_ax.
    + now apply (@in_cll1_perm Γ (A::nil)).
    + now apply in_cll1_limp_l with (Δ := ∅) (Δ' := _::_).
    + now apply in_cll1_limp_r with (Δ := ∅).
    + now apply in_cll1_with_l1.
    + now apply in_cll1_with_l2.
    + now apply in_cll1_with_r with (Δ := ∅).
    + now apply in_cll1_bang_l.
    + now apply in_cll1_bang_r.
    + now apply in_cll1_weak_l.
    + now apply in_cll1_cntr_l.
  Qed.

  Let cll_ill_empty_rec Γ Δ : Γ ⊢c Δ -> Δ <> ∅.
  Proof.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A Δ H1 IH1 | Γ A H1 IH1                                (* bang *)
                   | Γ A Δ H1 IH1                                             (* weak *)
                   | Γ A Δ H1 IH1 ];                                          (* cntr *)
            auto; try discriminate.
    + intros ->; now apply IH3, Permutation_nil, Permutation_sym.
    + intros H; now app inv nil in H.
  Qed.

  Let cll_ill_empty Γ : ~ Γ ⊢c ∅.
  Proof. intros H; now apply cll_ill_empty_rec with (1 := H). Qed.

  Let cll_ill_rec Γ Δ  : Γ ⊢c Δ -> forall A, Δ = A::∅ -> Γ ⊢i A.
  Proof.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A Δ H1 IH1 | Γ A H1 IH1                                (* bang *)
                   | Γ A Δ H1 IH1                                             (* weak *)
                   | Γ A Δ H1 IH1 ];                                          (* cntr *)
            intros C HC; try discriminate.
    + inversion HC; constructor.
    + constructor 2 with (1 := H1).
      rewrite HC in *.
      apply Permutation_sym, Permutation_length_1_inv in H2 as ->.
      apply IH3; auto.
    + app inv singleton in HC.
      * constructor; auto.
      * apply cll_ill_empty in H2 as [].
    + inversion HC; subst.
      constructor; apply IH1; auto.
    + rewrite HC in *.
      apply in_ill1_with_l1, IH1; auto.
    + rewrite HC in *.
      apply in_ill1_with_l2, IH1; auto.
    + inversion HC; subst; clear HC.
      constructor; auto.
    + subst; constructor; apply IH1; auto.
    + inversion HC; subst; constructor; auto.
    + subst; apply in_ill1_weak; auto.
    + subst; apply in_ill1_cntr; auto.
  Qed.

  Theorem S_cll_ill_restr Γ A : Γ ⊢c A::∅ -> Γ ⊢i A.
  Proof.
    intros H; now apply cll_ill_rec with (1 := H).
  Qed.

  Hint Resolve S_ill_cll_restr S_cll_ill_restr : core.

  Theorem S_ill_cll_restr_equiv Γ A : Γ ⊢i A <-> Γ ⊢c A::∅.
  Proof. split; auto. Qed.

End S_ill_cll_restr.

Section S_ill_cll.

  Notation "Γ '⊢i' A" := (S_ill Γ A) (at level 70).
  Notation "Γ '⊢c' Δ" := (S_cll Γ Δ) (at level 70).

  Theorem S_ill_cll Γ A : Γ ⊢i A -> Γ ⊢c A::∅.
  Proof.
    induction 1.
    + apply in_cll2_ax.
    + now apply (@in_cll2_perm Γ (A::nil)).
    + now apply in_cll2_limp_l with (Δ := ∅) (Δ' := _::_).
    + now apply in_cll2_limp_r with (Δ := ∅).
    + now apply in_cll2_with_l1.
    + now apply in_cll2_with_l2.
    + now apply in_cll2_with_r with (Δ := ∅).
    + now apply in_cll2_bang_l.
    + now apply in_cll2_bang_r.
    + now apply in_cll2_weak_l.
    + now apply in_cll2_cntr_l.
    + now apply in_cll2_times_l.
    + now apply in_cll2_times_r with (Δ := ∅) (Δ' := ∅).
    + now apply in_cll2_plus_l.
    + now apply in_cll2_plus_r1.
    + now apply in_cll2_plus_r2.
    + apply in_cll2_bot_l.
    + apply in_cll2_top_r.
    + now apply in_cll2_unit_l.
    + apply in_cll2_unit_r.
  Qed.

  Let Fixpoint has_bot f :=
    match f with
     | ll_var _ => False  
     | ll_zero x => x = ll_bot
     | ll_ban f => has_bot f
     | ll_bin _ f g => has_bot f \/ has_bot g
    end.

  Let cll_ill_empty_rec Γ Δ : Γ ⊢c Δ -> Δ = ∅ -> exists f, In f Γ /\ has_bot f.
  Proof.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2             (* * *)
                   | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1  (* + *)
                   | |                                                        (* bot, top *)
                   | Γ Δ H1 IH1 |                                             (* unit *)
                   | Γ A Δ H1 IH1 | Γ A H1 IH1                                (* bang *)
                   | Γ A Δ H1 IH1                                             (* weak *)
                   | Γ A Δ H1 IH1  ];                                         (* cntr *)
             try discriminate.
    + intros ->.
      apply Permutation_sym, Permutation_nil in H2 as ->.
      destruct IH3 as (f & G1 & G2); auto.
      exists f; split; auto.
      revert G1; now apply Permutation_in.
    + intros H.
      app inv nil in H.
      destruct IH2 as (f & G1 & G2); auto.
      destruct G1 as [ <- | G1 ].
      * exists (A ⊸ B); simpl; split; auto.
      * exists f; split; auto.
        right; apply in_or_app; tauto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | G1 ].
      * exists (A & B); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | G1 ].
      * exists (A & B); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | [ <- | G1 ] ].
      * exists (A ⊗ B); simpl; auto.
      * exists (A ⊗ B); simpl; auto.
      * exists f; simpl; auto.
    + intros ->; destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | G1 ].
      * exists (A ⊕ B); simpl; auto.
      * exists f; simpl; auto.
    + exists ⟘; simpl; auto.
    + intros ->.
      destruct IH1 as (f & ? & ?); auto.
      exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | G1 ].
      * exists (!A); simpl; auto.
      * exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      exists f; simpl; auto.
    + intros ->.
      destruct IH1 as (f & G1 & G2); auto.
      destruct G1 as [ <- | [ <- | G1 ] ].
      * exists (!A); simpl; auto.
      * exists (!A); simpl; auto.
      * exists f; simpl; auto.
  Qed.
 
  Let cll_ill_empty Γ : Γ ⊢c ∅ -> exists f, In f Γ /\ has_bot f.
  Proof. intros H; now apply cll_ill_empty_rec with (1 := H). Qed.

  Let cll_ill_rec Γ Δ  : Γ ⊢c Δ -> forall A, Δ = A::∅ -> Γ ⊢i A \/ has_bot A \/ exists f, In f Γ /\ has_bot f.
  Proof.
    induction 1 as [ A                                                        (* ax *)
                   | Γ Δ Γ' Δ' H1 H2 H3 IH3                                   (* perm *)
                   | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1             (* -o *)
                   | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2  (* & *)
                   | Γ A B Δ H1 IH1 | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2             (* * *)
                   | Γ A B Δ H1 IH1 H2 IH2 | Γ A B Δ H1 IH1 | Γ A B Δ H1 IH1  (* + *)
                   | |                                                        (* bot, top *)
                   | Γ Δ H1 IH1 |                                             (* unit *)
                   | Γ A Δ H1 IH1 | Γ A H1 IH1                                (* bang *)
                   | Γ A Δ H1 IH1                                             (* weak *)
                   | Γ A Δ H1 IH1  ];                                         (* cntr *)
             intros C HC.
    + inversion HC; left; constructor.
    + rewrite HC in *.
      apply Permutation_sym, Permutation_length_1_inv in H2 as ->.
      destruct (IH3 _ eq_refl) as [ ? | [ ? | (f & Hf & ?) ] ]; auto.
      * left; now constructor 2 with (1 := H1).
      * do 2 right; exists f; split; auto.
        revert Hf; now apply Permutation_in.
    + app inv singleton in HC.
      * destruct (IH1 _ eq_refl) as [ ? | G1 ]; auto.
        - destruct (IH2 _ eq_refl) as [ ? | [ ? | (f & [ <- | Hf1 ] & Hf2) ] ]; auto.
          ++ left; constructor; auto.
          ++ do 2 right; exists (A ⊸ B); simpl; tauto.
          ++ do 2 right; exists f; split; auto; right; apply in_or_app; auto.
        - do 2 right; destruct G1 as [ G1 | (f & ? & ?) ].
          ++ exists (A ⊸ B); simpl; tauto.
          ++ exists f; split; auto; right; apply in_or_app; auto.
      * do 2 right.
        apply cll_ill_empty in H2 as (f & [ <- | Hf1 ] & Hf2).
        - exists (A ⊸ B); simpl; tauto.
        - exists f; split; auto; right; apply in_or_app; auto.
    + inversion HC; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & [ <- | Hf ] & ?) ] ]; simpl; auto.
      * left; constructor; auto.
      * do 2 right; exists f; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & [ <- | Hf ] & ?) ] ]; simpl; auto.
      * left; apply in_ill3_with_l1; auto.
      * do 2 right; exists (A&B); simpl; auto.
      * do 2 right; exists f; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & [ <- | Hf ] & ?) ] ]; simpl; auto.
      * left; apply in_ill3_with_l2; auto.
      * do 2 right; exists (A&B); simpl; auto.
      * do 2 right; exists f; auto.
    + inversion HC; subst; clear HC.
      destruct (IH1 _ eq_refl) as [ ? | G1 ]; auto.
      * destruct (IH2 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
        - left; constructor; auto.
        - do 2 right; exists f; split; auto; right; apply in_or_app; auto.
      * destruct G1 as [ G1 | (f & ? & ?) ]; simpl; auto.
        do 2 right; exists f; split; auto; right; apply in_or_app; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & [ <- | [ <- | Hf ] ] & ?) ] ]; simpl; auto.
      * left; apply in_ill3_times_l; auto.
      * do 2 right; exists (A⊗B); simpl; auto.
      * do 2 right; exists (A⊗B); simpl; auto.
      * do 2 right; exists f; auto.
    + inversion HC; subst. 
      app inv nil in H3; simpl.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; auto.
      * destruct (IH2 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; auto.
        - left; constructor; auto.
        - do 2 right; exists f; split; auto; apply in_or_app; auto.
      * do 2 right; exists f; split; auto; apply in_or_app; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; auto.
      * destruct (IH2 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; auto.
        - left; constructor; auto.
        - do 2 right; destruct Hf1 as [ <- | ].
          ++ exists (A ⊕ B); simpl; auto. 
          ++ exists f; split; simpl; auto.
      * do 2 right; destruct Hf1 as [ <- | ].
        - exists (A ⊕ B); simpl; auto. 
        - exists f; split; simpl; auto.
    + inversion HC; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; constructor; auto.
      * do 2 right; exists f; auto.
    + inversion HC; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; apply in_ill3_plus_r2; auto.
      * do 2 right; exists f; auto.
    + do 2 right; exists ⟘; simpl; auto.
    + inversion HC; subst; left; constructor.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; constructor; auto.
      * do 2 right; exists f; auto.
    + inversion HC; subst; left; constructor.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; constructor; auto.
      * do 2 right.
        destruct Hf1 as [ <- | Hf1 ].
        - exists (!A); simpl; auto.
        - exists f; auto.
    + inversion HC; subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; constructor; auto.
      * do 2 right.
        apply in_map_iff in Hf1.
        destruct Hf1 as (g & <- & ?).
        exists (!g); simpl in *; split; auto.
        apply in_map_iff; exists g; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; apply in_ill3_weak; auto.
      * do 2 right; exists f; auto.
    + subst.
      destruct (IH1 _ eq_refl) as [ ? | [ ? | (f & Hf1 & Hf2) ] ]; simpl; auto.
      * left; apply in_ill3_cntr; auto.
      * do 2 right; destruct Hf1 as [ <- | [ <- | Hf1 ] ]; simpl in *.
        - exists (!A); simpl; auto.
        - exists (!A); simpl; auto.
        - exists f; auto.
  Qed.

  Theorem S_cll_ill Γ A : Γ ⊢c A::∅ -> Γ ⊢i A \/ has_bot A \/ exists f, In f Γ /\ has_bot f.
  Proof. intros H; now apply cll_ill_rec with (1 := H). Qed.

End S_ill_cll.




