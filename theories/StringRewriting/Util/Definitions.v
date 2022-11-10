Require Import Undecidability.StringRewriting.SR.
Require Import Setoid List Lia.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

Import ListNotations RuleNotation.

#[local] Hint Resolve in_cons incl_refl incl_appr incl_appl : list.

Lemma list_prefix_inv'' X (a : X) x u y v :
  ~ In a u -> ~ In a v -> x ++ a :: y = u ++ a :: v -> x = u /\ y = v.
Proof.
  induction x in u, v |- *; intros Hu Hv H; cbn in *.
  - destruct u. split. reflexivity. now inversion H. inversion H; subst. cbn in Hu. tauto.
  - destruct u. 
    + inversion H; subst. destruct Hv. apply in_app_iff. cbn. tauto.
    + inversion H; subst. eapply IHx in H2 as [-> ->]; eauto with list.
Qed.

Lemma list_prefix_inv X (a : X) x u y v :
  ~ In a x -> ~ In a u -> x ++ a :: y = u ++ a :: v -> x = u /\ y = v.
Proof.
  intro. revert u.
  induction x; intros; destruct u; inversion H1; subst; try now firstorder.
    eapply IHx in H4; try now firstorder. intuition congruence.
Qed.

(* * Definitions *)

#[local] Notation string := (string nat).
#[local] Notation SRS := (SRS nat).
Implicit Types a b : nat.
Implicit Types x y z : string.
Implicit Types d e : (string * string).
Implicit Types A R P : list (string * string).

Coercion sing (n : nat) := [n].

(* ** String Rewriting *)

Lemma rewt_induct :
  forall (R : SRS) z (P : string -> Prop),
    (P z) ->
    (forall x y : string, rew R x y -> rewt R y z -> P y -> P x) -> forall s, rewt R s z -> P s.
Proof.
  intros. induction H1; firstorder.
Qed.

#[export] Instance PreOrder_rewt R : PreOrder (rewt R).
Proof.
  split.
  - econstructor.
  - hnf. intros. induction H; eauto using rewR, rewS.
Qed.

Lemma rewt_subset R P x y :
  rewt R x y -> incl R P -> rewt P x y.
Proof.
  induction 1; intros.
  - reflexivity.
  - inversion H. subst. eapply rewS; eauto.
    eapply rewB. eauto.
Qed.

Lemma rew_subset (R P : SRS) x y :
  rew R x y -> incl R P -> SR.rew P x y.
Proof.
  intros H1 H2. inversion H1; subst.
  econstructor. eauto.
Qed.

Lemma rew_app_inv (R1 R2 : SR.SRS nat) x y :
  SR.rew (R1 ++ R2) x y <-> SR.rew R1 x y \/ SR.rew R2 x y.
Proof.
  split.
  - inversion 1 as [x0 y0 u v H0]; subst; eapply in_app_iff in H0 as [H0 | H0].
    + left. econstructor. eauto.
    + right. econstructor. eauto.
  - intros [H | H]; eapply rew_subset; eauto with list.
Qed.

(* ** Alphabets *)

Fixpoint sym (R : list (string * string)) :=
  match R with
    [] => []
  | x / y :: R => x ++ y ++ sym R
  end.

Lemma sym_word_l R u v  :
  In (u / v) R -> incl u (sym R).
Proof.
  induction R; cbn; intros.
  - easy.
  - destruct a as (u', v'). destruct H; try inversion H; subst; eauto with list.
Qed.

Lemma sym_word_R R u v  :
  In (u / v) R -> incl v (sym R).
Proof.
  induction R; cbn; intros.
  - easy.
  - destruct a as (u', v'). destruct H; try inversion H; subst; eauto with list.
Qed.

#[export] Hint Resolve sym_word_l sym_word_R : core.

(* *** Fresh symbols *)

Fixpoint fresh (l : list nat) :=
  match l with
  | [] => 0
  | x :: l => S x + fresh l
  end.

Lemma fresh_spec' l a : In a l -> a < fresh l.
Proof.
  induction l.
  - easy.
  - cbn; intros [ | ]; firstorder lia.
Qed.

Lemma fresh_spec (a : nat) (l : string) : In a l -> fresh l <> a.
Proof.
  intros H % fresh_spec'. intros <-. lia.
Qed.
