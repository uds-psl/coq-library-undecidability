From Coq Require Import List Arith Lia Permutation Wf_nat.
Import ListNotations.

From Undecidability.Shared.Libs.DLW Require Import gcd prime.
From Undecidability.FRACTRAN Require Import FRACTRAN fractran_utils.

Set Default Goal Selector "!".

(* necessary facts on prime factorization *)
Module Prime_factors.

#[local] Notation lprod := (fold_right mult 1).

Lemma prime_divides_lt {lc ld} :
  ~ (divides (lprod ld) (lprod lc)) ->
  Forall prime lc -> Forall prime ld ->
  exists (p : nat), prime p /\ count_occ Nat.eq_dec lc p < count_occ Nat.eq_dec ld p.
Proof.
  revert lc. induction ld as [|a ld IHld].
  - intros lc H. exfalso. apply H.
    exists (lprod lc). cbn. lia.
  - intros lc H Hlc Hld'.
    pose proof (Ha := Forall_inv Hld').
    pose proof (Hld := Forall_inv_tail Hld').
    destruct (in_dec Nat.eq_dec a lc) as [Halc|Halc].
    + apply in_split in Halc as [l1c [l2c ?]]. subst lc.
      assert (H' : not (divides (lprod (ld)) (lprod (l1c ++ l2c)))).
      { intros [p Hp]. rewrite !lprod_app in *.
        apply H. exists p. cbn. nia. }
      assert (H'lc : Forall prime (l1c ++ l2c)).
      { revert Hlc. rewrite !Forall_app.
        now intros [? ? %Forall_inv_tail]. }
      specialize (IHld _ H' H'lc Hld).
      destruct IHld as [p [? Hp]].
      exists p. split; [assumption|].
      revert Hp. rewrite !count_occ_app. cbn.
      destruct (Nat.eq_dec); lia.
    + exists a. split; [assumption|].
      apply (count_occ_not_In Nat.eq_dec) in Halc.
      rewrite count_occ_cons_eq, Halc; lia.
Qed.

Definition count_pow (p n : nat) : nat :=
  let (l, _) := (@prime_decomp (S n) (Nat.neq_succ_0 n))
    in count_occ Nat.eq_dec l p.

Lemma prime_divides_lt' {c d} (Hc : c <> 0) (Hd : d <> 0):
  ~ (divides d c) ->
  exists p,
    (forall x y, (S x) * c = (S y) * d -> count_pow p y < count_pow p x).
Proof.
  pose proof (@prime_decomp c Hc) as [lc [Hclc Hlc]].
  pose proof (@prime_decomp d Hd) as [ld [Hdld Hld]].
  subst. intros H. apply prime_divides_lt in H as [p [? Hp]]; [|assumption ..].
  exists p. intros x y. unfold count_pow.
  destruct (@prime_decomp (S x) _) as [lx [Hxlx Hlx]].
  destruct (@prime_decomp (S y) _) as [ly [Hyly Hly]].
  rewrite Hxlx, Hyly, <- !lprod_app.
  intros E. apply prime_decomp_uniq in E; [|now rewrite Forall_app ..].
  assert (iffLR : forall P Q, (P <-> Q) -> P -> Q) by tauto.
  assert (H' := iffLR _ _ (Permutation_count_occ Nat.eq_dec _ _) E p).
  rewrite !count_occ_app in H'. lia.
Qed.

Lemma rel_prime_intro {p q} : (p <> 0 \/ q <> 0) ->
  { a & { b & { g | p = a*g /\ q = b*g /\ is_gcd a b 1 } } }.
Proof.
  intros ?. assert (Hg := gcd_spec p q).
  assert (gcd p q <> 0).
  { intros H'g. rewrite H'g in Hg. apply is_gcd_0 in Hg. tauto. }
  destruct (divides_dec p (gcd p q)) as [[a Ha]|].
  2: { unfold is_gcd in Hg. tauto. }
  destruct (divides_dec q (gcd p q)) as [[b Hb]|].
  2: { unfold is_gcd in Hg. tauto. }
  exists a, b, (gcd p q). split; [easy|split;[easy|]].
  split; [apply divides_1|]. split; [apply divides_1|].
  intros [|[|k]].
  - intros [??] [??]. nia.
  - intros _ _. now exists 1.
  - intros [ka ?] [kb ?]. subst a b. exfalso.
    destruct Hg as [[??] [[??] Hpq]].
    destruct (Hpq (S (S k) * (gcd p q))) as [k' ?].
    + exists ka. nia.
    + exists kb. nia.
    + destruct k' as [|?]; nia.
Qed.

End Prime_factors.

Import Prime_factors.

Module Argument.

Lemma fractran_nstop_cons a b l s :
  (forall t, ~ l /F/ t ↓) -> ~ (a,b) :: l /F/ s ↓.
Proof.
  intros H [u [[n Hsu] Hu]].
  destruct (divides_dec (a*u) b) as [[t Ht]|?].
  - apply (Hu t), in_fractran_0. lia.
  - apply (H u). exists u.
    split; [now exists 0|].
    intros t Hut. now apply (Hu t), in_fractran_1.
Qed.

Lemma fractran_nstop_zero_num_1 d l s : ~ (0,d) :: l /F/ s ↓.
Proof.
  destruct d as [|d]; simpl; intros [y [_ Hs]]; apply (Hs 0); now constructor.
Qed.

Lemma fractran_stop_zero_den_1 c s (Hc : c <> 0) : [(c, 0)] /F/ s ↓.
Proof.
  destruct s as [|s]; simpl.
  - exists 1. constructor.
    + exists 1. exists 1. constructor; [|reflexivity].
      now constructor.
    + intros z [?|[? Hz]]%fractran_step_cons_inv; [lia|inversion Hz].
  - exists (S s). constructor.
    + now exists 0.
    + intros z [?|[? Hz]]%fractran_step_cons_inv; [lia|inversion Hz].
Qed.

Lemma fractran_stop_ndiv_singleton x c d (Hc : c <> 0) (Hd : d <> 0) :
  ~ divides d c -> [(c,d)] /F/ (S x) ↓.
Proof.
  intros [p H]%(prime_divides_lt' Hc Hd).
  induction x as [x IH] using (induction_ltof1 _ (fun x => (count_pow p x))); unfold ltof in IH.
  destruct (fractran_step_dec [(c,d)] (S x)) as [[y Hxy]|Hs].
  - revert Hxy. intros [|[? Hxy]]%fractran_step_cons_inv.
    + destruct y as [|y]; [lia|].
      specialize (H x y ltac:(lia)).
      apply IH in H as [y' [[n Hyy'] Hs']].
      exists y'. split; [|exact Hs'].
      exists (1+n), (S y). now split; [constructor|].
    + inversion Hxy.
  - exists (S x). now split; [exists 0|].
Qed.

(* if the second fraction is not redundant, then the program is not reversible *)
Lemma fractran_step_contradict_reversible a b c d l :
  is_gcd b a 1 -> ~ divides b d ->
  exists (s t u : nat),
    (a,b) :: (c,d) :: l /F/ s ≻ u /\ (a,b) :: (c,d) :: l /F/ t ≻ u /\ s <> t.
Proof.
  intros Hba Hbd. exists (c*b), (a*d), (a*c).
  constructor; [constructor; lia|].
  constructor.
  - apply in_fractran_1.
    + intros Hb. now do 2 apply (is_rel_prime_div _ Hba) in Hb.
    + constructor. lia.
  - intros E. apply Hbd. apply (is_rel_prime_div _ Hba). now exists c.
Qed.

Lemma fractran_step_iff_halt l1 l2 :
  (forall s t, l1 /F/ s ≻ t <-> l2 /F/ s ≻ t) -> (forall x, l1 /F/ x ↓ -> l2 /F/ x ↓).
Proof.
  intros H x. intros [y [[n Hn] Hs]]. exists y. constructor.
  - exists n. revert x Hn. induction n as [|n IHn]; simpl; auto.
    intros x [y' [Hy' Hs']]. exists y'. constructor; [now apply H|now apply IHn].
  - intros z Hs'. now apply (Hs z), H.
Qed.

Lemma fractran_step_iff_decide {l1 l2 n} :
  (forall s t, l1 /F/ s ≻ t <-> l2 /F/ s ≻ t) ->
  ((l1 /F/ n ↓) + (not (l1 /F/ n ↓))) ->
  ((l2 /F/ n ↓) + (not (l2 /F/ n ↓))).
Proof.
  intros H [|Hn]; [left|right].
  - eapply fractran_step_iff_halt; eassumption.
  - intros ?. apply Hn. eapply fractran_step_iff_halt; [|eassumption].
    firstorder easy.
Qed.

(* in a reversible FRACTRAN program the second fraction is shadowed by the first *)
Lemma fractran_reversible_shadow {a b c d P x y} : x <> 0 -> y <> 0 ->
  fractran_reversible ((a * x, b * x) :: (c * y, d * y) :: P) ->
  is_gcd b a 1 -> is_gcd d c 1 ->
  forall s t, (c * y) * s = t * (d * y) -> exists u, (a * x) * s = u * (b * x).
Proof.
  intros ?? HP Hba Hdc.
  destruct (divides_dec d b) as [[u Hu]|Hb].
  - subst d. intros s t Hst.
    assert (Hubcs : divides (u * b) (c * s)) by (exists t; nia).
    destruct (is_rel_prime_div s Hdc Hubcs) as [k ?].
    subst s. exists (a*k*u). nia.
  - exfalso.
    destruct (fractran_step_contradict_reversible a b c d P Hba Hb) as [s [t [u [? [? Hst]]]]].
    apply Hst.
    enough (H_extend : forall s' t', (a, b) :: (c, d) :: P /F/ s' ≻ t' ->
      (a * x, b * x) :: (c * y, d * y) :: P /F/ s' ≻ t').
    { apply (HP s t u); now apply H_extend. }
    intros s' t' [|[H'b Hs't']]%fractran_step_cons_inv.
    + apply in_fractran_0. nia.
    + revert Hs't'. intros [|[H'd Hs't']]%fractran_step_cons_inv.
      * apply in_fractran_1.
        { intros [k ?]. apply H'b. exists k. nia. }
        apply in_fractran_0. nia.
      * apply in_fractran_1.
        { intros [k1 ?]. apply H'b. exists k1. nia. }
        apply in_fractran_1.
        { intros [k2 ?]. apply H'd. exists k2. nia. }
        exact Hs't'.
Qed.

Lemma fractran_reversible_shorten {a b c d P s t} :
  fractran_reversible ((S a, b) :: (S c, d) :: P) ->
  ((S a, b) :: P /F/ s ≻ t) <-> ((S a, b) :: (S c, d) :: P /F/ s ≻ t).
Proof.
  intros HP.
  assert (Hba : b <> 0 \/ S a <> 0) by lia.
  destruct (rel_prime_intro Hba) as [b' [a' [gab [H'b [H'a Hb'a']]]]].
  rewrite H'b, H'a in *.
  assert (Hdc : d <> 0 \/ S c <> 0) by lia.
  destruct (rel_prime_intro Hdc) as [d' [c' [gcd [H'd [H'c Hd'c']]]]].
  rewrite H'd, H'c in *.
  assert (Hgab : gab <> 0) by lia.
  assert (Hgcd : gcd <> 0) by lia.
  split.
  + intros [?|[Hb ?]]%fractran_step_cons_inv.
    * now apply in_fractran_0.
    * apply in_fractran_1; [easy|].
      apply in_fractran_1; [|easy].
      intros [m Hm]. apply Hb.
      eapply (fractran_reversible_shadow Hgab Hgcd HP Hb'a' Hd'c').
      eassumption.
  + intros [?|[Hb H']]%fractran_step_cons_inv.
    * now apply in_fractran_0.
    * revert H'. intros [H'|[Hd ?]]%fractran_step_cons_inv.
      ** exfalso. apply Hb. eapply (fractran_reversible_shadow Hgab Hgcd HP Hb'a' Hd'c' s t). lia.
      ** now apply in_fractran_1.
Qed.

(* informative decision statement for empty FRACTRAN halting *)
Lemma fractran_empty_decision (n: nat) : ([] /F/ n ↓).
Proof.
  exists n. split; [now exists 0|].
  intros z H. now inversion H.
Qed.

(* informative decision statement for singleton FRACTRAN halting *)
Lemma fractran_singleton_decision c d n : ([(c,d)] /F/ n ↓) + (not ([(c,d)] /F/ n ↓)).
Proof.
  destruct (divides_dec c d) as [[k Hk] | Hndiv].
  { right. intros [y [[m Hm] Hstop]]. apply (Hstop (k*y)). constructor. nia. }
  destruct c as [|c].
  { right. now intros H%fractran_nstop_zero_num_1. }
  destruct d as [|d].
  { left. now apply fractran_stop_zero_den_1. }
  destruct n as [|n].
  { right. intros [y [[n Hn] Hy]].
    apply fractran_rt_no_zero_den in Hn.
    - apply (Hy 0). apply in_fractran_0. lia.
    - now repeat constructor. }
  left. now apply fractran_stop_ndiv_singleton.
Qed.

(* informative decision statement for reversible FRACTRAN halting *)
Theorem decision (P : list (nat * nat)) (n: nat) : fractran_reversible P -> (P /F/ n ↓) + (not (P /F/ n ↓)).
Proof.
  induction P as [P IH] using (induction_ltof1 _ (fun P => length P)); unfold ltof in IH.
  destruct P as [|(a,b) [|(c,d) P]].
  - (* empty program *)
    intros _. left. now apply fractran_empty_decision.
  - (* singleton program *)
    intros _. now apply fractran_singleton_decision.
  - (* at least two fractions, remove the second *)
    destruct a as [|a]; simpl.
    { intros _. right. now intros H%fractran_nstop_zero_num_1. }
    destruct c as [|c]; simpl.
    { intros _. right. now apply fractran_nstop_cons, fractran_nstop_zero_num_1. }
    intros HP.
    enough (H'P : forall s t, ((S a, b) :: P) /F/ s ≻ t <-> ((S a, b) :: (S c, d) :: P) /F/ s ≻ t).
    { apply (fractran_step_iff_decide H'P).
      apply IH; simpl; [lia|].
      intros n1 n2 m Hn1%H'P Hn2%H'P. eapply HP; eassumption. }
    intros s t. now apply fractran_reversible_shorten.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* decision procedure for the halting problem for reversible FRACTRAN *)
Definition decide : { P : list (nat * nat) | fractran_reversible P } * nat -> bool :=
  fun '(exist _ P HP, x) =>
    match Argument.decision P x HP with
    | inl _ => true
    | inr _ => false
    end.

(* decision procedure correctness *)
Lemma decide_spec : decider decide Halt_REV_FRACTRAN.
Proof.
  intros [[P HP] x]. unfold reflects. simpl.
  destruct (Argument.decision P x HP) as [[y Hy%eval_iff]|HPx].
  - firstorder easy.
  - split; [|easy]. intros [y ?%eval_iff]. firstorder easy.
Qed.
