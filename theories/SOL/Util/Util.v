(** * Preliminaries *)

From Coq Require Import PeanoNat.
Require Import Lia.
Import Nat.


(** ** Cantor Pairing *)
(** Code by Gert Smolka: https://www.ps.uni-saarland.de/~smolka/drafts/coq/pairing.v *)

Section Pairing.

  Implicit Types (n x y: nat) (c: nat * nat).

  Definition next c : nat * nat :=
    match c with
    | (0,y) => (S y, 0)
    | (S x, y) => (x, S y)
    end.

  Fixpoint unembed n : nat * nat :=
    match n with
    | 0 => (0,0)
    | S n' => next (unembed n')
    end.

  Fixpoint sum n : nat :=
    match n with
    | 0 => 0
    | S n' => S n' + sum n'
    end.

  Definition embed '(x, y) : nat :=
    sum (x + y) + y.

  Fact embed_next c :
    embed (next c) = S (embed c).
  Proof.
    destruct c as [[|x] y]; cbn -[sum].
    - rewrite !add_0_r. rewrite add_comm. reflexivity.
    - rewrite !add_succ_r. reflexivity.
  Qed.

  Fact embed_unembed n :
    embed (unembed n) = n.
  Proof.
    induction n as [|n IH]; cbn.
    - reflexivity.
    - rewrite embed_next, IH. reflexivity.
  Qed.

  Fact unembed_embed c :
    unembed (embed c) = c.
  Proof.
    revert c.
    enough (forall n c, embed c = n -> unembed n = c) by eauto.
    induction n as [|n IH]; intros [x y]; cbn [unembed].
    - destruct x, y.
      1:reflexivity. all:intros [=].
    - destruct y. 1:destruct x.
      + intros [=].
      + change (S x, 0) with (next (0,x)).
        rewrite embed_next. intros H. f_equal.
        apply IH. congruence.
      + change (x, S y) with (next (S x, y)). 
        rewrite embed_next. intros H. f_equal.
        apply IH. congruence.
  Qed.


  (* Definition prec p := match p with (S (S x), S y) => (x, y) | _ => (0, 0) end. *)
  Definition back n := match n with (S n) => n | 0 => 0 end.
  Definition pi1 n := fst (unembed n).
  Definition pi2 n := snd (unembed n).

  Lemma pi1_correct x y :
    pi1 (embed (x, y)) = x.
  Proof.
    unfold pi1. now rewrite unembed_embed.
  Qed.

  Lemma pi2_correct x y :
    pi2 (embed (x, y)) = y.
  Proof.
    unfold pi2. now rewrite unembed_embed.
  Qed.

  Lemma embed_zero :
    embed (0, 0) = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma embed_not_zero_l x y :
    embed (S x, y) <> 0.
  Proof.
    easy.
  Qed.

  Lemma embed_not_zero_r x y :
    embed (x, S y) <> 0.
  Proof.
    cbn. lia.
  Qed.

  Lemma sum_gt x :
    sum x >= x.
  Proof.
    induction x; cbn; lia.
  Qed.

  Lemma embed_gt x y :
    embed (x, y) >= x + y.
  Proof.
    cbn. pose (sum_gt (x + y)). lia.
  Qed.

  Lemma embed_succ n :
    exists x y, S n = embed (S x, y) \/ S n = embed (x, S y).
  Proof.
    destruct (unembed (S n)) as [[] []] eqn:H.
    - exfalso. cbn in H. destruct (unembed n) as [[] []]; cbn in H; try congruence.
    - exists 0, n0. right. rewrite <- H. now rewrite embed_unembed.
    - exists n0, 0. left. rewrite <- H. now rewrite embed_unembed.
    - exists (S n0), n1. right. rewrite <- H. now rewrite embed_unembed.
  Qed.


  Lemma pi1_le n :
    pi1 (S (S n)) < S (S n).
  Proof.
    unfold pi1. destruct (embed_succ (S n)) as [x [y [H1 | H2]]].
    - rewrite H1, unembed_embed. cbn [fst]. destruct y.
      + destruct x; cbn in *; lia.
      + pose (embed_gt (S x) (S y)). lia.
    - rewrite H2, unembed_embed. cbn [fst]. pose (embed_gt x (S y)). lia.
  Qed.

  Lemma pi2_le n :
    pi2 (S n) < S n.
  Proof.
    unfold pi2. destruct (embed_succ n) as [x [y [-> | ->]]].
    - rewrite unembed_embed. cbn [snd]. pose (embed_gt (S x) y). lia.
    - rewrite unembed_embed. cbn [snd]. destruct x.
      + cbn. lia.
      + pose (embed_gt (S x) (S y)). lia.
  Qed.

  Lemma pi1_pi2_le n :
    pi1 (pi2 (S n)) < S n.
  Proof.
    destruct n as [|[]]; try (cbn; lia).
    assert (pi2 (S (S (S n))) < S (S (S n))) by apply pi2_le.
    destruct (pi2 (S (S (S n)))) as [|[]]; cbn. lia. lia.
    pose (pi1_le n0). lia.
  Qed.

  Lemma pi2_pi2_le n :
    pi2 (pi2 (S n)) < S n.
  Proof.
    assert (pi2 (S n) < S n) by apply pi2_le.
    destruct (pi2 (S n)); cbn. lia. pose (pi2_le n0). lia.
  Qed.


  Global Opaque embed unembed pi1 pi2.

End Pairing.



(** ** Witness Operator *)
(** Code by Gert Smolka: https://www.ps.uni-saarland.de/~smolka/drafts/coq/wo.v *)

Section WO.
  Variable p: nat -> Prop.
  Variable p_dec: forall n, {p n} + {~ p n}.

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Lemma T_base n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma T_step n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply T_step, H.
  Qed.

  Lemma V n :
    p n -> T 0.
  Proof.
    intros H. eapply T_zero, T_base, H.
  Qed.

  Lemma W' :
    forall n, T n -> { k | p k }.
  Proof.
    refine (fix F n a {struct a} := let (phi) := a in
                          match p_dec n with
                            left H => _ | right H => _
                          end).
    - exact (exist p n H).
    - exact (F (S n) (phi H)).
  Qed.

  Theorem W :
    (exists n, p n) -> { n | p n }.
  Proof.
    intros H. apply (W' 0).
    destruct H as [n H].
    apply (V n), H.
  Qed.

End WO.



(** ** Hedberg's Theorem *)
(** Code by Gert Smolka: https://github.com/uds-psl/ACT/blob/master/coq/indeq.v *)

From Coq Require Import Logic.

Section Hedberg.

  Variable X: Type.
  Implicit Types x y z: X.

  Definition UIP := forall x y (e e': x = y), e = e'.
  Definition UIP' := forall x (e : x = x), e = eq_refl.

  Definition cast {x y} {p: X -> Type} : x = y -> p x -> p y :=
    fun e a => match e with eq_refl => a end.

  Definition sigma {x y} : x = y -> y = x := 
    fun e => cast (p:= fun z => z = x) e eq_refl.

  Definition tau {x y z} : x = y -> y = z -> x = z := 
    fun e => cast e (fun e => e).

  Lemma tau_sigma x y (e: x = y) :
    tau e (sigma e) = eq_refl.
  Proof.
    destruct e. reflexivity.
  Qed.

  Variable eq_dec : (forall x y : X, x = y \/ x <> y).

  Definition f {x y} (e : x = y) := match eq_dec x y with or_introl e' => e' | _ => e end.

  Lemma f_eq  x y (e e': x = y) :
    f e = f e'.
  Proof.
    unfold f. destruct eq_dec as [e''|h]. reflexivity. destruct (h e).
  Qed.

  Theorem Hedberg : 
    UIP.
  Proof.
    intros x y.
    assert (f_eq1 : forall e: x = y,  tau (f e) (sigma (f eq_refl)) = e).
    { destruct e. apply tau_sigma. }
    intros e e'.
    rewrite <-(f_eq1 e), <-(f_eq1 e').
    f_equal. apply f_eq.
  Qed.


  Lemma uip' :
    UIP'.
  Proof.
    intros x e. apply Hedberg.
  Qed.

  Lemma inj_pairT2 :
    forall p x u v, existT p x u = existT p x v -> u = v.
  Proof.
    intros p x.
    enough (forall a b : { x & p x }, a = b -> forall e: projT1 a = projT1 b, cast e (projT2 a) = projT2 b) as H.
    { intros u v e. apply (H _ _ e eq_refl). }
    intros a b [] e. now assert (e = eq_refl) as -> by now apply Hedberg.
  Qed.

End Hedberg.


Lemma nat_eq_dec_same n :
  Nat.eq_dec n n = left (eq_refl).
Proof.
  destruct Nat.eq_dec. f_equal. apply uip'. lia. easy.
Qed.

