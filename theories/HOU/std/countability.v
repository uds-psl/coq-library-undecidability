Set Implicit Arguments. 
Require Import FinFun.
From Undecidability.HOU Require Import std.decidable.
  
Inductive diag: nat -> nat -> Type :=
  | diagB: diag 0 0
  | diagC: forall m, diag 0 m -> diag (S m) 0
  | diagS: forall n m, diag (S n) m -> diag n (S m).


Fixpoint diagStepR m n (d: diag m n) : diag m (S n) :=
  match d with
  | diagB => diagS (diagC diagB)
  | diagC H => diagS (diagC (diagStepR H))
  | diagS H => diagS (diagStepR H)
  end.

Fixpoint diagStepL m n (d: diag m n) : diag (S m) n :=
  match d with
  | diagB => diagC diagB
  | diagC H => diagC (diagS (diagStepL H))
  | diagS H => diagS (diagStepL H)
  end.

Fixpoint diagZero (a: nat) : diag 0 a :=
  match a with
  | 0 => diagB
  | S a => diagStepR (diagZero a)
  end.

Fixpoint diagId m n: diag m n :=
  match m with
  | O => diagZero n
  | S m => diagStepL (diagId m n)
  end.

Definition I__P (p: nat * nat) :=
  let (m, n) := p in
  diag_rect (fun _ _ _ => nat) 0 (fun _ _ => S)  (fun _ _ _ => S) (diagId m n): nat.

Fixpoint R__P (n: nat) : nat * nat  :=
  match n with 
    | 0 =>  (0,0) 
    | S n => match R__P n with 
            | (0, b)  => (S b, 0)
            | (S a, b) => (a, S b)
      end
   end.

Lemma R__P_I__P p: R__P (I__P p) = p.
Proof.
  unfold I__P; destruct p as [m n]; induction (diagId m n); cbn.
  - reflexivity.
  - now rewrite IHd.
  - now rewrite IHd.
Qed.

Lemma R__P_injective n m: R__P n = R__P m -> n = m.
Proof.
  induction n in m |-*; destruct m; cbn; eauto.
  1: destruct (R__P m) as [[] b]; discriminate.
  1: destruct (R__P n) as [[] b]; discriminate.
  destruct (R__P n) as [[|k] p] eqn: H1, (R__P m) as [[|k'] p'] eqn: H2.
  all: injection 1; intros; subst.
  all: erewrite IHn; eauto.
  all: discriminate.
Qed.

Lemma I__P_R__P n: I__P (R__P n) = n.
Proof.
  eapply R__P_injective; now rewrite R__P_I__P.
Qed.


Require Import Arith Lia Nat Arith.Div2.

Definition I__S (s: nat + nat) :=
  match s with
  | inl n => double n
  | inr n => S (double n)
  end.


Definition R__S (n: nat) :=
  if even n then inl (div2 n) else inr (div2 n).

Lemma I__S_R__S n: I__S (R__S n) = n.
Proof.
  unfold I__S, R__S.
  destruct Nat.even eqn: H1.
  - symmetry. eapply even_double.  
    now eapply Even.even_equiv, Nat.even_spec.
  - symmetry. eapply odd_double; eauto.
    eapply Even.odd_equiv, Nat.odd_spec.
    unfold odd; rewrite H1; eauto.
Qed.

Lemma R__S_I__S s: (R__S (I__S s)) = s.
Proof.
  unfold I__S, R__S.
  destruct s.
  - specialize (Nat.even_spec (Nat.double n)) as [_ H].
    rewrite H, Nat.double_twice, Nat.div2_double; eauto.
    eapply Nat.even_spec. 
    unfold Nat.double.
    rewrite Nat.even_add.
    destruct (Nat.even n); reflexivity.
  - specialize (Nat.even_spec (Nat.double n)) as [_ H].
    rewrite Nat.even_succ, <-Nat.negb_even.
    rewrite H; cbn [negb].
    rewrite Nat.double_twice, Nat.div2_succ_double; eauto.
    eapply Nat.even_spec; unfold Nat.double;
      rewrite ?Nat.even_add; destruct (Nat.even n); reflexivity.
Qed.


Lemma injective_I__S : Injective I__S.
Proof.
  intros s s' H % (f_equal R__S). now rewrite !R__S_I__S in H.
Qed.

Lemma injective_I__P : Injective I__P.
Proof.
  intros s s' H % (f_equal R__P). now rewrite !R__P_I__P in H.
Qed.

Arguments I__P p : simpl never.
Arguments R__P n : simpl never.
Arguments I__S s : simpl never.
Arguments R__S n : simpl never.
