Require Import List Arith.

From Undecidability.Shared.Libs.DLW 
  Require Import gcd rel_iter pos vec.

From Undecidability.FRACTRAN.Utils 
  Require Import prime_seq.

Require Import Undecidability.FRACTRAN.FRACTRAN.

Definition fractran_stop l x := forall z, ~ l /F/ x ≻ z.

Definition fractran_steps l := rel_iter (fractran_step l).
Definition fractran_compute l x y := exists n, fractran_steps l n x y.
Definition fractran_terminates l x := exists y, fractran_compute l x y /\ fractran_stop l y.

Notation "l '/F/' x ↓ " := (fractran_terminates l x) (at level 70, no associativity).

(* The Halting problem for a FRACTRAN instance (l,x) is determining if
   there is y related via (fractran_step l)* to x and maximal for (fractran_step l) *) 

Definition FRACTRAN_PROBLEM := (list (nat*nat) * nat)%type.
Definition FRACTRAN_HALTING (P : FRACTRAN_PROBLEM) := let (l,x) := P in l /F/ x ↓.
 
Definition fractran_regular (l : list (nat * nat)) := Forall (fun c => snd c <> 0) l.

Definition FRACTRAN_REG_PROBLEM := 
  { l : list (nat*nat) & { _ : nat | fractran_regular l } }.
Definition FRACTRAN_REG_HALTING (P : FRACTRAN_REG_PROBLEM) : Prop.
Proof.
  destruct P as (l & x & _).
  exact (l /F/ x ↓).
Defined.

(* Given a FRACTRAN program and a starting vector [v1,...,vn],
    does the program terminate starting from p1 * q1^v1 * ... qn^vn *)

Definition FRACTRAN_ALT_PROBLEM := (list (nat*nat) * { n : nat & vec nat n })%type.

Definition FRACTRAN_ALT_HALTING : FRACTRAN_ALT_PROBLEM -> Prop.
Proof.
  intros (l & n & v).
  exact (l /F/ ps 1 * exp 1 v ↓).
Defined.

Lemma eval_iff P n m :
  fractran_eval P n m <-> fractran_compute P n m /\ fractran_stop P m.
Proof.
  split.
  - induction 1 as [ P n 
                    | P n m m' Hstep H [[k IH1] IH2]].
     + split. 
       * exists 0. econstructor.
       * firstorder.
     + split.
       * exists (1 + k). econstructor. eauto.
       * eauto.
  - intros [[k H1] H2].
    induction k in n, m, H1, H2 |- *.
    + inversion H1 as []. subst. econstructor. firstorder.
    + inversion H1 as [m' [H3 H4]].
      econstructor; eauto.
Qed. 

Lemma Halt_FRACTRAN_iff P :
  Halt_FRACTRAN P <-> FRACTRAN_HALTING P.
Proof.
  destruct P as (P, n).
  unfold Halt_FRACTRAN. now setoid_rewrite eval_iff.
Qed.