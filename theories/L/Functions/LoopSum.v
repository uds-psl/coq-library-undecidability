From Undecidability.L Require Import Tactics.LTactics.
From Undecidability.L.Datatypes Require Import LNat LSum LOptions.
Require Export Undecidability.L.Prelim.LoopSum.

Section loopSum.
  Variable X Y : Type.
  Context `{registered X}.
  Context `{registered Y}.

  Fixpoint time_loopSum (f: X -> X + Y) (fT : timeComplexity (X -> X + Y))
           (n:nat) (x : X) {struct n}:=
    4 + match n with
        | 0 => 0
        | S n' => fst (fT x tt)
                +  match f x with
                     inl x' => time_loopSum f fT n' x'
                   | inr x => 0
                   end
        end + 11.

  Global Instance termT_loopSum : computableTime' (@loopSum X Y) (fun n _ => (5,fun f fT => (1,fun x _ => (time_loopSum f fT n x,tt)))).
  extract.
  solverec.
  Qed.
End loopSum.


Lemma time_loopSum_bound_onlyByN {X Y} (H : registered X) (H0 : registered Y) (f:X -> X + Y) fT (P: nat -> _ -> Prop) boundL boundR:
  (forall n x, P n x -> match f x with
              | inl x' => P (S n) x' /\ fst (fT x tt) <= boundL
              | inr y => forall n', n <= n' -> fst (fT x tt) <= boundL + boundR n'
              end) ->
  forall n x,
    P 0 x -> 
    time_loopSum f fT n x <= n * (boundL + 15) + boundR n + 15.
Proof.
  intros H' n x.
  pose (n':=n). assert (Hleq : n<=n') by (cbn;omega).
  replace 0 with (n'-n) at 1 by (cbn;omega).
  replace (boundR n) with (boundR n') by reflexivity.
  clearbody n'.
  induction n in x,Hleq |-*. 1:now cbn;Lia.nia.
  intros HPx.
  cbn -[plus].
  specialize H' with (x:=x).
  destruct (f x).
  -edestruct H' as [? ->]. eassumption. rewrite IHn. 2:easy. Lia.lia. replace (n'-n) with (S (n'-S n)) by Lia.nia. eassumption. 
  -rewrite H' with (n':=n'). 2:easy. all:Lia.lia.
Qed.

