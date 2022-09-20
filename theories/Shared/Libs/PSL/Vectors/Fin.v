(* * Tactics for [Fin.t] *)

(* Author: Maximilian Wuttke and Fabian Kunze *)


From Undecidability.Shared.Libs.PSL Require Import Base.
Require Import Coq.Vectors.Fin.


Lemma fin_destruct_S (n : nat) (i : Fin.t (S n)) :
  { i' | i = Fin.FS i' } + { i = Fin.F1 }.
Proof.
  refine (match i in (Fin.t n')
          with
          | Fin.F1 => _
          | Fin.FS i' => _
          end); eauto.
  (*
  refine (match i as i0 in (Fin.t n') return
                match n' with
                | O => fun _ : Fin.t 0 => unit
                | S n'' => fun i0 : Fin.t (S n'') => { i' | i0 = Fin.FS i' } + { i0 = Fin0}
                end i0
          with
          | Fin.F1 => _
          | Fin.FS i' => _
          end); eauto.
   *)
Defined.

Lemma fin_destruct_O (i : Fin.t 0) : Empty_set.
Proof. refine (match i with end). Defined.


Lemma fin_destruct_add
: forall (n m : nat) (i : Fin.t (n+m)),
    {i' : Fin.t n | i = Fin.L _ i'} + {i' : Fin.t m | i = Fin.R _ i'}.
Proof.
  induction n;cbn. right. now eauto.
  intros ? i. destruct (fin_destruct_S i) as [[i' ->]| ->].
  -destruct (IHn _ i') as [ [? ->] | [? ->]].
    --left. now eexists (Fin.FS _).
    --right. eauto.
  -left. now exists Fin.F1.
Qed.  


Ltac destruct_fin i :=
  lazymatch type of i with
  | Fin.t (S ?n) =>
    let i' := fresh i in
    pose proof fin_destruct_S i as [ (i'&->) | -> ];
    [ destruct_fin i'
    | idtac]
  | Fin.t O =>
    pose proof fin_destruct_O i as []
  | Fin.t (_ + _) =>
    let i' := fresh i in
    pose proof fin_destruct_add i as [ (i'&->) | (i'&->)];destruct_fin i'
  | Fin.t _ => idtac
  end.
