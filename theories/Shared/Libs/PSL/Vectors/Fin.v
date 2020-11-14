(** * Tactics for [Fin.t] *)

(* Author: Maximilian Wuttke *)


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

Ltac destruct_fin i :=
  match type of i with
  | Fin.t (S ?n) =>
    let i' := fresh i in
    pose proof fin_destruct_S i as [ (i'&->) | -> ];
    [ destruct_fin i'
    | idtac]
  | Fin.t O =>
    pose proof fin_destruct_O i as []
  end.

Goal True.
  assert (i : Fin.t 4) by repeat constructor.
  enough (i = i) by tauto.
  destruct_fin i.
  all: reflexivity.
Qed.