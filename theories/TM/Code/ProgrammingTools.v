From Undecidability Require Export CodeTM Copy ChangeAlphabet WriteValue.
From Undecidability Require Export TMTac.
From Undecidability Require Export Basic.Mono Compound.Multi.

(** * All tools for programming Turing machines *)

(** All Coq modules in that the user programms Turing machine should [From Undecidability Require Import TM.Code.ProgrammingTools]. The module should additionally require and import the modules containing the constructor and deconstructor machines, e.g. [Require Import TM.Code.CaseNat], etc. *)




(** This tactic automatically solves/instantiates premises of a hypothesis. If the hypothesis is a conjunction, it is destructed. *)
Ltac modpon H :=
  simpl_surject;
  lazymatch type of H with
  | forall (i : Fin.t _), ?P => idtac
  | forall (x : ?X), ?P =>
    lazymatch type of X with
    | Prop =>
      tryif spec_assert H by
          (simpl_surject;
           solve [ eauto
                 | contains_ext
                 | isVoid_mono
                 ]
          )
      then idtac (* "solved premise of type" X *);
           modpon H
      else (spec_assert H;
            [ idtac (* "could not solve premise" X *) (* new goal for the user *)
            | modpon H (* continue after the user has proved the premise manually *)
            ]
           )
    | _ =>
      (* instantiate variable [x] with evar *)
      let x' := fresh "x" in
      evar (x' : X); specialize (H x'); subst x';
      modpon H
    end
  | ?X /\ ?Y =>
    let H' := fresh H in
    destruct H as [H H']; modpon H; modpon H'
  | _ => idtac
  end.



(** To get rid of all those uggly tape rewriting hypothesises. Be warned that maybe the goal can't be solved after that. *)
Ltac clear_tape_eqs :=
  repeat lazymatch goal with
         | [ H: ?t'[@ ?x] = ?t[@ ?x] |- _ ] => clear H
         end.


(** Machine Notations *)

Notation "pM @ ts" := (LiftTapes pM ts) (at level 41, only parsing).
Notation "pM ⇑ R" := (ChangeAlphabet pM R) (at level 40, only parsing).