From Undecidability Require Export CodeTM Copy ChangeAlphabet WriteValue.
From Undecidability Require Export TMTac.
From Undecidability Require Export Basic.Mono Compound.Multi.
Require Import Lia.
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


Tactic Notation "destruct" "_" "in" constr(H):=
  match type of H with
  | context[match ?X with _ => _ end] => destruct X
  | context[match ?X with _ => _ end] => destruct X
  end.

(* Tactics for interactive refinements of Relations that ger derived instead of full TM_correct. See e.g. DecodaTape *)
Tactic Notation "tacInEvar" constr(E) tactic3(tac) :=
  is_evar E;
  let t := type of E in
  let __tmp_callInEvar := fresh "__tmp_callInEvar" in
  evar (__tmp_callInEvar:t);
  (only [__tmp_callInEvar]:tac);unify E __tmp_callInEvar;subst __tmp_callInEvar;instantiate.

Tactic Notation "introsSwitch" ne_simple_intropattern_list(P):=
  match goal with
    |- (forall f' , ?REL _ (?R f')) =>
    tacInEvar R intros P;cbn beta;intros P
  end.

Tactic Notation "destructBoth" constr(g) "as" simple_intropattern(P) :=
  lazymatch goal with
    |- (RealiseIn _ ?R _) =>
    tacInEvar R (destruct g as P);destruct g as P;cbn zeta iota beta
  | |- (?REL _ ?R) =>
    tacInEvar R (destruct g as P);destruct g as P;cbn zeta iota beta
  end.


Tactic Notation "destructBoth" constr(g) :=
  destructBoth g as [].


Tactic Notation "infTer" int_or_var(n) :=
  let t := try (first [simple eapply ex_intro | simple apply conj | simple eapply Nat.le_refl])
  in t;do n t.


Tactic Notation "length_not_eq" "in" constr(H):=
  let H' := fresh "H" in
  specialize (f_equal (@length _) H) as H';repeat (try autorewrite with list in H';cbn in H');nia.

Ltac length_not_eq :=
  let H := fresh "H" in intros H;exfalso;length_not_eq in H.


(** Machine Notations *)

Notation "pM @ ts" := (LiftTapes pM ts) (at level 41, only parsing).
Notation "pM ⇑ R" := (ChangeAlphabet pM R) (at level 40, only parsing).

From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.
