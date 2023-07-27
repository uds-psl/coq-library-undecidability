From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Import Reflection Computable.

(* ** Symbolic simplification for L*)

(* *** Lproc *)

(* This module provides tactics fLproc and Lproc that solve goals of the form [lambda s] or [proc s] or [closed s] for L-terms [s]. *)

#[export] Hint Resolve rho_lambda rho_cls : LProc.

Lemma proc_closed p : proc p -> closed p.
Proof.
  firstorder easy.
Qed.

Lemma proc_lambda p : proc p -> lambda p.
Proof.
  firstorder easy.
Qed.

Ltac fLproc :=intros;
              once lazymatch goal with
              | [ |- proc _ ] => split;fLproc
              | [ |- lambda ?s ] => eexists; reflexivity || fail "Prooving 'lambda " s " ' by computation failed. It is either not a fixed term, some used identifier is opaqie or the goal does not hold"
              | [ |- closed ?s ] => vm_compute; reflexivity || fail "Prooving 'closed " s " ' by computation failed. It is either not a fixed term, some used identifier is opaque or the goal does not hold"
              end.



Ltac Lproc' :=idtac;
  once lazymatch goal with
  | |- bound _ (L.app _ _) => refine (dclApp _ _)
  | |- bound _ (L.lam _) => refine (dcllam _)
  | |- bound ?y (L.var ?x) => exact (dclvar (proj1 (Nat.ltb_lt x y) eq_refl))
  | |- lambda (match ?c with _ => _ end) => destruct c
  | |- lambda (@enc ?t ?H ?x) => exact_no_check (proc_lambda (@proc_enc t H x))
  | |- lambda (@ext ?X ?tt ?x ?H) => exact_no_check (proc_lambda (@proc_ext X tt x H))
  | |- lambda (app _ _) => fail
  | |- lambda _ => (simple apply proc_lambda;(trivial with nocore LProc || tauto)) || tauto || (eexists;reflexivity)
  | |- rClosed ?phi _ => solve [simple apply rClosed_decb_correct;[assumption|reflexivity]]
  | |- L.closed ?s => refine (proj2 (closed_dcl s) _)
  | |- bound _  (match ?c with _ => _ end) => destruct c
  | |- bound _ (rho ?s) => simple apply rho_dcls
  | |- bound ?k (@ext ?X ?tt ?x ?H) =>
    exact_no_check (closed_dcl_x k (proc_closed (@proc_ext X tt x H)))
  | |- bound ?k (@enc ?t ?H ?x) =>
    exact_no_check (closed_dcl_x k (proc_closed (@proc_enc t H x)))
  | |- bound ?k ?s => (refine (@closed_dcl_x k s _); (trivial with LProc || (apply proc_closed;trivial with LProc || tauto) || tauto ))
  | |- ?s => idtac s;fail 1000
  end.


(* early abort for speed!*)
Tactic Notation (at level 3) "repeat'" tactic3(t) :=
  let rec loop := (once t);try loop in loop.

Ltac Lproc := (* match goal with |- ?G => idtac G end ;time "Lproc"( *)
  lazymatch goal with
  | |- proc (app _ _) => fail
  | |- proc (@enc ?t ?H ?x) => exact_no_check (@proc_enc t H x)
  | |- proc (@ext ?X ?tt ?x ?H) => exact_no_check (@proc_ext X tt x H)
  | |- proc _ => refine (conj _ _);[|solve [Lproc]];Lproc
                                    
  | |- closed _ => solve [repeat' Lproc']
                     
  | |- lambda (app _ _) => fail
  | |- lambda _ => repeat' Lproc'
  | s := ?t |- ?p ?s => change (p t);Lproc
         end.