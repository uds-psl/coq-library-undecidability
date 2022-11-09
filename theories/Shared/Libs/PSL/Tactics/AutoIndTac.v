(* Mostly taken form https://github.com/sigurdschneider/lvc/blob/23b7fa8cd0640503ff370144fb407192632f9cc6/Infra/AutoIndTac.v *)

(* fail 1 will break from the 'match H with', and indicate to
   the outer match that it should consider finding another 
   hypothesis, see documentation on match goal and fail
   This tactic is a variation of Tobias Tebbi's revert_except_until *)

Ltac revert_all :=
  repeat match goal with [ H : _ |- _ ] => revert H end.

Tactic Notation "revert" "all" := revert_all.

Ltac revert_except i :=
  repeat match goal with [ H : _ |- _ ] => tryif unify H i then fail else revert H end.
                         
Tactic Notation "revert" "all" "except" ident(i) := revert_except i.

Ltac clear_except i :=
  repeat match goal with [ H : _ |- _ ] => tryif unify H i then fail else clear H end.
                         
Tactic Notation "clear" "all" "except" ident(i) := clear_except i.

Ltac clear_all :=
  repeat match goal with
           [H : _ |- _] =>  clear H
         end.

