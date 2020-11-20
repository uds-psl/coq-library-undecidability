From Undecidability.TM.Hoare Require Import HoareLogic.
Definition abbreviate {A:Type} (x:A) := x.
Arguments abbreviate {A} {x}.
  
  (* The concept of abbreviations is taken from  VST*)

  Tactic Notation "abbreviate" constr(y) "as"  ident(x)  :=
  (first [ is_var y
          |  let x' := fresh x in pose (x':= @abbreviate _ y);
              change y with x']).

Tactic Notation "abbreviate" constr(y) ":" constr(t) "as"  ident(x)  :=
   (first [ is_var y
           |  let x' := fresh x in pose (x':= @abbreviate t y);
               change y with x']).

Ltac unfold_abbrev :=
  repeat match goal with H := @abbreviate _ _ |- _ =>
                        unfold H, abbreviate; clear H
            end.

Ltac clear_abbrevs :=  repeat match goal with
                        | H := @abbreviate (_ -> Assert _ _) _ |- _ => clear H
                        | H := @abbreviate (Assert _) _ |- _ => clear H
                        end.

Ltac force_sequential  :=
lazymatch goal with
(*| P := @abbreviate ret_assert (normal_ret_assert _) |- semax _ _ _ ?P' =>
    constr_eq P P'
| P := @abbreviate ret_assert _ |- semax _ _ ?c ?P' =>
    constr_eq P P'; 
    try (is_sequential false false c;
         unfold abbreviate in P; subst P;
         apply sequential; simpl_ret_assert)
| P := @abbreviate ret_assert _ |- _ => unfold abbreviate in P; subst P;
      force_sequential
| P := _ : ret_assert |- semax _ _ _ ?P' => 
      constr_eq P P'; unfold abbreviate in P; subst P;
      force_sequential
| |- semax _ _ _ (normal_ret_assert ?P) => 
       abbreviate (normal_ret_assert P) : ret_assert as POSTCONDITION
| |- semax _ _ ?c ?P =>
    tryif (is_sequential false false c)
    then (apply sequential; simpl_ret_assert;
          match goal with |- semax _ _ _ ?Q =>
             abbreviate Q : ret_assert as POSTCONDITION
          end)
    else abbreviate P : ret_assert as POSTCONDITION *)
| |- TripleT _ _ _ ?P => abbreviate P as POSTCONDITION
| |- Triple _ _ ?P => abbreviate P as POSTCONDITION
end.

Ltac abbreviate_TM := force_sequential.

Ltac start_TM := abbreviate_TM.