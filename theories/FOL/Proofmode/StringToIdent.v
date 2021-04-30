From MetaCoq.Template Require Import All.

MetaCoq Quote Definition qUnit := unit.

Definition unitFunc k := tLambda {| binder_name := nNamed k; binder_relevance := Relevant |} qUnit (tRel 0).

Ltac coq_string_to_ident_lambda' s :=
  let k v := exact v in
  run_template_program (tmUnquoteTyped (unit->unit) (unitFunc s)) k.

Ltac string_to_ident s :=
  let x := constr:(ltac:(coq_string_to_ident_lambda' s) : unit -> unit) in
  match x with
  | (fun (name:_) => _) => name
  end.
