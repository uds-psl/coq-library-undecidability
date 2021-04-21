From Equations Require Import Equations DepElim.
From Undecidability.Shared Require Import Dec ListAutomation.
From Undecidability.FOL Require Import Util.Syntax Util.Syntax_facts Util.FullDeduction Util.FullDeduction_facts Util.FullTarski.
From Undecidability.FOL.Proofmode Require Import Theories.

Require Import List Lia String.
Import ListNotations.

Open Scope string_scope.

(* 
 * We to have an Iris-like proof mode, where the context is displayed
 * above a line with the current goal below. Also the assumptions should
 * have names.
 * This is all done using notation. But this notation should only be applied
 * in the goal, not in other hypothesis. Therefore we define aliases for 
 * `prv` and lists that the notation can match for. Also the list alias
 * holds the assumption names as an extra argument.
 *)
Definition pm {p cf cp ff} C phi := @prv p cf cp ff C phi.
Arguments pm {_} {_} {_} {_} _ _.

Definition tpm {p cf cp ff} C phi := @tprv p cf cp ff C phi.
Arguments tpm {_} {_} {_} {_} _ _.

Section PM.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ff : falsity_flag}.


Definition cnil := @nil form.
Definition ccons (s : string) phi C := @cons form phi C.
(* Special alias for unknown lists. Only used to indent with one space in Notation *)
Definition cblackbox (A : list form) := A.

Definition tnil : theory := fun _ => False.
Definition tcons (s : string) phi (T : theory) : theory := extend T phi.
(* Special alias for unknown theories. Only used to indent with one space in Notation *)
Definition tblackbox (T : theory) := T.

End PM.


(* Dummy tactic the end user *must* override if defined
 * terms like `zero` are used. *)
Ltac custom_fold := idtac.

(* Dummy tactic the end user *must* override if defined
 * terms like `zero` are used. *)
 Ltac custom_unfold := idtac.

(* Dummy tactic the end user can override to add domain
 * specific simplifications. *)
Ltac custom_simpl := idtac.



(** Overload deduction rules to also work for theories: *)

Class DeductionRules `{funcs_signature, preds_signature, falsity_flag} (context : Type) (ent : context -> form -> Type) (cons : form -> context -> context) (map : (form -> form) -> context -> context) (In : form -> context -> Prop) :=
{
  II A phi psi : ent (cons phi A) psi -> ent A (phi ~> psi) ;
  IE A phi psi : ent A (phi ~> psi) -> ent A phi -> ent A  psi ;
  AllI A phi : ent (map (subst_form ↑) A) phi -> ent A (∀ phi) ;
  AllE A t phi : ent A (∀ phi) -> ent A (phi[t..]) ;
  ExI A t phi : ent A (phi[t..]) -> ent A (∃ phi) ;
  ExE A phi psi : ent A (∃ phi) -> ent (cons phi (map (subst_form ↑) A)) (psi[↑]) -> ent A psi ;
  Ctx A phi : In phi A -> ent A phi ;
  CI A phi psi : ent A phi -> ent A psi -> ent A (phi ∧ psi) ;
  CE1 A phi psi : ent A (phi ∧ psi) -> ent A phi ;
  CE2 A phi psi : ent A (phi ∧ psi) -> ent A psi ;
  DI1 A phi psi : ent A phi -> ent A (phi ∨ psi) ;
  DI2 A phi psi : ent A psi -> ent A (phi ∨ psi) ;
  DE A phi psi theta : ent A (phi ∨ psi) -> ent (cons phi A) theta -> ent (cons psi A) theta -> ent A theta ;
}.

Class ClassicalDeductionRules `{funcs_signature, preds_signature, falsity_flag} (context : Type) (ent : context -> form -> Type) :=
{
  Pc A phi psi : ent A (((phi ~> psi) ~> phi) ~> phi)
}.

Class FalsityDeductionRules `{funcs_signature, preds_signature} (context : Type) (ent : context -> form -> Type) :=
{
  Exp A phi : ent A ⊥ -> ent A phi ;
}.

Class WeakClass `{funcs_signature, preds_signature, falsity_flag} (context : Type) (ent : context -> form -> Type) (incl : context -> context -> Prop) :=
{
  Weak A B phi : ent A phi -> incl A B -> ent B phi
}.

Instance prv_DeductionRules `{funcs_signature, preds_signature, falsity_flag, peirce} : DeductionRules (list form) prv cons (@List.map form form) (@In form) := 
{| 
  II := FullDeduction.II ;
  IE := FullDeduction.IE ;
  AllI := FullDeduction.AllI ;
  AllE := FullDeduction.AllE ;
  ExI := FullDeduction.ExI ;
  ExE := FullDeduction.ExE ;
  Ctx := FullDeduction.Ctx ;
  CI := FullDeduction.CI ;
  CE1 := FullDeduction.CE1 ;
  CE2 := FullDeduction.CE2 ;
  DI1 := FullDeduction.DI1 ;
  DI2 := FullDeduction.DI2 ;
  DE := FullDeduction.DE ;
|}.

Instance prv_ClassicalDeductionRules `{funcs_signature, preds_signature, falsity_flag} : ClassicalDeductionRules (list form) (@prv _ _ _ class) := 
{| 
  Pc := FullDeduction.Pc
|}.

Instance prv_FalsityDeductionRules `{funcs_signature, preds_signature, peirce} : FalsityDeductionRules (list form) (@prv _ _ falsity_on _) := 
{| 
  Exp := FullDeduction.Exp
|}.

Instance prv_WeakClass `{funcs_signature, preds_signature, falsity_flag, peirce} : WeakClass (list form) prv (@List.incl form) := 
{| 
  Weak := FullDeduction_facts.Weak
|}.

(* TODO: Why doesn't this exist? *)
Instance eq_dec_full_operators : eq_dec binop. unfold dec; decide equality. Qed.
Instance eq_dec_full_logic_quant : eq_dec quantop. unfold dec; decide equality. Qed.

Instance tprv_DeductionRules `{funcs_signature, preds_signature, falsity_flag, peirce, eq_dec syms, eq_dec preds} : DeductionRules theory tprv (fun a b => extend b a) mapT (fun a b => in_theory b a) := 
{| 
  II := Theories.T_II ;
  IE := Theories.T_IE ;
  AllI := Theories.T_AllI ;
  AllE := Theories.T_AllE ;
  ExI := Theories.T_ExI ;
  ExE := Theories.T_ExE ;
  Ctx := Theories.T_Ctx ;
  CI := Theories.T_CI ;
  CE1 := Theories.T_CE1 ;
  CE2 := Theories.T_CE2 ;
  DI1 := Theories.T_DI1 ;
  DI2 := Theories.T_DI2 ;
  DE := Theories.T_DE ;
|}.

Instance tprv_ClassicalDeductionRules `{funcs_signature, preds_signature, falsity_flag} : ClassicalDeductionRules theory (@tprv _ _ _ class) := 
{| 
  Pc := Theories.T_Pc
|}.

Instance tprv_FalsityDeductionRules `{funcs_signature, preds_signature, peirce} : FalsityDeductionRules theory (@tprv _ _ falsity_on _) := 
{| 
  Exp := Theories.T_Exp
|}.

Instance tprv_WeakClass `{funcs_signature, preds_signature, falsity_flag, peirce} : WeakClass theory tprv subset_T := 
{| 
  Weak := Theories.WeakT
|}.



(** Context utilities *)

Definition digit_to_string n := match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5" 
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | _ => "_"
end.
Fixpoint nat_to_string' fuel n := match fuel with
  | 0 => "OUT OF FUEL"
  | S fuel' => match n with
    | 0 => ""
    | _ =>  nat_to_string' fuel' (Nat.div n 10)  ++ digit_to_string (Nat.modulo n 10)
    end
end.
Definition nat_to_string n := match n with 0 => "0" | _ => nat_to_string' 100 n end.

(* Returns the index of the first occurence of `name` in the 
 * context `C`, or `None` if it doesn't exist. *)
Ltac lookup' n C name :=
  match C with
  | ccons name _ _ => constr:(Some n) 
  | ccons _ _ ?C' => lookup' (S n) C' name
  | tcons name _ _ => constr:(Some n) 
  | tcons _ _ ?T' => lookup' (S n) T' name
  | _ => None
  end.
Ltac lookup := lookup' 0.

Ltac nth A n :=
  match n with
  | 0 => match A with ?t :: _ => t | extend _ ?t => t | ccons _ ?t _ => t | tcons _ ?t _ => t end
  | S ?n' => match A with _ :: ?A' => nth A' n' | extend ?A' _ => nth A' n' | ccons _ _ ?A' => nth A' n' | tcons _ _ ?T' => nth T' n' end
  end.

Ltac remove A n :=
  match n with
  | 0 => match A with _ :: ?A' => A' | extend ?A' _ => A' | ccons _ _ ?A' => A' | tcons _ _ ?A' => A' end
  | S ?n' => match A with 
    | ?t :: ?A' => let A'' := remove A' n' in constr:(t::A'') 
    | extend ?A' ?t => let A'' := remove A' n' in constr:(extend t A'') 
    | ccons ?s ?t ?A' => let A'' := remove A' n' in constr:(ccons s t A'') 
    | tcons ?s ?t ?A' => let A'' := remove A' n' in constr:(tcons s t A'') 
    end
  end.

Ltac replace_ltac A n phi :=
  match n with
  | 0 => match A with _ :: ?A' => constr:(phi::A') | extend ?A' _ => constr:(extend A' phi) | ccons ?s _ ?A' => constr:(ccons s phi A') | tcons ?s _ ?A' => constr:(tcons s phi A') end
  | S ?n' => match A with 
    | ?t :: ?A' => let A'' := replace_ltac A' n' phi in constr:(t::A'') 
    | extend ?A' ?t => let A'' := replace_ltac A' n' phi in constr:(extend t A'') 
    | ccons ?s ?t ?A' => let A'' := replace_ltac A' n' phi in constr:(ccons s t A'') 
    | tcons ?s ?t ?A' => let A'' := replace_ltac A' n' phi in constr:(tcons s t A'') 
    end
  end.

Ltac map_ltac A f :=
  match A with
  | nil => constr:(nil)
  | cnil => constr:(cnil)
  | tnil => constr:(tnil)
  | @Vector.nil ?a => constr:(@Vector.nil a)
  | cblackbox ?A' => A
  | tblackbox ?A' => A
  | cons ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(cons x' A'')
  | ccons ?s ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(ccons s x' A'')
  | tcons ?s ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(tcons s x' A'')
  | @Vector.cons _ ?x _ ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(@Vector.cons _ x' _ A'')
  end.

(* Finds the first name of form `base`, `base0`, `base1`, ... thats not 
 * contained in the context/variable list `C`. *)
Ltac new_name' n base C :=
  let name := match n with 
    | 0 => base
    | S ?n' => let s := eval cbn in (nat_to_string n') in eval cbn in (base ++ s)
  end in
  match lookup C name with
  | @None => name
  | @Some _ _ => new_name' (S n) base C
  end.
Ltac new_name base C := new_name' 0 base C.

(* For context creation we need to give names to the initial formulas.
 * This is done using syntactic matching with ltac instead of a Galina
 * function, because if we want to prove `A ⊢ φ` for an unknown A we 
 * don't want to go into the `A`. *)
Ltac create_context' A :=
  match A with
  | ?phi::?A' =>
    let x := create_context' A' in match x with (?c, ?n) =>
      match n with
        | 0 => constr:((ccons "H" phi c, S n))
        | S ?n' => let s' := eval cbn in ("H" ++ nat_to_string n') in constr:((ccons s' phi c, S n))
      end
    end
  | extend ?T' ?phi =>
    let x := create_context' T' in match x with (?c, ?n) =>
      match n with
        | 0 => constr:((tcons "H" phi c, S n))
        | S ?n' => let s' := eval cbn in ("H" ++ nat_to_string n') in constr:((tcons s' phi c, S n))
      end
    end
  | nil => constr:((cnil, 0))
  | _ => 
    (* If it's not a cons or nil, it's a variable/function call/... 
     * and we don't want to look into it *)
    match type of A with
    | list form => constr:((cblackbox A, 0))
    | theory => constr:((tblackbox A, 0))
    | form -> Prop => constr:((tblackbox A, 0))
    end
  end.
Ltac create_context A := let x := create_context' A in match x with (?c, _) => c end.




(** Variable names utilities: *)

(* We save identifiers with the binder of a trivial function *)
Inductive ident_name := Ident : (unit -> unit) -> ident_name.

Require Import Undecidability.FOL.Proofmode.Ltac2StringIdent.
Ltac to_ident_name id :=
  eval cbv in (ltac:(clear; apply Ident; intros id; assumption) : ident_name).

Notation "x" := (Ident (fun x => x)) (at level 1, only printing).

Definition named_quant {fsig psig ops ff} op (x : ident_name) phi := @quant fsig psig ops ff op phi.
Definition named_var {fsig} n (x : ident_name) := @var fsig n.
Arguments named_var {_ _} _.

(* Fails if `n` is not constant (e.g. a variable). Else returns 0. *)
Ltac assert_is_constant_nat n :=
  match n with
    | 0 => 0
    | S ?n => assert_is_constant_nat n
  end.

Ltac annotate_term f t :=
  match t with
    | context C[ var ?n ] => 
        let _ := assert_is_constant_nat n in
        let ident_name := eval cbn in (f n) in
        let t' := context C[ @named_var _ n ident_name ] in
        annotate_term f t'
    | _ => t 
  end.
  (* match t with
  | var ?n =>
      let _ := assert_is_constant_nat n in
      let name := eval cbn in (f n) in
      constr:(@named_var _ n name)
  | func ?fu ?v =>
      let map_fun := annotate_term f in
      let v' := map_ltac v map_fun in
      constr:(func fu v')
  | _ => t
  end. *)

Ltac annotate_form' f idx phi :=
  match phi with
  | falsity => falsity
  | atom ?P ?v =>
      let map_fun := annotate_term f in
      let v' := map_ltac v map_fun in
      constr:(atom P v')
  | bin ?op ?psi1 ?psi2 => 
      let psi1' := annotate_form' f idx psi1 in
      let psi2' := annotate_form' f idx psi2 in
      constr:(bin op psi1' psi2')
  | quant ?op ?psi =>
      let name := eval cbn in ("x" ++ nat_to_string idx) in
      let id := string_to_ident name in
      (* Check if identifier is already used *)
      match phi with
      | _ => 
          let _ := eval cbv in ltac:(assert (id := 0); clear id; exact 0) in
          let ident_name := to_ident_name id in
          let f' := constr:(fun n => match n with 0 => ident_name | S n' => f n' end) in
          let psi' := annotate_form' f' (S idx) psi in
          constr:(named_quant op ident_name psi')
      | _ => annotate_form' f (S idx) phi
      end
  (* If we don't have a concrete logic operator, it could be a
   * function call like `is_union $0 $1`. Also annotate those
   * arguments *)
  | _ => 
      match phi with
      | context C[ var ?n ] => 
          let _ := assert_is_constant_nat n in
          let ident_name := eval cbn in (f n) in
          let phi' := context C[ @named_var _ n ident_name ] in
          annotate_form' f idx phi'
      | _ => phi
      end
  end.

Ltac add_binder_names :=
  match goal with 
  | [ |- @pm _ _ _ ?p ?C ?phi ] =>
    let f := constr:(fun (n : nat) => Ident (fun _unknown => _unknown)) in
    let annotate_form := annotate_form' f 0 in
    let phi' := annotate_form phi in
    let C' := map_ltac C annotate_form in
    change (@pm _ _ _ p C' phi')
  | [ |- @tpm _ _ _ ?p ?C ?phi ] =>
    let f := constr:(fun (n : nat) => Ident (fun _unknown => _unknown)) in
    let annotate_form := annotate_form' f 0 in
    let phi' := annotate_form phi in
    let C' := map_ltac C annotate_form in
    change (@tpm _ _ _ p C' phi')
  end.
Ltac update_binder_names := unfold named_quant; unfold named_var; add_binder_names.




(** Proof Mode: *)

Notation "" := cnil (only printing).
Notation "A" := (cblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (ccons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Notation "" := tnil (only printing).
Notation "A" := (tblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (tcons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Notation "∀ x .. y , phi" := (named_quant All x ( .. (named_quant All y phi) .. )) (at level 50, only printing,
  format "'[' '∀'  '/  ' x  ..  y ,  '/  ' phi ']'").
Notation "∃ x .. y , phi" := (named_quant Ex x ( .. (named_quant Ex y phi) .. )) (at level 50, only printing,
  format "'[' '∃'  '/  ' x  ..  y ,  '/  ' phi ']'").

Notation "x" := (named_var (Ident (fun x => x))) (at level 1, only printing).

Notation "C '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm C phi)
  (at level 1, left associativity,
  format " C '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).

Notation "T '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (tpm T phi)
  (at level 1, left associativity,
  format " T '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).


(* Tactics to toggle proof mode *)
Ltac fstart := 
  match goal with 
  | [ |- @prv _ _ _ ?p ?A ?phi ] => let C := create_context A in change (@pm _ _ _ p C phi)
  | [ |- @tprv _ _ _ ?p ?T ?phi ] => let C := create_context T in change (@tpm _ _ _ p C phi)
  end;
  add_binder_names.
Ltac fstop := 
  match goal with 
  | [ |- @pm _ _ _ ?p ?C ?phi ] => change (@prv _ _ _ p C phi)
  | [ |- @tpm _ _ _ ?p ?C ?phi ] => change (@tprv _ _ _ p C phi)
  end;
  unfold pm in *; unfold cnil; unfold ccons;unfold cblackbox; 
  unfold tpm in *; unfold tnil; unfold tcons;unfold tblackbox; 
  unfold named_quant; unfold named_var.




(** Compatability tactics: *)

(* All the tactics defined below work with the original `prv` type.
 * The following tactic lifts them to be compatible with `pm`.
 *
 * Every tactic must have an additional argument where the current
 * context is filled in if the proof mode is active, and `cnil` 
 * otherwise. *)
Ltac make_compatible tac :=
  match goal with
  | [ |- prv ?A _ ] => tac A
  | [ |- tprv ?T _ ] => tac T
  | [ |- @pm _ _ _ ?p ?C _ ] => 
      fstop; 
      tac C;
      match goal with 
      | [ |- pm _ _ ?G ] => change (@pm _ _ _ p C G) 
      | [ |- prv _ ?G ] => change (@pm _ _ _ p C G)
      | _ => idtac 
      end;
      try update_binder_names (* [try] because some tactics add normal Coq goals *)
  | [ |- @tpm _ _ ?p ?C _ ] => 
      fstop;
      tac C;
      match goal with 
      | [ |- tprv _ ?G ] => change (@tpm _ _ p C G)
      | _ => idtac 
      end;
      try update_binder_names (* [try] because some tactics add normal Coq goals *)
  end.


(* [assert] and [enough] that are compatible with all proof modes.
 * This way we can avoid matching on the goal each time. *)
Ltac assert_compat' phi H :=
  match goal with
  | [ |- ?C ⊢ _ ] => assert (@prv _ _ _ C phi) as H
  | [ |- ?C ⊩ _ ] => assert (@tprv _ _ _ C phi) as H
  | [ |- @pm _ _ _ _ ?C _ ] => assert (@pm _ _ _ _ C phi) as H
  | [ |- @tpm _ _ _  _ ?C _ ] => assert (@tpm _ _ _ _ C phi) as H
  end.
Tactic Notation "assert_compat" constr(phi) := let H := fresh in assert_compat' phi H.
Tactic Notation "assert_compat" constr(phi) "as" ident(H) := assert_compat' phi H.
Tactic Notation "assert_compat" constr(phi) "by" tactic(tac) := let H := fresh in assert_compat' phi H; [tac|].
Tactic Notation "assert_compat" constr(phi) "as" ident(H) "by" tactic(tac) := assert_compat' phi H; [tac|].

Ltac enough_compat' phi H :=
  match goal with
  | [ |- ?C ⊢ _ ] => enough (@prv _ _ _ C phi) as H
  | [ |- ?C ⊩ _ ] => enough (@tprv _ _ _ C phi) as H
  | [ |- @pm _ _ _ _ ?C _ ] => enough (@pm _ _ _ _ C phi) as H
  | [ |- @tpm _ _ _ _ ?C _ ] => enough (@tpm _ _ _ _ C phi) as H
  end.
Tactic Notation "enough_compat" constr(phi) := let H := fresh in enough_compat' phi H.
Tactic Notation "enough_compat" constr(phi) "as" ident(H) := enough_compat' phi H.
Tactic Notation "enough_compat" constr(phi) "by" tactic(tac) := let H := fresh in enough_compat' phi H; [tac|].
Tactic Notation "enough_compat" constr(phi) "as" ident(H) "by" tactic(tac) := enough_compat' phi H; [tac|].

Ltac apply_compat' H1 H2 :=
  match goal with
  | [ |- _ ⊢ _ ] => apply H1
  | [ |- _ ⊩ _ ] => apply H2
  end.
Ltac apply_compat_in H1 H2 H :=
  match goal with
  | [ |- _ ⊢ _ ] => apply H1 in H
  | [ |- _ ⊩ _ ] => apply H2 in H
  end.
Tactic Notation "apply_compat" constr(H1) constr(H2) := apply_compat' H1 H2.
Tactic Notation "apply_compat" constr(H1) constr(H2) "in" hyp(H) := apply_compat_in H1 H2 H.


(* Return the context of the goal or a hypothesis *)
Ltac get_context_goal :=
  match goal with
  | [ |- ?C ⊢ _ ] => C
  | [ |- ?C ⊩ _ ] => C
  | [ |- pm ?C _ ] => C
  | [ |- tpm ?C _ ] => C
  end.
Ltac get_context_hyp H :=
  match type of H with
  | ?C ⊢ _ => C
  | ?C ⊩ _ => C
  | pm ?C _ => C
  | tpm ?C _ => C
  end.
Tactic Notation "get_context" := get_context_goal.
Tactic Notation "get_context" hyp(H) := get_context_hyp H.

(* Return the formula inside the goal or a hypothesis *)
Ltac get_form_goal :=
  match goal with
  | [ |- _ ⊢ ?phi ] => phi
  | [ |- _ ⊩ ?phi ] => phi
  | [ |- pm _ ?phi ] => phi
  | [ |- tpm _ ?phi ] => phi
  end.
Ltac get_form_hyp H :=
  match type of H with
  | _ ⊢ ?phi => phi
  | _ ⊩ ?phi => phi
  | pm _ ?phi => phi
  | tpm _ ?phi => phi
  end.
Tactic Notation "get_form" := get_form_goal.
Tactic Notation "get_form" hyp(H) := get_form_hyp H.




(** Simplification: *)

(* Spimplify terms that occur during specialization *)
Ltac simpl_subst_hyp H :=
  cbn in H;
  repeat match type of H with
  | context C[fun x => $(S x)] => let H' := context C[↑] in change H' in H
  | context C[S >> var] => let H' := context C[↑] in change H' in H
  end;
  try rewrite !up_term in H;
  try rewrite !subst_term_shift in H;
  try rewrite !up_form in H;
  try rewrite !subst_shift in H;
  (* Evaluate `(S >> var) 4` into `$5`. [cbn] doesn't do it, unfold instead *)
  unfold ">>";
  (* But this also turns `↑` into `fun x => $(S x)` *)
  repeat match goal with
  | [ |- context C[fun x => $(S x)] ] => let H' := context C[↑] in change H' in H
  end;
  (* Domain specific simplifications: *)
  custom_fold;
  custom_simpl.

Ltac simpl_subst_goal :=
  cbn;
  repeat match goal with
  | [ |- context C[fun x => $(S x)] ] => let G := context C[↑] in change G
  | [ |- context C[S >> var] ] => let G := context C[↑] in change G
  end;
  try rewrite !up_term;
  try rewrite !subst_term_shift;
  try rewrite !up_form;
  try rewrite !subst_shift;
  (* Evaluate `(S >> var) 4` into `$5`. [cbn] doesn't do it, unfold instead *)
  unfold ">>";
  (* But this also turns `↑` into `fun x => $(S x)` *)
  repeat match goal with
  | [ |- context C[fun x => $(S x)] ] => let G := context C[↑] in change G
  end;
  (* Domain specific simplifications: *)
  custom_fold;
  custom_simpl.

Tactic Notation "simpl_subst" hyp(H) := (simpl_subst_hyp H).
Tactic Notation "simpl_subst" := (simpl_subst_goal).


(* Syntactically evaluate `mapT f (T ⋄ a ⋄ b ⋄ c)` to
 * `(mapT f T) ⋄ f a ⋄ f b ⋄ f c` like it would happen using
 * [cbn] for map in normal lists. *)
Ltac eval_mapT M :=
  match M with
  | mapT ?f (extend ?T ?a) => let T' := eval_mapT (mapT f T) in constr:(extend T' (f a))
  | mapT ?f (tcons ?s ?a ?T) => let T' := eval_mapT (mapT f T) in constr:(tcons s (f a) T')
  | mapT ?f (tblackbox ?T) => constr:(tblackbox (mapT f T))
  | _ => M
  end.

Lemma mapT_step `{s1 : funcs_signature, s2 : preds_signature, ff : falsity_flag, p : peirce} f a T1 T2 :
  subset_T T1 (mapT f T2) -> subset_T (extend T1 (f a)) (mapT f (extend T2 a)).
Proof.
  intros H psi H1. destruct H1 as [H1|H1].
  - destruct (H psi H1) as [rho [H2 H3]]. exists rho. split. now left. assumption.
  - exists a. split. now right. auto.
Qed.

(* Replace `mapT f (T ⋄ a ⋄ b ⋄ c)` in the context with 
 * `(mapT f T) ⋄ f a ⋄ f b ⋄ f c`. *)
Ltac simpl_context_mapT :=
  match goal with 
  | [ |- tprv ?T ?phi ] =>
      let T' := eval_mapT T in
      let X := fresh in
      enough (tprv T' phi) as X; [ 
        eapply Weak; [now apply X | repeat apply mapT_step; apply subset_refl ]
      |]
  | [ |- tpm ?T ?phi ] =>
      let T' := eval_mapT T in
      let X := fresh in
      enough (tpm T' phi) as X; [ 
        eapply Weak; [now apply X | repeat apply mapT_step; apply subset_refl ]
      |]
  end.









(** End user proof tactics: *)

Ltac ctx := make_compatible ltac:(fun _ => apply Ctx; firstorder).

Ltac fexfalso := make_compatible ltac:(fun _ => apply Exp).
Ltac fsplit := make_compatible ltac:(fun _ => apply CI).
Ltac fleft := make_compatible ltac:(fun _ => apply DI1).
Ltac fright := make_compatible ltac:(fun _ => apply DI2).




(* 
 * [fintro], [fintros] 
 * 
 * Similar to Coq. Identifiers need to be given as strings (e.g. 
 * [fintros "H1" "H2"]). With "?" you can automatically generate
 * a name (e.g. [fintros "?" "H"]).
 * 
 * Now also handles intro patterns! For now unneccessary spaces
 * are not alowed in intro patterns. E.g. instead of "[H1 | H2]",
 * write "[H1|H2]".
 *)


(* Intro pattern parsing. This gets its own section to avoid 
 * importing Ascii globally. *)
Section IntroPattern.
  Import Ascii.

  Inductive intro_pattern :=
    | patId : string -> intro_pattern
    | patAnd : intro_pattern -> intro_pattern -> intro_pattern
    | patOr : intro_pattern -> intro_pattern -> intro_pattern.

  Fixpoint read_name s := match s with
  | String "]" s' => ("", String "]" s')
  | String " " s' => ("", String " " s')
  | String "|" s' => ("", String "|" s')
  | String c s' => let (a, s'') := read_name s' in (String c a, s'')
  | EmptyString => ("", EmptyString)
  end.

  Fixpoint parse_intro_pattern' s fuel := match fuel with
  | 0 => (None, s)
  | S fuel' =>
    match s with
    | String ("[") s' => 
        match parse_intro_pattern' s' fuel' with
        | (Some p1, String "|" s'') => match parse_intro_pattern' s'' fuel' with
                                      | (Some p2, String "]" s''') => (Some (patOr p1 p2), s''')
                                      | _ => (None, "")
                                      end
        | (Some p1, String " " s'') => match parse_intro_pattern' s'' fuel' with
                                      | (Some p2, String "]" s''') => (Some (patAnd p1 p2), s''')
                                      | _ => (None, "")
                                      end
        | _ => (None, "")
        end
      | String ("]") s' => (Some (patId "?"), String "]" s')
      | String " " s' => (Some (patId "?"), String " " s')
      | String "|" s' => (Some (patId "?"), String "|" s')
      | EmptyString => (None, EmptyString)
      | s => let (a, s') := read_name s in (Some (patId a), s')
    end
  end.
  Definition parse_intro_pattern s := fst (parse_intro_pattern' s 100).

End IntroPattern.

Ltac create_pattern T :=
  match T with
  | ?t ∧ ?s => constr:(patAnd (patId "?") (patId "?"))
  | ?t ∨ ?s => constr:(patOr (patId "?") (patId "?"))
  | ∃ ?t => constr:(patAnd (patId "?") (patId "?"))
  | named_quant Ex _ ?t => constr:(patAnd (patId "?") (patId "?"))
  | _ => constr:(patId "?")
  end.

Ltac create_deep_pattern T :=
  match T with
  | ?t ∧ ?s =>
    let p1 := create_deep_pattern t in
    let p2 := create_deep_pattern s in
    constr:(patAnd p1 p2)
  | ?t ∨ ?s =>
    let p1 := create_deep_pattern t in
    let p2 := create_deep_pattern s in
    constr:(patOr p1 p2)
  | ∃ ?t =>
    let p1 := constr:(patId "?") in
    let p2 := create_deep_pattern t in
    constr:(patAnd p1 p2)
  | named_quant Ex _ ?t =>
    let p1 := constr:(patId "?") in
    let p2 := create_deep_pattern t in
    constr:(patAnd p1 p2)
  | _ => constr:(patId "?")
  end.


Section Fintro.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  Variable p : peirce.

  Lemma intro_and_destruct A s t G :
    A ⊢ (s ~> t ~> G) -> A ⊢ (s ∧ t ~> G).
  Proof.
    intros. now apply switch_conj_imp.
  Qed.

  Lemma intro_or_destruct A s t G :
    A ⊢ (s ~> G) -> A ⊢ (t ~> G) -> A ⊢ (s ∨ t ~> G).
  Proof.
    intros Hs Ht. apply II. eapply DE. ctx.
    eapply Weak in Hs. eapply IE. apply Hs. ctx. firstorder.
    eapply Weak in Ht. eapply IE. apply Ht. ctx. firstorder.
  Qed.

  Context {eq_dec_Funcs : eq_dec syms}.
  Context {eq_dec_Preds : eq_dec preds}.

  Lemma intro_and_destruct_T T s t G :
    T ⊩ (s ~> t ~> G) -> T ⊩ (s ∧ t ~> G).
  Proof.
    intros. apply II. apply (IE _ t). apply (IE _ s).
    eapply Weak. apply H. firstorder.
    eapply CE1, Ctx; firstorder.
    eapply CE2, Ctx; firstorder.
  Qed.

  Lemma intro_or_destruct_T T s t G :
    T ⊩ (s ~> G) -> T ⊩ (t ~> G) -> T ⊩ (s ∨ t ~> G).
  Proof.
    intros Hs Ht. apply II. eapply DE. ctx.
    eapply Weak in Hs. eapply IE. apply Hs. ctx. firstorder.
    eapply Weak in Ht. eapply IE. apply Ht. ctx. firstorder.
  Qed.

  Lemma subst_zero phi x :
    $0 = x -> phi = phi[fun n => match n with 0 => x | S n => $(S n) end].
  Proof.
    intros. symmetry. apply subst_id. intros [|]; cbn. now rewrite H. reflexivity.
  Qed.

  Lemma subst_zero_term t x :
    $0 = x -> t`[fun n => match n with 0 => x | S n => $(S n) end] = t.
  Proof.
    intros. apply subst_term_id. intros [|]; cbn. now rewrite H. reflexivity.
  Qed.

End Fintro.


(* Check if the name `id` doesn't already occur in the context or
 * create a new name if `id = "?"`. *)
Ltac hypname_from_pattern C id :=
  match id with 
  | "?" => new_name "H" C
  | _ => match lookup C id with
    | @None => id
    | @Some _ _ => let msg := eval cbn in ("Identifier already used: " ++ id) in fail 7 msg
    end
  end.

(* For variable names that are introduced with ∀ this gets infinitely
 * more difficult.
 * Ltac doesn't have an easy way to convert a Coq string into an identifier.
 * I found this snippet using Ltac2 that is used in the Iris proof
 * mode, but doesn't seem that stable. 
 * See https://github.com/coq/coq/issues/7412 
 *
 * Nonetheless I am going to use it, but split up the intro tactic into
 * ident and hyp intro. I use tactic notation at the end to also support
 * intro with a 'real' Coq ident instead of a string. This should keep
 * working if this hack breaks down. *)
Require Import Undecidability.FOL.Proofmode.Ltac2StringIdent.
Ltac varname_from_pat pat :=
  match pat with 
  | patId "?" => fresh "x"
  | patId ?id => string_to_ident id
  end.


Ltac fintro_ident x :=
  let H := fresh "H" in
  match goal with
  | [ |- _ ⊢ ∀ ?t ] => 
    apply AllI;
    edestruct nameless_equiv_all as [x H];
    apply H; clear H;
    simpl_subst
  | [ |- @pm _ _ _ ?p ?C (named_quant All _ ?t) ] =>
    apply AllI;
    edestruct nameless_equiv_all as [x H];
    apply H; clear H;
    simpl_subst;
    match goal with [ |- prv _ ?t'] => change (@pm _ _ _ p C t') end;
    update_binder_names
  | [ |- _ ⊩ ∀ ?t ] =>
    let E := fresh "E" in
    apply AllI;
    assert (exists x, $0 = x) as [x E] by (now exists ($0));
    rewrite (subst_zero t x E);
    simpl_context_mapT;
    simpl_subst;
    repeat (try rewrite subst_zero_term; [| apply E]);
    clear E
  | [ |- @tpm _ _ _ ?p ?C (named_quant All _ ?t) ] =>
    let E := fresh "E" in
    apply AllI;
    assert (exists x, $0 = x) as [x E] by (now exists ($0));
    rewrite (subst_zero t x E);
    simpl_context_mapT;
    simpl_subst;
    repeat (try rewrite subst_zero_term; [| apply E]);
    clear E;
    update_binder_names
  | _ =>
    (* Unfold definitions to check if there are hidden ∀ underneath. 
     * Also perform simplification and fix names if the definition
     * does something nasty. *)
    progress custom_unfold; simpl_subst; try update_binder_names;
    custom_unfold; (* Unfold again because [simpl_subst] folds *)
    fintro_ident x;
    custom_fold
  end.


Ltac fintro_pat' pat :=
  match pat with
  | patAnd ?p1 ?p2 => (* Existential *)
      make_compatible ltac:(fun C =>
        apply II; eapply ExE; [ apply Ctx; now left |
          let x := varname_from_pat p1 in
          let H := fresh "H" in
          edestruct nameless_equiv_ex as [x H];
          apply H; clear H; cbn; simpl_subst; apply -> imps;
          apply (Weak C); [| firstorder] ]
      ); 
      fintro_pat' p2
  | patAnd ?p1 ?p2 => (* Conjunction *)
      make_compatible ltac:(fun _ => 
        match goal with 
        | [ |- prv _ _ ] => apply intro_and_destruct
        | [ |- tprv _ _ ] => apply intro_and_destruct_T
        end
      ); 
      fintro_pat' p1; fintro_pat' p2  
  | patOr ?p1 ?p2 =>
      make_compatible ltac:(fun _ => 
        match goal with 
        | [ |- prv _ _ ] => apply intro_or_destruct
        | [ |- tprv _ _ ] => apply intro_or_destruct_T
        end
      );
      [fintro_pat' p1 | fintro_pat' p2]
  | patId ?id =>
      match goal with 
      | [ |- ?A ⊢ ∀ ?t ] => let x := varname_from_pat pat in fintro_ident x
      | [ |- ?A ⊩ ∀ ?t ] => let x := varname_from_pat pat in fintro_ident x
      | [ |- ?A ⊢ (?s ~> ?t) ] => apply II
      | [ |- ?A ⊩ (?s ~> ?t) ] => apply II
      (* Special care for intro in proof mode *)
      | [ |- @pm _ _ _ ?p ?C (named_quant All _ ?t) ] => let x := varname_from_pat pat in fintro_ident x
      | [ |- @tpm _ _ _ ?p ?C (named_quant All _ ?t) ] => let x := varname_from_pat pat in fintro_ident x
      | [ |- @pm _ _ _ ?p ?C (?s ~> ?t) ] => apply II; let name := hypname_from_pattern C id in change (@pm _ _ _ p (ccons name s C) t)
      | [ |- @tpm _ _ _ ?p ?C (?s ~> ?t) ] => apply II; let name := hypname_from_pattern C id in change (@tpm _ _ _ p (tcons name s C) t)
      | _ =>
        (* Unfold definitions to check if there are hidden ∀ underneath. 
         * Also perform simplification and fix names if the definition
         * does something nasty. *)
        progress custom_unfold; simpl_subst; try update_binder_names;
        custom_unfold; (* Unfold again because [simpl_subst] folds *)
        fintro_pat' pat;
        custom_fold
      end
  end.

Ltac fintro_pat intro_pat := 
  let pat := match intro_pat with
    | "..." => match get_form_goal with ?t ~> _ => create_deep_pattern t end
    | _ => match eval cbn in (parse_intro_pattern intro_pat) with
            | Some ?p => p
            | None => let msg := eval cbn in ("Invalid intro pattern: " ++ intro_pat) in fail 2 msg
            end
  end in fintro_pat' pat.

Tactic Notation "fintro" := fintro_pat constr:("?").
Tactic Notation "fintro" constr(H) := fintro_pat H.
Tactic Notation "fintro" ident(x) := fintro_ident x.

Tactic Notation "fintros" := repeat fintro.

Tactic Notation "fintros" constr(H1) := fintro_pat H1.
Tactic Notation "fintros" ident(H1) := fintro_ident H1.

Tactic Notation "fintros" constr(H1) constr(H2) := fintro_pat H1; fintro_pat H2.
Tactic Notation "fintros" ident(H1) constr(H2) := fintro_ident H1; fintro_pat H2.
Tactic Notation "fintros" constr(H1) ident(H2) := fintro_pat H1; fintro_ident H2.
Tactic Notation "fintros" ident(H1) ident(H2) := fintro_ident H1; fintro_ident H2.

Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) := fintro_pat H1; fintro_pat H2; fintro_pat H3.
Tactic Notation "fintros" ident(H1) constr(H2) constr(H3) := fintro_ident H1; fintro_pat H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) ident(H2) constr(H3) := fintro_pat H1; fintro_ident H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) constr(H2) ident(H3) := fintro_pat H1; fintro_pat H2; fintro_ident H3.
Tactic Notation "fintros" ident(H1) ident(H2) constr(H3) := fintro_ident H1; fintro_ident H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) ident(H2) ident(H3) := fintro_pat H1; fintro_ident H2; fintro_ident H3.
Tactic Notation "fintros" ident(H1) ident(H2) ident(H3) := fintro_ident H1; fintro_ident H2; fintro_ident H3.

Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) constr(H4) := fintro_pat H1; fintro_pat H2; fintro_pat H3; fintro_pat H4.
Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) := fintro_pat H1; fintro_pat H2; fintro_pat H3; fintro_pat H4; fintro_pat H4.






(* High level context managment *)

(* Tactic Notation "is_hyp" hyp(H) := idtac. *)
Ltac is_hyp H := match type of H with ?t => match type of t with Prop => idtac end end.

(* Check wether T is a hypothesis, a context index, a context formula
 * or a context name and put it into hypothesis H. *)
 Ltac turn_into_hypothesis T H contxt := 
  tryif is_hyp T
  then assert (H := T)  (* Hypothesis *)
  else match goal with 
  | [ |- @prv _ _ _ ?p ?C _ ] => 
      match type of T with
      | form => assert (@prv _ _ _ p C T) as H by ctx  (* Explicit form *)
      | nat => let T' := nth C T in assert (@prv _ _ _ p C T') as H by ctx  (* Idx in context *)
      | string => match lookup contxt T with  (* Context name *)
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
        | @Some _ ?n => let T' := nth C n in assert (@prv _ _ _ p C T') as H by ctx
        end
      end
  | [ |- @tprv _ _ _ ?p ?C _ ] => 
      match type of T with
      | form => assert (@tprv _ _ _ p C T) as H by ctx  (* Explicit form *)
      | nat => let T' := nth C T in assert (@tprv _ _ _ p C T') as H by ctx  (* Idx in context *)
      | string => match lookup contxt T with  (* Context name *)
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
        | @Some _ ?n => let T' := nth C n in assert (@tprv _ _ _ p C T') as H by ctx
        end
      end
  end.

(* Replace the context entry T_old with formula `phi` in 
 * `H_new : X ⊢ phi` *)
Ltac replace_context T_old H_new :=
  let C := get_context_goal in
  let phi := get_form_hyp H_new in
  let psi := get_form_goal in
  let X := fresh in
  (enough_compat (phi ~> psi) as X by eapply (IE _ _ _ X); apply H_new);
  let C' := match type of T_old with
    | nat => replace_ltac C T_old phi
    | form => map_ltac C ltac:(fun f => match f with T_old => phi | ?psi => psi end)
    | string => match lookup C T_old with
      | @None => let msg := eval cbn in ("Unknown identifier: " ++ T_old) in fail 4 msg
      | @Some _ ?n => replace_ltac C n phi
      end
  end in
  fintro; apply (Weak C'); [| firstorder].





(* 
 * [fspecialize (H x1 x2 ... xn)], [fspecialize H with x1 x2 ... xn] 
 * 
 * Specializes a Coq hypothesis `H` of the form `X ⊢ ∀∀...∀ p1 ~> ... ~> pn ~> g`
 * with `x1, x2, ..., xn`.
 *)

Ltac fspecialize_list H A := 
  match A with
  | [] => simpl_subst H
  | ?x::?A' =>
      (* Don't match for ∀ or ~>, because it might be folded (e.g. ax_symm) *)
      tryif (
        let H' := fresh "H" in
        make_compatible ltac:(fun C => turn_into_hypothesis x H' C);
        apply (fun H => IE _ _ _ H H') in H;
        clear H'
      ) then idtac
      else (
        (* For some reason we cannot directly [apply (AllE _ x)]
          if x contains ⊕, σ, etc. But evar seems to work. *)
        let x' := fresh "x" in 
        eapply (AllE _ ?[x']) in H; 
        instantiate (x' := x)
      );
      fspecialize_list H A'
  end.

(* Specialize in context *)
Ltac fspecialize_context T A :=
  let H := fresh "H" in
  make_compatible ltac:(fun C => turn_into_hypothesis T H C);
  fspecialize_list H A;
  replace_context T H;
  try update_binder_names;
  try simpl_subst;
  clear H.

Ltac fspecialize' T A := tryif is_hyp T then fspecialize_list T A else fspecialize_context T A.

Tactic Notation "fspecialize" "(" constr(H) constr(x1) ")" := fspecialize' H constr:([x1]).
Tactic Notation "fspecialize" "(" constr(H) constr(x1) constr(x2) ")" := fspecialize' H constr:([x1; x2]).
Tactic Notation "fspecialize" "(" constr(H) constr(x1) constr(x2) constr(x3) ")" :=  fspecialize' H constr:([x1;x2;x3]).

Tactic Notation "fspecialize" constr(H) "with" constr(x1) := fspecialize' H constr:([x1]).
Tactic Notation "fspecialize" constr(H) "with" constr(x1) constr(x2) := fspecialize' H constr:([x1;x2]).
Tactic Notation "fspecialize" constr(H) "with" constr(x1) constr(x2) constr(x3) := fspecialize' H constr:([x1;x2;x3]).




(*
 * [fapply (H x1 ... xn)], [feapply (H x1 ... xn)]
 *  
 * Works on
 * - Coq hypothesis by name
 * - Formula in in ND context by index (e.g. [fapply 3])
 * - Explicit formula type in the context (e.g. [fapply ax_symm])
 * - Name of a context assumption in proof mode (e.g. [fapply "H2"])
 *)

Section Fapply.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  Variable p : peirce.

  Lemma fapply_equiv_l A phi psi :
    A ⊢ (phi ↔ psi) -> A ⊢ phi -> A ⊢ psi.
  Proof.
    intros. apply (IE _ phi). eapply CE1. apply H. apply H0.
  Qed.

  Lemma fapply_equiv_r A phi psi :
    A ⊢ (phi ↔ psi) -> A ⊢ psi -> A ⊢ phi.
  Proof.
    intros. apply (IE _ psi). eapply CE2. apply H. apply H0.
  Qed.

  Context {eq_dec_Funcs : eq_dec syms}.
  Context {eq_dec_Preds : eq_dec preds}.

  Lemma fapply_equiv_l_T A phi psi :
    A ⊩ (phi ↔ psi) -> A ⊩ phi -> A ⊩ psi.
  Proof.
    intros. apply (IE _ phi). eapply CE1. apply H. apply H0.
  Qed.

  Lemma fapply_equiv_r_T A phi psi :
    A ⊩ (phi ↔ psi) -> A ⊩ psi -> A ⊩ phi.
  Proof.
    intros. apply (IE _ psi). eapply CE2. apply H. apply H0.
  Qed.
End Fapply.

(* Helper tactics: *)

(* [fapply_without_quant] takes a formula `H : X ⊢ p1 ~> p2 ~> ... ~> pn ~> g`
 * without leading quantifiers. It solves the goal `X ⊢ g` by 
 * adding subgoals for each premise `p1, p2, ..., pn`.
 *
 * Also supports formulas of Type `H : X ⊢ ... ~> (pn ↔ g)` or 
 * `H : X ⊢ ... ~> (g ↔ pn)`.
 *
 * If ∀-quantifiers occur inbetween, they are instantiated with evars. *)
Ltac fapply_without_quant H :=
  tryif exact H then idtac else
  let Hs := fresh "Hs" in 
  let Ht := fresh "Ht" in 
  match get_form_hyp H with
  | ?s ~> ?t => 
    match goal with 
    | [ |- @prv _ _ _ ?p ?A _ ] =>
        enough (@prv _ _ _ p A s) as Hs; 
        [ assert (@prv _ _ _ p A t) as Ht; 
          [ apply (IE _ _ _ H Hs) | fapply_without_quant Ht; clear Hs; clear Ht ] 
        | ]
    | [ |- @tprv _ _ _ ?p ?A _ ] =>
        enough (@tprv _ _ _ p A s) as Hs; 
        [ assert (@tprv _ _ _ p A t) as Ht; 
          [ apply (IE _ _ _ H Hs) | fapply_without_quant Ht; clear Hs; clear Ht ] 
        | ]
    end
  
  (* Handle application of equivalence. It would be nice to use match
   * to check which side matches, but it doesn't work because of evars.
   * Therefore simply try both options. *)
  | _ ↔ _ =>
    match goal with
    | [ |- _ ⊢ _] => tryif apply (fapply_equiv_l _ _ _ _ H) then idtac else apply (fapply_equiv_r _ _ _ _ H)
    | [ |- _ ⊩ _] => tryif apply (fapply_equiv_l_T _ _ _ _ H) then idtac else apply (fapply_equiv_r_T _ _ _ _ H)
    end
  
  (* Quantifiers are instantiated with evars *)
  | ∀ _ => eapply AllE in H; simpl_subst H; fapply_without_quant H

  (* If we don't find something useful, try unfolding definitions to 
   * check if there is something hidden underneath. Also perform 
   * simplification if the definition does something nasty. *)
  | _ =>
    progress custom_unfold; simpl_subst H;
    custom_unfold; (* Unfold again because [simpl_subst] folds *)
    fapply_without_quant H;
    custom_fold
  end.

Ltac instantiate_evars H := repeat eassert (H := H _); repeat eapply AllE in H.

(* If `H` has the type `P1 -> P2 -> ... -> Pn -> (A ⊢ ϕ)`, this
 * tactic adds goals for `P1, P2, ..., Pn` and specializes `H`. *)
Ltac assert_premises H :=
  match type of H with
  | ?A -> ?B => 
      let H' := fresh "H" in assert A as H';
      [|specialize (H H'); clear H'; assert_premises H ]
  | forall _, _ => eassert (H := H _); assert_premises H
  | _ => idtac
  end.

Ltac feapply' T A := fun contxt =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` contains further Coq premises before the formula 
   * statement, we add them as additional goals. *)
  assert_premises H;
  (* Only try here, because it would fail on these additional goals. *)
  try (
    fspecialize_list H A;
    instantiate_evars H;
    simpl_subst H;
    let C := get_context_goal in 
    eapply (Weak _ C) in H; [| firstorder];
    fapply_without_quant H;
    (* [fapply_without_quant] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals;
    custom_fold
  );
  clear H.

Ltac fapply' T A contxt :=
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` contains further Coq premises before the formula 
   * statement, we add them as additional goals. *)
  assert_premises H;
  (* Only try here, because it would fail on these additional goals. *)
  try (
    fspecialize_list H A; 
    instantiate_evars H; 
    simpl_subst H;
    let C := get_context_goal in
    eapply (Weak _ C) in H; [| firstorder];
    fapply_without_quant H;
    (* [fapply_without_quant] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals;
    custom_fold;
    (* Evars should only be used for unification in [fapply].
     * Therefore reject, if there are still evars visible. *)
    (* TODO: This is not optimal. If the goal contains evars, 
     * H might still contain evars after unification and we would fail. *)
    tryif has_evar ltac:(type of H) 
    then fail 3 "Cannot find instance for variable. Try feapply?" 
    else clear H
  );
  try clear H.


Tactic Notation "feapply" constr(T) := make_compatible ltac:(feapply' T constr:([] : list form)).
Tactic Notation "feapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(feapply' T constr:([x1])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(feapply' T constr:([x1;x2])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(feapply' T constr:([x1;x2;x3])).

Tactic Notation "fapply" constr(T) := make_compatible ltac:(fapply' T constr:([] : list form)).
Tactic Notation "fapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(fapply' T constr:([x1])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(fapply' T constr:([x1;x2])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fapply' T constr:([x1;x2;x3])).

(* If the term to apply is the result of a function call
 * (like `PA_induction (...)`), this needs to be differentiated
 * from the other parenthesis notation.
 *
 * To make it work, you need to put double parenthesis: [fapply ((PA_induction (...)))] *)
Tactic Notation "feapply" "(" constr(T) ")" := make_compatible ltac:(feapply' T constr:([] : list form)).
Tactic Notation "fapply" "(" constr(T) ")" := make_compatible ltac:(fapply' T constr:([] : list form)).






(*
 * [fapply (H x1 ... xn) in Hyp ], [feapply (H x1 ... xn) in Hyp]
 *  
 * Works on
 * - Coq hypothesis by name
 * - Formula in in ND context by index (e.g. [fapply 3 in 0])
 * - Explicit formula type in the context (e.g. [fapply ax_symm in (x ~> y)])
 * - Name of a context assumption in proof mode (e.g. [fapply "H2" in "H1"])
 *)


(* Takes two formulas `H_imp : X ⊢ p1 ~> ... ~> pn ~> q`
 * `H_hyp : X ⊢ pn`. It also takes `T_hyp` which identifies `H_hyp`
 * in the context.
 * It changes the assumption `pn` in the context into `q` and adds
 * additional goals for each premise `p1, p2, ..., pn`.
 *
 * Also supports formulas of Type `H_imp : X ⊢ ... ~> (pn ↔ q)` or 
 * `H_imp : X ⊢ ... ~> (q ↔ pn)`.
 *
 * If ∀-quantifiers occur inbetween, they are instantiated with evars. *)
Ltac fapply_in_without_quant_in T_hyp H_imp H_hyp :=
  match get_form_hyp H_imp with
  | ?s ~> ?t =>
    let H_hyp' := fresh "H_hyp'" in
    tryif assert_compat t as H_hyp' by (feapply H_imp; apply H_hyp)
    then (replace_context T_hyp H_hyp'; clear H_hyp')
    else ( 
      (* Try to assert `s` as a goal for the user to prove and
       * check if we can apply `t`. *)
      let Hs := fresh "Hs" in
      let Ht := fresh "Ht" in
      (enough_compat s as Hs); [
        (assert_compat t as Ht by apply (IE _ _ _ H_imp Hs));
        (* replace_context T_imp Ht; *)
        fapply_in_without_quant_in T_hyp Ht H_hyp;
        clear Ht; clear Hs
      | ] )
  
  (* Handle application of equivalence. It would be nice to use match
   * to check which side matches, but it doesn't work because of evars.
   * Therefore simply try both options. *)
  | ?s ↔ ?t =>
    let H_hyp' := fresh "H_hyp'" in
    (tryif assert_compat t as H_hyp' by (feapply H_imp; apply H_hyp) then idtac
    else assert_compat s as H_hyp' by (feapply H_imp; apply H_hyp));
    replace_context T_hyp H_hyp'; clear H_hyp'
  
  (* Quantifiers are instantiated with evars *)
  | ∀ _ => instantiate_evars H_imp; fapply_in_without_quant_in T_hyp H_imp H_hyp

  (* If we don't find something useful, try unfolding definitions to 
    * check if there is something hidden underneath. Also perform 
    * simplification if the definition does something nasty. *)
  | _ =>
    progress custom_unfold; simpl_subst H_imp; simpl_subst H_hyp;
    custom_unfold; (* Unfold again because [simpl_subst] folds *)
    fapply_in_without_quant_in T_hyp H_imp H_hyp;
    custom_fold
  end.


Ltac feapply_in T_imp A T_hyp :=
  let H_imp := fresh "H_imp" in
  let H_hyp := fresh "H_hyp" in
  make_compatible ltac:(fun contxt =>
    turn_into_hypothesis T_imp H_imp contxt;
    turn_into_hypothesis T_hyp H_hyp contxt
  );
  (* If `H_imp` contains further Coq premises before the  
   * formula statement, we add them as additional goals. *)
  assert_premises H_imp;
  (* Only try here, because it would fail on these additional goals. *)
  try (
    let C := get_context_goal in 
    fspecialize_list H_imp A;
    instantiate_evars H_imp;
    simpl_subst H_imp;
    eapply (Weak _ C) in H_imp; [| firstorder];
    fapply_in_without_quant_in T_hyp H_imp H_hyp;
    (* [fapply_in_without_quant_in] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals;
    simpl_subst;
    try update_binder_names;
    clear H_imp; clear H_hyp
  ).

Ltac fapply_in T_imp A T_hyp :=
  feapply_in T_imp A T_hyp;
  (* Evars should only be used for unification in [fapply].
   * Therefore reject, if there are still evars visible. *)
  (* TODO: This is not optimal. If the goal contains evars, 
   * H might still contain evars after unification and we would fail. *)
  let C := get_context_goal in
  let phi := get_form_goal in
  tryif has_evar C then fail 3 "Cannot find instance for variable. Try feapply?" 
  else tryif has_evar phi then fail 3 "Cannot find instance for variable. Try feapply?" 
  else idtac.

Tactic Notation "feapply" constr(T_imp) "in" constr(T_hyp) := feapply_in T_imp constr:([] : list form) T_hyp.
Tactic Notation "feapply"  "(" constr(T_imp) constr(x1) ")" "in" constr(T_hyp) := feapply_in T_imp constr:([x1] : list form) T_hyp.
Tactic Notation "feapply" "(" constr(T_imp) constr(x1) constr(x2) ")" "in" constr(T_hyp) := feapply_in T_imp constr:([x1;x2] : list form) T_hyp.
Tactic Notation "feapply" "(" constr(T_imp) constr(x1) constr(x2) constr(x3) ")" constr(T_hyp) := feapply_in T_imp constr:([x1;x2;x3] : list form) T_hyp.

Tactic Notation "fapply" constr(T_imp) "in" constr(T_hyp) := fapply_in T_imp constr:([] : list form) T_hyp.
Tactic Notation "fapply"  "(" constr(T_imp) constr(x1) ")" "in" constr(T_hyp) := fapply_in T_imp constr:([x1] : list form) T_hyp.
Tactic Notation "fapply" "(" constr(T_imp) constr(x1) constr(x2) ")" "in" constr(T_hyp) := fapply_in T_imp constr:([x1;x2] : list form) T_hyp.
Tactic Notation "fapply" "(" constr(T_imp) constr(x1) constr(x2) constr(x3) ")" constr(T_hyp) := fapply_in T_imp constr:([x1;x2;x3] : list form) T_hyp.





(*
 * [fassert phi], [fassert phi as "H"]
 *
 * Similar to coq. Also supports intro patterns.
 *)

Section Fassert.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Lemma fassert_help `{peirce} A phi psi :
    A ⊢ phi -> A ⊢ (phi ~> psi) -> A ⊢ psi.
  Proof.
    intros H1 H2. eapply IE. exact H2. exact H1.
  Qed.

  Context {eq_dec_Funcs : eq_dec syms}.
  Context {eq_dec_Preds : eq_dec preds}.

  Lemma fassert_help_T `{peirce} A phi psi :
    A ⊩ phi -> A ⊩ (phi ~> psi) -> A ⊩ psi.
  Proof.
    intros H1 H2. eapply IE. exact H2. exact H1.
  Qed.
End Fassert.

Ltac fassert' phi := fun _ =>
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  match goal with
  | [ |- ?A ⊢ ?psi ] =>
    assert (A ⊢ phi) as H1; [ | 
      assert (A ⊢ (phi ~> psi)); [ clear H1 |
        apply (fassert_help A phi psi H1 H2)
      ]
    ]
  | [ |- ?A ⊩ ?psi ] =>
    assert (A ⊩ phi) as H1; [ | 
      assert (A ⊩ (phi ~> psi)); [ clear H1 |
        apply (fassert_help_T A phi psi H1 H2)
      ]
    ]
  end.

Tactic Notation "fassert" constr(phi) := (make_compatible ltac:(fassert' phi)); [| fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) := (make_compatible ltac:(fassert' phi)); [| fintro_pat H].
Tactic Notation "fassert" constr(phi) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro_pat H].





(*
 * [fdestruct H], [fdestruct H as "pattern"]
 *
 * Destructs an assumption into the ND context. Works on
 * - Coq hypothesis by name
 * - Formula in in ND context by index (e.g. [fdestruct 3])
 * - Name of a context assumption in proof mode (e.g. [fdestruct "H2"])
 *)

(* [fdestruct] is implemented by moving the formula from the
 * in front of the goal and calling [fintro] with the intro pattern. *)

Ltac move_from_context_to_goal T := 
  let C := get_context_goal in
  let n := match type of T with
    | nat => T
    | string => match lookup C T with
      | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
      | @Some _ ?n => n
      end
  end in
  let phi := nth C n in
  let C' := remove C n in
  apply (Weak (phi::C')); [| firstorder];
  match goal with 
  | [ |- prv _ _ ] => apply -> imps
  | [ |- tprv _ _ ] => apply -> switch_imp_T
  | [ |- pm _ ?psi ] => apply -> imps; change (pm C' (phi ~> psi))
  | [ |- tpm _ ?psi ] => apply -> switch_imp_T; change (tpm C' (phi ~> psi))
  end.

Section Fdestruct.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  Context {p : peirce}.

  Lemma fdestruct_discharge_premises T a b c :
    T ⊢ a -> T ⊢ b ~> c -> T ⊢ (a ~> b) ~> c.
  Proof.
    intros H1 H2. fintros. fapply H2. fapply 0. eapply Weak. apply H1. firstorder.
  Qed.

  Context {eq_dec_Funcs : eq_dec syms}.
  Context {eq_dec_Preds : eq_dec preds}.

  Lemma fdestruct_discharge_premises_T T a b c :
    T ⊩ a -> T ⊩ (b ~> c) -> T ⊩ ((a ~> b) ~> c).
  Proof.
    intros H1 H2. fintros. fapply H2. fapply 0. eapply Weak. apply H1. firstorder.
  Qed.
End Fdestruct.

Ltac fdestruct_discharge_premises :=
  try (
    match goal with 
    | [ |- prv _ _ ] => apply fdestruct_discharge_premises
    | [ |- tprv _ _ ] => apply fdestruct_discharge_premises_T
    | [ |- pm _ _ ] => make_compatible ltac:(fun _ => apply fdestruct_discharge_premises)
    | [ |- tpm _ _ ] => make_compatible ltac:(fun _ => apply fdestruct_discharge_premises_T)
    end;
    [| fdestruct_discharge_premises ]).

Ltac fdestruct' T A pat :=
  tryif is_hyp T then (
    (* Move Coq hypothesis into the context and call again *)
    let H := fresh "H" in
    let X := fresh "X" in
    assert (H := T);
    let s := get_form_hyp H in
    match goal with
    | [ |- prv ?C ?t ] => enough (C ⊢ (s ~> t)) as X by (feapply X; feapply H)
    | [ |- tprv ?C ?t ] => enough (C ⊩ (s ~> t)) as X by (feapply X; feapply H)
    | [ |- pm ?C ?t ] => enough (pm C (s ~> t)) as X by (feapply X; feapply H)
    | [ |- tpm ?C ?t ] => enough (tpm C (s ~> t)) as X by (feapply X; feapply H)
    end;
    fintro "?"; fdestruct' 0 A pat; clear H
  )
  else (
    try fspecialize_context T A;
    move_from_context_to_goal T;
    (* If the formula to destruct has premises, add them as goals *)
    fdestruct_discharge_premises;
    (* Compute pattern. Only try because of the additional goals *)
    try (let pattern := lazymatch pat with
    | "" => match get_form_goal with ?t ~> _ => create_pattern t end
    | "..." => match get_form_goal with ?t ~> _ => create_deep_pattern t end
    | _ => 
      match eval cbn in (parse_intro_pattern pat) with 
      | @Some _ ?p => p
      | @None => let msg := eval cbn in ("Invalid pattern: " ++ pat) in fail 3 msg
      end
    end in
    fintro_pat' pattern)
  ).

Tactic Notation "fdestruct" constr(T) := fdestruct' T constr:([] : list form) "".
Tactic Notation "fdestruct" "(" constr(T) constr(x1) ")" := fdestruct' T constr:([x1]) "".
Tactic Notation "fdestruct" "(" constr(T) constr(x1) constr(x2) ")" := fdestruct' T constr:([x1;x2]) "".
Tactic Notation "fdestruct" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := fdestruct' T constr:([x1;x2;x3]) "".

Tactic Notation "fdestruct" constr(T) "as" constr(pat) := fdestruct' T constr:([] : list form) pat.
Tactic Notation "fdestruct" "(" constr(T) constr(x1) ")" "as" constr(pat) := fdestruct' T constr:([x1]) pat.
Tactic Notation "fdestruct" "(" constr(T) constr(x1) constr(x2) ")" "as" constr(pat) := fdestruct' T constr:([x1;x2]) pat.
Tactic Notation "fdestruct" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" "as" constr(pat) := fdestruct' T constr:([x1;x2;x3]) pat.

(* Now that we have fdestruct, we can build a fancy [eapply in as] tactic *)
Tactic Notation "feapply" constr(T_imp) "in" constr(T_hyp) "as" constr(pat) := feapply_in T_imp constr:([] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "feapply"  "(" constr(T_imp) constr(x1) ")" "in" constr(T_hyp) "as" constr(pat) := feapply_in T_imp constr:([x1] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "feapply" "(" constr(T_imp) constr(x1) constr(x2) ")" "in" constr(T_hyp) "as" constr(pat) := feapply_in T_imp constr:([x1;x2] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "feapply" "(" constr(T_imp) constr(x1) constr(x2) constr(x3) ")" constr(T_hyp) "as" constr(pat) := feapply_in T_imp constr:([x1;x2;x3] : list form) T_hyp; try fdestruct T_hyp as pat.

Tactic Notation "fapply" constr(T_imp) "in" constr(T_hyp) "as" constr(pat) := fapply_in T_imp constr:([] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "fapply"  "(" constr(T_imp) constr(x1) ")" "in" constr(T_hyp) "as" constr(pat) := fapply_in T_imp constr:([x1] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "fapply" "(" constr(T_imp) constr(x1) constr(x2) ")" "in" constr(T_hyp) "as" constr(pat) := fapply_in T_imp constr:([x1;x2] : list form) T_hyp; try fdestruct T_hyp as pat.
Tactic Notation "fapply" "(" constr(T_imp) constr(x1) constr(x2) constr(x3) ")" constr(T_hyp) "as" constr(pat) := fapply_in T_imp constr:([x1;x2;x3] : list form) T_hyp; try fdestruct T_hyp as pat.





(** Classical Logic *)

Section Classical.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma case_help A phi psi :
    A ⊢C (phi ∨ (phi ~> ⊥) ~> psi) -> A ⊢C psi.
  Proof.
    intro H. eapply IE. apply H.
    eapply IE. eapply Pc.
    apply II. apply DI2. apply II.
    eapply IE. apply Ctx. right. now left.
    apply DI1. apply Ctx. now left.
  Qed.

  Lemma contradiction_help A phi :
    A ⊢C ((phi ~> ⊥) ~> ⊥) -> A ⊢C phi.
  Proof.
    intro H. eapply IE. eapply Pc. apply II.
    apply Exp. eapply IE. eapply Weak. apply H. firstorder.
    apply II. eapply IE. apply Ctx. right. now left.
    apply Ctx. now left.
  Qed.

  Context {eq_dec_Funcs : eq_dec syms}.
  Context {eq_dec_Preds : eq_dec preds}.

  Lemma case_help_T A phi psi :
    A ⊩C (phi ∨ (phi ~> ⊥) ~> psi) -> A ⊩C psi.
  Proof.
    intro H. eapply IE. apply H.
    eapply IE. eapply Pc.
    apply II. apply DI2. apply II.
    eapply IE. apply Ctx. firstorder.
    apply DI1. apply Ctx. firstorder.
  Qed.

  Lemma contradiction_help_T A phi :
    A ⊩C ((phi ~> ⊥) ~> ⊥) -> A ⊩C phi.
  Proof.
    intro H. eapply IE. eapply Pc. apply II.
    apply Exp. eapply IE. eapply Weak. apply H. firstorder.
    apply II. eapply IE. apply Ctx. firstorder.
    apply Ctx. firstorder.
  Qed.

End Classical.


Tactic Notation "fclassical" constr(phi) "as" constr(H1) constr(H2) := 
  make_compatible ltac:(fun _ => 
    match goal with
    | [ |- _ ⊢ _ ] => apply (case_help _ phi)
    | [ |- _ ⊩ _ ] => apply (case_help_T _ phi)
    end
  ); let pat := eval cbn in ("[" ++ H1 ++ "|" ++ H2 ++ "]") in fintro_pat pat.
Tactic Notation "fclassical" constr(phi) "as" constr(H) := fclassical phi as H H.
Tactic Notation "fclassical" constr(phi) := fclassical phi as "".

Tactic Notation "fcontradict" "as" constr(H) := 
  make_compatible ltac:(fun _ => 
    match goal with 
    | [ |- _ ⊢ _ ] => apply contradiction_help
    | [ |- _ ⊩ _ ] => apply contradiction_help_T
    end
  ); fintro_pat H.
Tactic Notation "fcontradict" := fcontradict as "?".






(** Provide general rewriting by abstracting the equality symbol and the
    neccessary lemmas in the `Leibniz` type class *)

Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Fixpoint VecForall2 {X Y n} (p : X -> Y -> Prop) (v1 : Vector.t X n) (v2 : Vector.t Y n) :=
  match v1 in Vector.t _ n return Vector.t Y n -> Prop with
  | Vector.nil _ => fun _ => True
  | Vector.cons _ x _ v1 => fun v2 => p x (Vector.hd v2) /\ VecForall2 p v1 (Vector.tl v2)
  end v2.

Class Leibniz (Σ_funcs : funcs_signature) (Σ_preds : preds_signature) (ff : falsity_flag) :=
{
  Eq_pred : preds ;
  eq_binary : 2 = ar_preds Eq_pred ;
  eq s t := @atom Σ_funcs Σ_preds _ _ Eq_pred (cast eq_binary (Vector.cons term s 1 (Vector.cons term t 0 (Vector.nil term)))) ;

  Axioms : list form ;

  eq_refl `{peirce} : Axioms ⊢ ∀ (eq ($0) ($0)) ;
  eq_sym `{peirce} : Axioms ⊢ ∀ ∀ (eq ($0) ($1) ~> eq ($1) ($0)) ;

  eq_func_congr `{peirce} : forall A F v1 v2, incl Axioms A -> VecForall2 (fun t1 t2 => A ⊢ eq t1 t2) v1 v2 -> A ⊢ eq (func F v1) (func F v2) ;
  eq_pred_congr `{peirce} : forall A P v1 v2, incl Axioms A -> VecForall2 (fun t1 t2 => A ⊢ eq t1 t2) v1 v2 -> A ⊢ atom P v1 <-> A ⊢ atom P v2 ;
}.

Lemma eq_subst_help `{funcs_signature} f y (v : Vector.t term 2) (e : 2 = y) :
  Vector.map f (cast e v) = cast e (@Vector.map term term f _ v).
Proof.
  destruct e. reflexivity.
Qed.

Lemma refl `{L : Leibniz, p : peirce} A x :
  incl Axioms A -> A ⊢ eq x x.
Proof.
  intros H. assert (H_refl := eq_refl). fspecialize (H_refl x). 
  rewrite eq_subst_help in H_refl. eapply Weak. apply H_refl. easy.
Qed.

Lemma sym `{L : Leibniz, p : peirce} A x y :
  incl Axioms A -> A ⊢ eq x y -> A ⊢ eq y x.
Proof.
  intros H1 H2. assert (H_sym := eq_sym). fspecialize (H_sym y x). 
  rewrite ! eq_subst_help in H_sym. simpl_subst H_sym. eapply IE. eapply Weak. 
  apply H_sym. easy. easy.
Qed.

Lemma leibniz_term `{L : Leibniz} `{p : peirce} A t s1 s2 :
  incl Axioms A -> (forall n, A ⊢ eq (s1 n) (s2 n)) -> A ⊢ eq (t`[s1]) (t`[s2]).
Proof.
  intros HA H. induction t; cbn.
  - apply H.
  - apply eq_func_congr. easy. induction v; constructor. apply IH; left. 
    apply IHv. intros. apply IH. now right.
Qed.

Lemma leibniz `{L : Leibniz} `{peirce} A phi t t' :
  incl Axioms A -> A ⊢ eq t t' -> A ⊢ phi[t..] -> A ⊢ phi[t'..].
Proof.
  enough (forall s1 s2, incl Axioms A ->(forall n, A ⊢ eq (s1 n) (s2 n)) -> A ⊢ phi[s1] <-> A ⊢ phi[s2]) as X. 
  { intros. apply X with (s1 := t..). easy. intros []; cbn. easy. now apply refl. easy. }
  induction phi; intros s1 s2 HA H1.
  - easy.
  - cbn in *. eapply eq_pred_congr. easy. induction t0; constructor.
    now apply leibniz_term. apply IHt0.
  - cbn in *. destruct b0; split; intros H2.
    + apply CE in H2. fsplit. now apply (IHphi1 L A s1). now apply (IHphi2 L A s1).
    + apply CE in H2. fsplit. now apply (IHphi1 L A s1 s2). now apply (IHphi2 L A s1 s2).
    + eapply DE in H2. apply H2.
      * fleft. apply (IHphi1 L _ s1). now apply incl_tl. intros. eapply Weak. 
        apply H1. now apply incl_tl. ctx.
      * fright. apply (IHphi2 L _ s1). now apply incl_tl. intros. eapply Weak. 
        apply H1. now apply incl_tl. ctx.
    + eapply DE in H2. apply H2.
      * fleft. apply (IHphi1 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
        apply H1. now apply incl_tl. ctx.
      * fright. apply (IHphi2 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
        apply H1. now apply incl_tl. ctx.
    + fintros. apply (IHphi2 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
      apply H1. now apply incl_tl. eapply IE. eapply Weak. apply H2. now apply incl_tl.
      apply (IHphi1 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
      apply H1. apply incl_tl, incl_refl. ctx.
    + fintros. apply (IHphi2 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
      apply H1. now apply incl_tl. eapply IE. eapply Weak. apply H2. now apply incl_tl.
      apply (IHphi1 L _ s1 s2). now apply incl_tl. intros. eapply Weak. 
      apply H1. apply incl_tl, incl_refl. ctx.
  - destruct q; split; cbn; intros H2.
    + fintros. rewrite subst_comp. apply (IHphi L _ _ (up s1 >> subst_term x..)). easy. 
      intros []; cbn. now apply refl. simpl_subst. simpl_subst. apply sym. easy. apply H1.
      rewrite <- subst_comp. now apply AllE.
    + fintros. rewrite subst_comp. apply (IHphi L _ _ (up s2 >> subst_term x..)). easy. 
      intros []; cbn. now apply refl. simpl_subst. simpl_subst. apply H1.
      rewrite <- subst_comp. now apply AllE.
    + fdestruct H2. apply (ExI _ x). rewrite ! subst_comp.
      apply (IHphi L _ _ (up s1 >> subst_term x..)). now apply incl_tl. 2: ctx.
      intros []; cbn. apply refl; now apply incl_tl. simpl_subst. simpl_subst. apply sym. now apply incl_tl.
      eapply Weak. apply H1. now apply incl_tl.
    + fdestruct H2. apply (ExI _ x). rewrite ! subst_comp.
      apply (IHphi L _ _ (up s2 >> subst_term x..)). now apply incl_tl. 2: ctx.
      intros []; cbn. apply refl; now apply incl_tl. simpl_subst. simpl_subst. 
      eapply Weak. apply H1. now apply incl_tl.
Qed.


(* Lemmas for rewriting with equivalences *)
Section FrewriteEquiv.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.
  Context {p : peirce}.

  Lemma frewrite_equiv_bin_l A op phi psi theta :
    A ⊢ (phi ↔ psi) -> A ⊢ (bin op phi theta ↔ bin op psi theta).
  Proof.
    intros E. fstart. destruct op; fsplit.
    - fintros "[P T]". fsplit. fapply E. ctx. ctx.
    - fintros "[P T]". fsplit. fapply E. ctx. ctx.
    - fintros "[P|T]". fleft. fapply E. ctx. fright. ctx.
    - fintros "[P|T]". fleft. fapply E. ctx. fright. ctx.
    - fintros "H" "P". fapply "H". fapply E. ctx.
    - fintros "H" "P". fapply "H". fapply E. ctx. 
  Qed.

  Lemma frewrite_equiv_bin_r A op phi psi theta :
    A ⊢ (phi ↔ psi) -> A ⊢ (bin op theta phi ↔ bin op theta psi).
  Proof.
    intros E. fstart. destruct op; fsplit.
    - fintros "[P T]". fsplit. ctx. fapply E. ctx.
    - fintros "[P T]". fsplit. ctx. fapply E. ctx.
    - fintros "[P|T]". fleft. ctx. fright. fapply E. ctx.
    - fintros "[P|T]". fleft. ctx. fright. fapply E. ctx.
    - fintros "H" "P". fapply E. fapply "H". ctx.
    - fintros "H" "P". fapply E. fapply "H". ctx.
  Qed.

  Lemma frewrite_equiv_bin_lr A op phi psi theta chi :
    A ⊢ (phi ↔ psi) -> A ⊢ (theta ↔ chi) -> A ⊢ (bin op phi theta ↔ bin op psi chi).
  Proof.
    intros E1 E2. fstart. destruct op; fsplit.
    - fintros "[P T]". fsplit. fapply E1. ctx. fapply E2. ctx.
    - fintros "[P C]". fsplit. fapply E1. ctx. fapply E2. ctx.
    - fintros "[P|T]". fleft. fapply E1. ctx. fright. fapply E2. ctx.
    - fintros "[P|C]". fleft. fapply E1. ctx. fright. fapply E2. ctx.
    - fintros "H" "P". fapply E2. fapply "H". fapply E1. ctx.
    - fintros "H" "P". fapply E2. fapply "H". fapply E1. ctx.
  Qed.

  Lemma frewrite_equiv_quant A op phi psi :
    A ⊢ (phi ↔ psi) -> A ⊢ (quant op phi[↑] ↔ quant op psi[↑]).
  Proof.
    intros E. fstart. destruct op; fsplit.
    - fintros "H" x. fapply E. fapply ("H" $0). (* Give dummy argument to avoid uninstantiated evar *)
    - fintros "H" x. fapply E. fapply ("H" $0).
    - fintros "[x H]". apply ExI with (t := x); simpl_subst. fapply E. ctx.
    - fintros "[x H]". apply ExI with (t := x); simpl_subst. fapply E. ctx.
  Qed.

  Lemma frewrite_equiv_switch A phi psi :
    A ⊢ (phi ↔ psi) -> A ⊢ (psi ↔ phi).
  Proof.
    intros E. fdestruct E. fsplit; ctx.
  Qed.

  Context {eq_dec_Funcs : EqDec syms}.
  Context {eq_dec_Preds : EqDec preds}.

  Lemma frewrite_equiv_bin_l_T T op phi psi theta :
    T ⊩ (phi ↔ psi) -> T ⊩ (bin op phi theta ↔ bin op psi theta).
  Proof.
    intros [A [ ]]. exists A. split. easy. now apply frewrite_equiv_bin_l.
  Qed.

  Lemma frewrite_equiv_bin_r_T T op phi psi theta :
    T ⊩ (phi ↔ psi) -> T ⊩ (bin op theta phi ↔ bin op theta psi).
  Proof.
    intros [A [ ]]. exists A. split. easy. now apply frewrite_equiv_bin_r.
  Qed.

  Lemma frewrite_equiv_bin_lr_T T op phi psi theta chi :
    T ⊩ (phi ↔ psi) -> T ⊩ (theta ↔ chi) -> T ⊩ (bin op phi theta ↔ bin op psi chi).
  Proof.
    intros [A [ ]] [B [ ]]. exists (List.app A B). split.
    now apply contains_app. apply frewrite_equiv_bin_lr.
    eapply Weak. apply H0. now apply incl_appl.
    eapply Weak. apply H2. now apply incl_appr.
  Qed.

  Lemma frewrite_equiv_quant_T T op phi psi :
    T ⊩ (phi ↔ psi) -> T ⊩ (quant op phi[↑] ↔ quant op psi[↑]).
  Proof.
    intros [A [ ]]. exists A. split. easy. now apply frewrite_equiv_quant.
  Qed.

  Lemma frewrite_equiv_switch_T T phi psi :
    T ⊩ (phi ↔ psi) -> T ⊩ (psi ↔ phi).
  Proof.
    intros [A [ ]]. exists A. split. easy. now apply frewrite_equiv_switch.
  Qed.

End FrewriteEquiv.

Ltac contains phi f := match phi with f => idtac | context P [ f ] => idtac end.

(* Solves a goal `A ↔ B` if `A` equals `B` up to replacing `phi`
 * with `psi`. `H` needs to be proof of `C ⊢ phi ↔ psi`. *)
Ltac frewrite_equiv_solve H phi psi :=
  match get_form_goal with
  | phi ↔ psi => apply H
  | bin ?op ?l ?r ↔ _ => (
      tryif contains l phi
      then (tryif contains r phi
        then apply_compat frewrite_equiv_bin_lr frewrite_equiv_bin_lr_T
        else apply_compat frewrite_equiv_bin_l frewrite_equiv_bin_l_T)
      else apply_compat frewrite_equiv_bin_r frewrite_equiv_bin_r_T
    );
    frewrite_equiv_solve H phi psi
  | quant _ _ _ ↔ _ => 
    apply_compat frewrite_equiv_quant frewrite_equiv_quant_T;
    frewrite_equiv_solve H phi psi
  end.

(* Replaces all occurences of `t` in `phi` with `s`. *)
Ltac frewrite_replace_all phi t s :=
  match phi with
  | context C[t] => let phi' := context C[s] in frewrite_replace_all phi' t s
  | _ => phi
  end.

Fixpoint up_n `{funcs_signature} n sigma := match n with
| 0 => sigma
| S n' => up (up_n n' sigma)
end.

Ltac shift_n n t := 
  match n with
  | 0 => t
  | S ?n' => shift_n n' (t`[↑])
  end.

Ltac vector_map_ltac v f :=
  match v with
  | Vector.nil ?t => constr:(Vector.nil t)
  | @Vector.cons _ ?x _ ?v' =>
    let x' := f x in 
    let v'' := vector_map_ltac v' f in
    constr:(@Vector.cons _ x' _ v'')
  end.

(* Returns a new formula where all occurences of `t` are turned into
 * `($n)[up_n n t..]` and every other term `s` into `s[up_n n ↑][up_n t..]`,
 * where `n` is the quantor depth. *)
Ltac add_shifts' n t G :=
  let f := add_shifts' n t in 
  let t_shifted := shift_n n t in
  match G with
  (* Terms: *)
  | t_shifted => constr:(($n)`[up_n n t..])
  | $(?m) => constr:(($m)`[up_n n ↑]`[up_n n t..])
  | func ?fu ?vec => let vec' := vector_map_ltac vec f in constr:(func fu vec')
  (* Formulas: *)
  | falsity => constr:(falsity[up_n n ↑][up_n n t..])
  | atom ?P ?vec => let vec' := vector_map_ltac vec f in constr:(atom P vec')
  | bin ?op ?u ?v => let u' := f u in let v' := f v in constr:(bin op u' v')
  | quant ?op ?u => let u' := add_shifts' (S n) t u in constr:(quant op u')
  (* Fallback for variables which cannot be matched syntactically: *)
  | ?u => match type of u with 
      | form => constr:(u[up_n n ↑][up_n n t..])
      | term => constr:(u`[up_n n ↑]`[up_n n t..])
      end
  end.
Ltac add_shifts := add_shifts' 0.

(* Returns a new formula where all occurences of `s[up_n n ↑][up_n nt..]` 
 * in G are turned into `s[up_n n ↑]` and `($n)[up_n n t..]` into `$n`. *)
Ltac remove_shifts G t :=
  match G with 
  | context C[ ?s[up_n ?n ↑][up_n ?n t..] ] => let G' := context C[ s[up_n n ↑] ] in remove_shifts G' t
  | context C[ ?s`[up_n ?n ↑]`[up_n ?n t..] ] => let G' := context C[ s`[up_n n ↑] ] in remove_shifts G' t
  | context C[ ($ ?n)`[up_n ?n t..] ] => let G' := context C[ $n ] in remove_shifts G' t
  | _ => G
  end.

(* Like [do n tac] but works with Galina numbers. *)
Ltac repeat_n n tac := match n with 0 => idtac | S ?n' => tac; repeat_n n' tac end.

Ltac frewrite' T A back := fun contxt =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  fspecialize_list H A; 
  instantiate_evars H; 
  simpl_subst H;

  (* For some reason the match below binds `_t` and `_t'` to terms
   * with unfolded constants (like `zero` in PA). This messes up
   * syntactic matching later. Therefore just unfold everything,
   * do the rewriting and fold back later. *)
  custom_unfold;

  (* For some reason `↑` sometimes gets turned into `fun x => $(S x)` *)
  repeat match goal with
  | [ |- context C[fun x => $(S x)] ] => let G := context C[↑] in change G
  end;

  match get_form_hyp H with 
  (* Rewrite with equivalence *)
  | ?_phi ↔ ?_psi => 
    let phi := match back with true => _psi | false => _phi end in
    let psi := match back with true => _phi | false => _psi end in
    match back with true => apply_compat frewrite_equiv_switch frewrite_equiv_switch_T in H | _ => idtac end;

    let G := get_form_goal in
    let G' := frewrite_replace_all G phi psi in
    let E := fresh "E" in
    assert_compat (G ↔ G') as E;
    [ frewrite_equiv_solve H phi psi |];
    feapply E;
    clear E

  (* Rewrite with equality *)
  | atom ?p (@Vector.cons _ ?_t _ (@Vector.cons _ ?_t' _ (Vector.nil term))) =>
    (* Make sure that we have equality *)
    assert (p = Eq_pred) as _ by reflexivity;

    let t := match back with true => _t' | false => _t end in
    let t' := match back with true => _t | false => _t' end in
    
    (* 1. Replace each occurence of `t` with `($n)[up_n n t..]` and every
     *  other `s` with `s[up_n n ↑][up_n n t..]`. The new formula is 
     *  created with the [add_shifts] tactic and proven in place. *)
    let C := get_context_goal in
    let G := get_form_goal in
    let X := fresh in
    let G' := add_shifts t G in
    match goal with
    | [ |- _ ⊢ _ ] => enough (C ⊢ G') as X
    | [ |- _ ⊩ _ ] => enough (C ⊩ G') as X
    end;
    [
      repeat match type of X with context K[ ?u`[up_n ?n ↑]`[up_n ?n t..] ] =>
        let R := fresh in
        (* TODO: Prove general lemma for this: *)
        assert (u`[up_n n ↑]`[up_n n t..] = u) as R; [
          rewrite subst_term_comp; apply subst_term_id; 
          let a := fresh in intros a;
          (repeat_n n ltac:(try destruct a)); reflexivity |];
        rewrite R in X
      end;
      apply X
    |];
    
    (* 2. Pull out the [t..] substitution *)
    match goal with 
    | [ |- ?U ⊢ ?G ] => let G' := remove_shifts G t in change (U ⊢ G'[t..])
    | [ |- ?U ⊩ ?G ] => let G' := remove_shifts G t in change (U ⊩ G'[t..])
    end;

    (* 3. Change [t..] to [t'..] using leibniz. For some reason
     *  we cannot directly [apply leibniz with (t := t')] if t'
     *  contains ⊕, σ, etc. But evar seems to work. *)
    let t'' := fresh "t" in 
    match goal with
    | [ |- _ ⊢ _ ] => eapply (leibniz _ _ ?[t''])
    | [ |- _ ⊩ _ ] => fail "Rewrite not supported under theories" (* eapply (leibniz_T _ _ ?[t'']) *)
    end;
    [ instantiate (t'' := t'); firstorder |
      match back with
      | false => let H_sym := fresh in assert (H_sym := eq_sym); feapply H_sym; clear H_sym; fapply H
      | true => apply H
      end
    | ];
    
    (* 4. Pull substitutions inward, but don't unfold `up_n` *)
    cbn -[up_n];
    
    (* 5. Turn subst_term calls back into []-Notation *)
    (* repeat match goal with [ |- context C`[subst_term ?sigma ?s] ] =>
      let G' := context C[ s`[sigma] ] in change G'
    end; *)

    (* 6. Fix simplification that occurs because of cbn *)
    repeat match goal with [ |- context C[up_n ?n ↑ ?a] ] =>
      let G' := context C[ ($a)[up_n n ↑] ] in change G'
    end;

    (* 7. Change `up (up ...)` back into `up_n n ...` *)
    repeat match goal with 
    | [ |- context C[up_n ?n (up ?s)]] => let G' := context C[up_n (S n) s] in change G'
    | [ |- context C[up ?s]] => let G' := context C[up_n 1 s] in change G'
    end;

    (* 8. Simplify *)
    repeat match goal with [ |- context K[ ?u `[up_n ?n ↑]`[up_n ?n t'..] ]] =>
      let R := fresh in
      (* TODO: Prove general lemma for this: *)
      assert (u`[up_n n ↑]`[up_n n t'..] = u) as R; [
        rewrite subst_term_comp; apply subst_term_id; 
        let a := fresh in intros a;
        (repeat_n n ltac:(try destruct a)); reflexivity |];
      rewrite ! R;
      clear R
    end;

    (* Base case for rewrite without quantors *)
    cbn; try rewrite !subst_shift; try rewrite !subst_term_shift;

    (* Final simplifications *)
    custom_fold;
    simpl_subst
  end;
  clear H.

Tactic Notation "frewrite" constr(T) := make_compatible ltac:(frewrite' T constr:([] : list form) constr:(false)).
Tactic Notation "frewrite" "(" constr(T) constr(x1) ")" := make_compatible ltac:(frewrite' T constr:([x1]) constr:(false)).
Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2]) constr:(false)).
Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2;x3]) constr:(false)).

Tactic Notation "frewrite" "<-" constr(T) := make_compatible ltac:(frewrite' T constr:([] : list form) constr:(true)).
Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) ")" := make_compatible ltac:(frewrite' T constr:([x1]) constr:(true)).
Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2]) constr:(true)).
Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2;x3]) constr:(true)).




Ltac fexists x := make_compatible ltac:(fun _ => 
  apply (ExI _ x); 
  simpl_subst).



