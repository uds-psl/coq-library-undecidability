From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat LTerm LBool LProd List.List_enc LOptions.

(* ** Extracted encoding of natural numbers *)

#[global]
Instance term_nat_enc : computableTime' (enc (X:= nat)) (fun n _ => (n * 14 + 12,tt)).
Proof.
  unfold enc;cbn. extract. solverec.
Qed.

(* ** Extracted term encoding *)

#[global]
Instance term_term_enc : computableTime' (enc (X:=term)) (fun s _ => (size s * 30,tt)).
Proof.
  unfold enc;cbn. extract. solverec.
Qed.



#[global]
Instance bool_enc :computableTime' (enc (X:=bool)) (fun l _ => (12,tt)).
Proof.
  unfold enc;cbn. extract. solverec.
Qed.

(* ** Extracted tuple encoding *)

#[global]
Instance term_prod_enc X Y (R1:encodable X) (R2:encodable Y) t__X t__Y
         `{computableTime' (@enc X _) t__X} `{computableTime' (@enc Y _) t__Y}
  :computableTime' (enc (X:=X*Y)) (fun w _ => (let '(x,y):= w in  fst (t__X x tt) + fst (t__Y y tt) + 15,tt)).
Proof.
  unfold enc;cbn.
  extract. solverec.
Qed.


#[global]
Instance term_list_enc X (R:encodable X) t__X 
         `{computableTime' (@enc X _) t__X} 
  :computableTime' (enc (X:=list X)) (fun l _ => (sumn (map (fun x => fst (t__X x tt) + 17) l) + 12,tt)).
Proof.
  unfold enc;cbn.
  extract. solverec.
Qed.

Import LOptions.

#[global]
Instance term_option_enc X (R:encodable X) t__X 
         `{computableTime' (@enc X _) t__X} 
  :computableTime' (enc (X:=option X)) (fun x _ => (match x with Some x => fst (t__X x tt) | _ => 0 end + 15,tt)).
Proof.
  unfold enc;cbn.
  extract. solverec.
Qed.



(*
Set Printing Implicit.
Check (extT (@enc (nat*(nat*nat)) _)).
*)
(*
Definition prod_enc' {X Y} (enc_x : X -> term) (enc_y : Y -> term) : X * Y -> term :=
  fix f w := let '(x,y) := w in
             lam (var 0 (enc_x x) (enc_y y)).

Lemma enc_prod_eq {X Y} {H__x:encodable X} {H__y : encodable Y}:
  @enc (X*Y) _ = prod_enc' (@enc _ H__x) (@enc _ H__y).
Proof.
  unfold enc. destruct H__x, H__y. reflexivity.
Qed.

Instance term_prod_enc' {X Y} {H__x : encodable X} {H__Y : encodable Y}:
  computableTime' (@prod_enc' X Y) (fun _ t__X => (1,fun _ t__Y => (1,fun w _ => (let '(x,y):= w in  fst (t__X x tt) + fst (t__Y y tt) + 15,tt)))).
Proof.
  extract. solverec.
Qed.
*)
