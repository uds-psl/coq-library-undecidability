From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat LTerm LProd Lists.

(** ** Extracted encoding of natural numbers *)

Instance term_nat_enc : computableTime' (nat_enc) (fun n _ => (n * 14 + 12,tt)).
Proof.
  extract. solverec.
Qed.

(** ** Extracted term encoding *)

Instance term_term_enc : computableTime' (term_enc) (fun s _ => (size s * 30,tt)).
Proof.
  extract. solverec.
Qed.

(** ** Extracted tuple encoding *)

Instance term_prod_enc X Y (R1:registered X) (R2:registered Y) t__X t__Y
         `{computableTime' (@enc X _) t__X} `{computableTime' (@enc Y _) t__Y}
  :computableTime' (@prod_enc X Y R1 R2) (fun w _ => (let '(x,y):= w in  fst (t__X x tt) + fst (t__Y y tt) + 15,tt)).
Proof.
  unfold prod_enc.
  change (match R1 with
          | @mk_registered _ enc _ _ => enc
          end) with (enc (registered:=R1)).
  change (match R2 with
          | @mk_registered _ enc _ _ => enc
          end) with (enc (registered:=R2)).
  extract. solverec.
Qed.


Instance term_list_enc X (R:registered X) t__X 
         `{computableTime' (@enc X _) t__X} 
  :computableTime' (@list_enc X R) (fun l _ => (sumn (map (fun x => fst (t__X x tt) + 17) l) + 12,tt)).
Proof.
  unfold list_enc.
  change (match R with
          | @mk_registered _ enc _ _ => enc
          end) with (enc (registered:=R)).
  extract. solverec.
Qed.

Import LOptions.

Instance term_option_enc X (R:registered X) t__X 
         `{computableTime' (@enc X _) t__X} 
  :computableTime' (@option_enc X R) (fun x _ => (match x with Some x => fst (t__X x tt) | _ => 0 end + 15,tt)).
Proof.
  unfold option_enc.
  change (match R with
          | @mk_registered _ enc _ _ => enc
          end) with (enc (registered:=R)).
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

Lemma enc_prod_eq {X Y} {H__x:registered X} {H__y : registered Y}:
  @enc (X*Y) _ = prod_enc' (@enc _ H__x) (@enc _ H__y).
Proof.
  unfold enc. destruct H__x, H__y. reflexivity.
Qed.

Instance term_prod_enc' {X Y} {H__x : registered X} {H__Y : registered Y}:
  computableTime' (@prod_enc' X Y) (fun _ t__X => (1,fun _ t__Y => (1,fun w _ => (let '(x,y):= w in  fst (t__X x tt) + fst (t__Y y tt) + 15,tt)))).
Proof.
  extract. solverec.
Qed.
*)
