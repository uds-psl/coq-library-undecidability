From Undecidability.L.Datatypes Require Import LOptions LBool LNat Lists.
From Undecidability.L.Tactics Require Import LTactics ComputableTactics.
Require Import Nat.

Section demo.

(* for examples of usage see LBool/LNat/Lists/Option/Encoding etc*)

Definition unit_enc := fun (x:unit) => I.

Instance register_unit : registered  unit.
Proof.
  register unit_enc. 
Defined.

(* example for higher-order-stuff *)

Definition on0 (f:nat->nat->nat) := f 0 0.

Instance term_on0 : computable on0.
Proof.
  extract. 
Qed.

Lemma test_Some_nat : computable (@Some nat).
Proof.
  extract.
Qed.

(** *** Interactive Demo *)

Section PaperExample.

  (** Examples of the tactics that proof the correctness lemmata *)

  Import ComputableTactics.
  Import ComputableTactics.Intern.

  Goal computable orb.
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    cstep.
    all:    cstep.
  Qed.

  Print cnst.

  (** Comming up with the conditions for the time bound *)
  Goal forall fT, computableTime orb fT.
    intros.
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep. (* Note that the second goal got more specific *)
    cstep. (* Note that the second goal got more specific *)
    cstep.
    1,2:cstep. (* Note that the hole in the second goal got filled with True*)
    solverec.
  Abort.  

  (** Finding the Time Bound *)
  
  Goal computableTime orb (fun _ _ => (cnst "c1",fun _ _ => (cnst "c2",tt))).
    extract. solverec. (* Now the values are clear *)
  Abort.

  Goal computableTime orb (fun _ _ => (1,fun _ _ => (3,tt))).
    extract. solverec.
  Abort.
  
  Import Datatypes.LNat.
  
  Goal computable Nat.add.
    unfold Nat.add.
    extractAs s.
    computable_using_noProof s.
    cstep.
    all:cstep.
    all:cstep.
  Qed.

  Goal computable (fix f (x y z : nat) := y + match y with |  S (S y) => S (f x y z) | _ => 0 end).
    extractAs s.
    computable_using_noProof s.
    cstep.
    all:cstep.
    all:cstep.
    all:cstep.
  Qed.

  
  
  Lemma supported3 : computable (fun (b:bool) => if b then (fix f x := match x with S x => f x | 0 => 0 end) else S).
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    all:cstep.
    all:cstep.
  Qed.


  (* this is due to https://github.com/coq/coq/issues/9761 *)
  Lemma unsupported : computable (fix f (y : nat) {struct y}:= match y with | S (S y) => f y | _ => S end).
    extractAs s.
    computable_using_noProof s.
    repeat cstep.
    Fail Guarded.
  Abort.

    (* this is due to https://github.com/coq/coq/issues/9761 *)
  Lemma workarround : let f := (fix f (z y : nat) {struct y}:= match y with | S (S y) => f z y | _ => S z end) in computable (fun y z => f z y).
    intros f. assert (computable f) by (unfold f;extract).
    extract.
  Qed.

  Lemma unsupported2 :  computable 10.
    extract. (* not true*) Fail reflexivity. 
  Abort.
  (* not a problem inside a function*)
  Goal computable (fun n : nat => 10).
    extract.
  Qed.

  

  Import Datatypes.Lists.
  Remove Hints term_map : typeclass_instances. 

  Lemma map_term A B  (Rx : registered A)  (Ry: registered B):
    computable (@map A B).
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    all:cstep.
  Qed.

  (*comming up with the condition *)

   Lemma termT_map A B (Rx : registered A)  (Ry: registered B):
    computableTime (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
    extractAs s.
    computable_using_noProof s.
    cstep.
    cstep.
    repeat cstep.
  Abort.
  
  (* comming up with the time bound *)

  Lemma termT_map A B (Rx : registered A)  (Ry: registered B):
    computableTime (@map A B) (fun f fT => (cnst "c",fun xs _ => (cnst ("f",xs),tt))).
    extract. solverec.
  Abort.

  Lemma term_map (X Y:Type) (Hx : registered X) (Hy:registered Y):
    computableTime (@map X Y)
                   (fun f fT => (1,fun l _ => (fold_right (fun x res => fst (fT x tt) + res + 12) 8 l,tt))).
  Proof.
    extract.
    solverec.
  Qed.

  End PaperExample. 


  (*
(* this is more or lest just a test for internalization automation... *)
Instance term_option_map X Y (Hy:registered Y) (Hx : registered X):computable (@option_map X Y).
Proof.
  compute' 0.  
  computePrettyStep.
  
  Unshelve. Focus 4. unfold int. cbn. Lsimpl. unfold intApp'. Set Printing Implicit. split. unfold int. cbn.  hnf. reflexivity. cbn. Lsimpl.
  computePrettyStep.
  computePrettyStep.
  Unshelve. Focus 4. split. reflexivity. Lreflexivity.
  compute auto. 
Qed.
   *)

  Instance term_nat_eqb : computable Nat.eqb.
  Proof.
    extract. 
  Defined.

End demo.
