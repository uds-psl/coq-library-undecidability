(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* ** Object-level encoding of bounded universal quantification II *)

Require Import Arith List Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac gcd prime binomial sums bool_nat.

From Undecidability.H10.Matija 
  Require Import cipher.

From Undecidability.H10.Dio 
  Require Import dio_logic dio_expo dio_binary.

Set Implicit Arguments.

Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).

(* seqs_of_ones l q u u1 iff 

            l+1 < q 
       and  u  = ∑(i<l) r^(2^(1+i))
       and  u1 = ∑(i<l) r^(2^(2+i)) 
       with r := 2^(4q)
 
  *)

Theorem dio_rel_seqs_of_ones l q u u1 : 𝔻F l -> 𝔻F q -> 𝔻F u -> 𝔻F u1
          -> 𝔻R (fun v => seqs_of_ones (l v) (q v) (u v) (u1 v)).
Proof. 
  dio by lemma (fun v => seqs_of_ones_dio (l v) (q v) (u v) (u1 v)). 
Defined.

#[export] Hint Resolve dio_rel_seqs_of_ones : dio_rel_db.

(* a is the q-cipher of some l-tuple *)

Theorem dio_rel_Code l q a : 𝔻F l -> 𝔻F q -> 𝔻F a
                          -> 𝔻R (fun v => Code (l v) (q v) (a v)).
Proof.
  dio by lemma (fun v => Code_dio (l v) (q v) (a v)).
Defined.

#[export] Hint Resolve dio_rel_Code : dio_rel_db.

(* c is the q-cipher of the l-tuple <x,...,x> *)

Theorem dio_rel_Const l q c x : 𝔻F l -> 𝔻F q -> 𝔻F c -> 𝔻F x
                             -> 𝔻R (fun v => Const (l v) (q v) (c v) (x v)).
Proof.
  dio by lemma (fun v => Const_dio (l v) (q v) (c v) (x v)).
Defined.

#[export] Hint Resolve dio_rel_Const : dio_rel_db.

(* a is the q-cipher of the l-tuple <0,...,l-1> *)

Theorem dio_rel_CodeNat l q a : 𝔻F l -> 𝔻F q -> 𝔻F a 
                             -> 𝔻R (fun v => CodeNat (l v) (q v) (a v)).
Proof.
  dio by lemma (fun v => CodeNat_dio (l v) (q v) (a v)).
Defined.

#[export] Hint Resolve dio_rel_CodeNat : dio_rel_db.

(* Testing whether a is the q cipher of the sum of the tuples of q-ciphers b and c *)

Theorem dio_rel_Code_plus a b c : 𝔻F a -> 𝔻F b -> 𝔻F c
                               -> 𝔻R (fun v => Code_plus (a v) (b v) (c v)).
Proof. intros; unfold Code_plus; dio auto. Defined.

(* Testing whether a is the q cipher of the product of the tuples of q-ciphers b and c *)

Theorem dio_rel_Code_mult l q a b c : 𝔻F l -> 𝔻F q -> 𝔻F a -> 𝔻F b -> 𝔻F c
                                   -> 𝔻R (fun v => Code_mult (l v) (q v) (a v) (b v) (c v)).
Proof. intros; unfold Code_mult; dio auto. Defined.

#[export] Hint Resolve dio_rel_Code_plus dio_rel_Code_mult : dio_rel_db.

(* Now we have diophantine representations of q-cipher of the following l-tuple

    1) <x,...,x>  (for x < 2^q)
    2) <0,...,l-1> 
    3) testing whether some code is a q-cipher of some tuple
    4) testing sum and product equality among q-ciphers 

*)
