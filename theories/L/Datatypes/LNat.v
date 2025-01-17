From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Export LTactics GenEncode.
Require Import Undecidability.Shared.Libs.PSL.Numbers.

From Stdlib Require Import Nat.
From Undecidability.L Require Import Datatypes.LBool Functions.EqBool Datatypes.LProd. 
Import GenEncode. Import Nat.
(* ** Encoding of natural numbers *)

MetaCoq Run (tmGenEncodeInj "nat_enc" nat).
#[export] Hint Resolve nat_enc_correct : Lrewrite.

#[global]
Instance termT_S : computable S.
Proof.
  extract constructor.
Qed.

#[global]
Instance termT_pred : computable pred.
Proof.
  extract.
Qed.

#[global]
Instance termT_plus' : computable add.
Proof.
  extract.
Qed.

#[global]
Instance termT_mult : computable mult.
Proof.
  extract.
Qed.

#[global]
Instance term_sub : computable Nat.sub.
Proof.
  extract.
Qed.

#[global]
Instance termT_leb : computable leb.
Proof.
  extract.
Qed.

#[global]
Instance term_ltb : computable Nat.ltb. 
Proof. 
  extract.
Qed.

#[global]
Instance eqbNat_inst : eqbClass Nat.eqb.
Proof.
  exact Nat.eqb_spec. 
Qed.

#[global]
Instance eqbComp_nat : eqbComp nat.
Proof.
  constructor. unfold Nat.eqb.
  extract.
Qed.

#[global]
Instance termT_nat_min : computable Nat.min.
Proof.
  extract.
Qed. 

#[global]
Instance termT_nat_max : computable Nat.max.
Proof. 
  extract.
Qed. 

#[global]
Instance termT_pow:
  computable Init.Nat.pow.
Proof.
  extract.
Qed.


#[global]
Instance termT_divmod : 
  computable divmod. 
Proof. 
  extract.
Qed. 

#[global]
Instance termT_modulo : 
  computable Init.Nat.modulo. 
Proof.
  extract.
Qed. 

(* now some more encoding-related properties:*)

Fixpoint nat_unenc (s : term) :=
  match s with
  | lam (lam #1) => Some 0
  | lam (lam (app #0 s)) => match nat_unenc s with Some n => Some (S n) | x=>x end
  | _ => None
  end.

Lemma unenc_correct m : (nat_unenc (nat_enc m)) = Some m.
Proof.
  induction m; simpl; now try rewrite IHm.
Qed.

Lemma unenc_correct2 t n : nat_unenc t = Some n -> nat_enc n = t.
Proof with try solve [Coq.Init.Tactics.easy].
  revert n. eapply (size_induction (f := size) (p := (fun t => forall n, nat_unenc t = Some n -> nat_enc n = t))). clear t. intros t IHt n H.
  destruct t as [ | | t]. easy. easy.
  destruct t as [ | | t]. easy. easy.
  destruct t. 3:easy.
  -destruct n0. easy. destruct n0. 2:easy. inv H. easy.
  -destruct t1. 2-3:easy. destruct n0. 2:easy. simpl in H. destruct (nat_unenc t2) eqn:A.
   +apply IHt in A;simpl;try lia. destruct n. inv H. simpl. congruence.
   +congruence.
Qed.

Lemma dec_enc t : dec (exists n, t = nat_enc n).
Proof.
  destruct (nat_unenc t) eqn:H.
  - left. exists n. now eapply unenc_correct2 in H.
  - right. intros [n A]. rewrite A in H. rewrite unenc_correct in H. inv H.
Qed.
