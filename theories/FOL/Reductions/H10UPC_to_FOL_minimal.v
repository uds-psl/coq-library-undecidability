(* * FOL Reductions *)

From Undecidability.DiophantineConstraints Require Import H10C.
From Undecidability.DiophantineConstraints.Util Require Import H10UPC_facts.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FragmentNDFacts Semantics.Tarski.FragmentSoundness Semantics.Tarski.FragmentFacts Syntax.BinSig Semantics.Kripke.FragmentCore  Semantics.Kripke.FragmentSoundness Semantics.Kripke.FragmentToTarski.
From Undecidability.Shared Require Import Dec.
From Undecidability.Shared.Libs.PSL Require Import Numbers.
From Coq Require Import Arith Lia List.
From Undecidability.FOL.Reductions Require Import H10UPC_to_FOL_friedman H10UPC_to_FOL_constructions.


(* ** Validity *)

(*
Idea: The relation (#&#35;#) has the following properties:#<ul>#
#<li>#n ~ p: n is left component of p#</li>#
#<li>#p ~ n: p is right component of p#</li>#
#<li>#p ~ p: the special relationship of H10UPC#</li>#
#<li>#n ~ m: n = m. Special case n=0, m=1: #<br />#
          The instance h10 of H10UPC is a yes-instance. #<br />#
          This is to facilitate Friedman translation#</li>#
*)


Set Default Goal Selector "!".


Require Import Undecidability.Synthetic.Definitions.

(* Final collection of undecidability reductions *)
Section undecResults.

  Definition minimalSignature (f:funcs_signature) (p:preds_signature) : Prop := 
    match f,p with
     {|syms := F; ar_syms := aF|},{|preds := P; ar_preds := aP|}
       => (F -> False) /\ exists pp : P, aP pp = 2
    end.

  Lemma sig_is_minimal : minimalSignature sig_empty sig_binary.
  Proof.
  split.
  * intros [].
  * now exists tt.
  Qed.

  Theorem validReduction : H10UPC_SAT ⪯ @valid sig_empty sig_binary falsity_off.
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply transport.
  * apply inverseTransport.
  Qed.

  Theorem satisReduction : complement H10UPC_SAT ⪯ @satis sig_empty sig_binary falsity_on.
  Proof.
  exists (fun l => @F falsity_on l → falsity). split.
  * apply satisTransport.
  * apply satisInverseTransport.
  Qed.

  Theorem proveReduction : H10UPC_SAT ⪯ (fun (k:@form sig_empty sig_binary frag_operators falsity_off) => nil ⊢M k).
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply proofTransport.
  * apply inverseProofTransport.
  Qed.

  Theorem classicalProveReduction :
    H10UPC_SAT ⪯ (fun (k:@form sig_empty sig_binary frag_operators falsity_off) => nil ⊢C k).
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply classicalProvabilityTransport.
  * apply classicalProvabilityInverseTransport.
  Qed.

  Theorem kripkeValidReduction : H10UPC_SAT ⪯ @kvalid sig_empty sig_binary falsity_off.
  Proof.
  exists (fun l => @F falsity_off l). split.
  * apply kripkeTransport.
  * apply kripkeInverseTransport.
  Qed.

  Theorem kripkeSatisReduction : complement H10UPC_SAT ⪯ @ksatis sig_empty sig_binary falsity_on.
  Proof.
  exists (fun l => @F falsity_on l → falsity). split.
  * apply ksatisTransport.
  * apply ksatisInverseTransport.
  Qed.

End undecResults.
