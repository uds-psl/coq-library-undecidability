Set Implicit Arguments.
From Undecidability.HOU Require Import calculus.calculus 
  concon.conservativity unification.higher_order_unification.

(* ** Consequences *)
From Undecidability.HOU Require Import third_order.pcp third_order.simplified third_order.huet.

Corollary MPCP_U X: MPCP ⪯ U X.
Proof.
  eapply reduction_transitive. eapply MPCP_U3.
  eapply unification_conserve; eauto.
Qed.


Corollary PCP_U X: PCP ⪯ U X.
Proof.
  eapply reduction_transitive. eapply PCP_U3.
  eapply unification_conserve; eauto.
Qed.
