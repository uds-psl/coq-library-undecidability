From Undecidability.TM Require Export TM.

Definition HaltsTM {sig: finType} {n: nat} (M : mTM sig n) (t : tapes sig n) :=
  exists outc k, loopM (initc M t) k = Some outc.

Definition HaltTM n (S: {sig:finType & mTM sig n & tapes sig n}) :=
  HaltsTM (projT2 (sigT_of_sigT2 S)) (projT3 S).

Arguments HaltTM :clear implicits.
