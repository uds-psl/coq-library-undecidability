From Coq Require List Vector.

From Undecidability.TM Require Import TM Util.TM_facts.

Import ListNotations Vector.VectorNotations.

Definition encNatTM {Σ : Type} (s b : Σ) (n : nat) :=
  @midtape Σ [] b (repeat s n).

Definition TM_computable {k} (R : Vector.t nat k -> nat -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t nat k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t
                                /\ Vector.hd t = encNatTM s b m) /\
  (forall q t, TM.eval M (start M) ((niltape :: Vector.map (encNatTM s b) v) ++ Vector.const niltape n) q t ->
          exists m, Vector.hd t = encNatTM s b m).