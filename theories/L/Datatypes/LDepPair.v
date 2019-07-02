From Undecidability.L.Tactics Require Import LTactics GenEncode.


(** TODO: I'm not sure how usable this definition is, I puit it here as i Didn;t want to rewrite it if needed. *)
Section sigT.
  Variable A : Type.
  Context `{reg_A : registered A}.
  Variable P : A -> Type.
  Context `{reg_P : forall x, registered (P x)}.

  Definition sigT_enc : encodable (sigT P) :=
    fun '@existT _ _ x y => lam (0 (enc x) (enc y)).
  
  Global Instance registered_sigT : registered (sigT P).
  Proof.
    exists sigT_enc.
    -intros []. cbn. Lproc.
    -intros [] [] H. inv H. eapply inj_enc in H1. subst x. apply inj_enc in H2. subst p. easy.
  Defined.

End sigT.
