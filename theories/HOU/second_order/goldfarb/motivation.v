Set Implicit Arguments.
Require Import List Lia.
From Undecidability.HOU Require Import std.std axioms.
Import ListNotations.

Set Default Proof Using "Type".

(* ** Multiplication Motivation  *)
Section Motivation.

  Variable (n: nat).
  Implicit Type (m p: nat) (M N: list (nat * nat)).

  Definition step '(a, b) := (n + a, 1 + b).
  Notation Step X := (map step X).
  Definition t k := (k * n, k).
  Definition T k := tab t k.
  Definition Mrel m p M := M ++ [(p, m)] = t 0 :: Step M.
  
  
  Lemma step_t k: step (t k) = t (S k).
  Proof. reflexivity. Qed.

  Lemma M_forward m: Mrel m (m * n) (T m).
  Proof.
    unfold Mrel, T; change (_ ++ _) with (tab t (S m)).
    now rewrite tab_S, tab_map. 
  Qed.

  Lemma M_backward_exists m p M: Mrel m p M -> exists l, M = T l.
  Proof.
    enough (forall a b x, M ++ [x] = (a, b) :: Step M -> M ++ [x] = tab (fun k => (a + k * n, b + k)) (S (length M))) as H.
    - intros H1 % H; apply app_injective_right in H1 as [H1 _]; eauto.
    - induction M as [|[l r]]; [cbn|]; intros; simplify; eauto.
      injection H as ? ? H1; subst. specialize (IHM _ _ _ H1) as ->.
      cbn [length]; rewrite !tab_S; cbn; simplify; do 2 f_equal.
      f_equal; lia. eapply tab_ext; intros; f_equal; lia.
  Qed.

  Lemma M_backward_equations m p l : Mrel m p (T l) -> m = l /\ m * n = p.
  Proof.
    unfold Mrel. rewrite <-M_forward.
    intros H % app_injective; intuition; congruence. 
  Qed.
  
  Lemma M_iff m p M: (m * n = p /\ M = T m) <-> Mrel m p M.
  Proof.
    split.
    - intros [<- ->]. apply M_forward.
    - intros H. specialize (M_backward_exists H) as [l ->].
      eapply M_backward_equations in H; intuition.
  Qed.

End Motivation.
