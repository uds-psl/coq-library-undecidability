From Undecidability.L Require Import L AbstractMachines.Programs AbstractMachines.AbstractHeapMachineDef.
(** *** Bonus:  Unfolding on Programs *)

(** We define a function f to unfold a closure, needed for the Turing machine M_unf. *)

Section UnfoldPro.

  Variable H : list heapEntry.

  Fixpoint unfoldC fuel (s:term) a k {struct fuel}: option term :=
    match fuel with
      0 => None
    | S fuel =>
      match s with
      | app s t =>
        match unfoldC fuel s a k, unfoldC fuel t a k with
          Some s',Some t' => Some (s' t')
        | _,_ => None
        end
      | lam s => 
        match unfoldC fuel s a (S k) with
          Some s' => Some (lam s')
        | _ => None
        end
      | var n =>
        if leb k n then 
          match lookup H a (n-k) with
            Some (s,b) =>
            match unfoldC fuel s b 1 with
              Some s' => Some (lam s')
            | _ => None
            end 
          | _ => None
          end
        else
          Some (var n)
      end
    end.

  Lemma unfoldC_mono s a k n n' :
    n <= n' -> unfoldC n s a k <> None -> unfoldC n' s a k = unfoldC n s a k.
  Proof.
    induction n in s,a,k,n'|-*. now cbn.
    destruct n'. now omega.
    intros leq eq. cbn in eq|-*.
    repeat (let eq := fresh "eq" in destruct _ eqn:eq).
    all:try congruence.
    all: repeat lazymatch goal with
            _ : S ?n <= S ?n', 
                H : (unfoldC ?n ?P ?a ?k  = _) ,
                    H' : (unfoldC ?n' ?P ?a ?k = _)
            |- _ => rewrite IHn in H';[ | omega | congruence]
                    end.
    all:congruence.
  Qed.

  Fixpoint depth s : nat :=
    match s with
      app s t => S (max (depth s) (depth t))
    | lam s => S (depth s)
    | _ => 1
    end.
  
  Lemma unfoldC_correct a k s s':
    unfolds H a k s s' ->
    unfoldC (depth s') s a k = Some s'.
  Proof.
    induction 1. all:cbn.
    1,2: (destruct (Nat.leb_spec0 k n); try omega);[].
    - easy.
    -rewrite H1, IHunfolds. all:easy.
    -rewrite IHunfolds. easy.
    -erewrite unfoldC_mono. 3:now rewrite IHunfolds1. 2:now Lia.lia.
     rewrite IHunfolds1. 
     erewrite unfoldC_mono. 3:now rewrite IHunfolds2. 2:now Lia.lia.
     rewrite IHunfolds2. easy.
  Qed.

  Lemma unfoldC_correct_final P a s:
    reprC H (P,a) s ->
    exists t, s = lam t /\ exists n, unfoldC n P a 1 = Some t.
  Proof.
    intros H'. inv H'.
    specialize (unfoldC_correct H5) as eq. eauto.
  Qed.

  Lemma unfoldsC_correct2 n s a k s':
    unfoldC n s a k = Some s'
    -> unfolds H a k s s'.
  Proof.
    induction n in a,s,s',k|-*. now inversion 1.
    cbn.
    destruct s. 1:destruct (Nat.leb_spec0 k n0).
    all:repeat (let eq := fresh "eq" in destruct _ eqn:eq);intros [= <-];subst.
    all: repeat lazymatch goal with
                   H : (unfoldC ?n ?P ?a ?k  = Some _) 
            |- _ => apply IHn in H
                    end.
     all:eauto using unfolds,not_ge.
  Qed.
End UnfoldPro.

Lemma unfolds_inj H k s a s1 s2 :
  unfolds H k s a s1 -> unfolds H k s a s2 -> s1=s2.
Proof.
  (* intros (n1&eq1)%unfoldC_correct (n2&eq2)%unfoldC_correct.
  enough (unfoldC H a k s n1 = unfoldC H a k s n2) by congruence.
  specialize unfoldC_mono with (n':= max n1 n2) (n:= min n1 n2).
  eapply Max.max_case_strong;eapply Min.min_case_strong;intros ? ?.
  all:try (replace n2 with n1 in * by omega;congruence).
  all:intros ->. all:easy. *)
  
  induction 1 in s2|-*;intros H';inv H';try congruence;try omega.
  -rewrite H1 in H5. inv H5. f_equal. eauto.
  -f_equal. eauto.
  -f_equal. all:auto.
Qed.

