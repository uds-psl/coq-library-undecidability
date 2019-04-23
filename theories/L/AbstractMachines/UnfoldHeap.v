From Undecidability.L Require Import L AbstractMachines.Programs AbstractMachines.AbstractHeapMachine.
(** *** Bonus:  Unfolding on Programs *)

(** We define a function f to unfold a closure, needed for the Turing machine M_unf. *)

Section UnfoldPro.

  Variable H : list heapEntry.

  Fixpoint f (P:Pro) a k fuel {struct fuel}: option Pro :=
    match fuel with
      0 => None
    | S fuel =>
      match P,k with
       (* [retT],0 => Some [retT] *)
      | retT::P,S k =>
        match f P a k fuel with
          Some P' => Some (retT::P')
        | _ => None
        end
      | appT::P,_ =>
        match f P a k fuel with
          Some P' => Some (appT::P')
        | _ => None
        end
      | lamT::P,_ =>
        match f P a (S k) fuel with
          Some P' => Some (lamT::P')
        | _ => None
        end
      | varT n::P,_ =>
        if Dec (n >= k) then 
          match lookup H a (n-k) with
            Some (Q,b) =>
            match f Q b 1 fuel,f P a k fuel with
              Some Q', Some P' => 
              Some (lamT::Q'++retT::P')
            | _,_ => None
            end 
          | _ => None
          end
        else
          match f P a k fuel with
            Some P' => 
            Some (varT n::P')
          | _ => None
          end
      |[],_ => Some []
      |_,_ => None
      end      
    end.

  Lemma f_mono P a k n n' :
    n <= n' -> f P a k n <> None -> f P a k n' = f P a k n.
  Proof.
    induction n in P,a,k,n'|-*. now cbn.
    destruct n'. now omega.
    intros leq eq. cbn in eq|-*.
    repeat (let eq := fresh "eq" in destruct _ eqn:eq).
    all:try congruence.
    all:  repeat match goal with
            _ : S ?n <= S ?n', 
                H : (f ?P ?a ?k ?n' = _) ,
                    H' : (f ?P ?a ?k ?n = _)
            |- _ => rewrite IHn in H;[ | omega | congruence]
                    end.
    all:congruence.
  Qed.
  
  Lemma f_correct' Q Q' a k s s' n:
    unfolds H a k s s' ->
    f Q a k n = Some Q' -> 
    exists n', f (compile s++Q) a k n' = Some (compile s' ++ Q').
  Proof.
    induction s' in Q',Q,a,k,s,n |- *;intros H' eq.
    inv H'.
    - exists (S n). cbn. decide _. omega.
      now rewrite eq.
    - cbn. exfalso. inv H2. inv H3.
    - inv H'.
      {exfalso.  inv H2. inv H3. }
      cbn [compile].
      autorewrite with list.
      edestruct IHs'2 with (Q:=appT::Q) (n:=S n) as [n2 eq2]. 1:eassumption.
      cbn. now rewrite eq.
      edestruct IHs'1 as [n1 eq1]. 1:eassumption.
      2:{
        eexists. erewrite eq1. reflexivity.
      }
      eassumption.
    -inv H'.
     +inv H2. inv H3.
      edestruct IHs' with (n:=1)(Q:=@nil Tok) as [n1 eq1]. eassumption.
      reflexivity.
      autorewrite with list in eq1.
      exists (S (max n n1)).
      cbn. decide _. 2:omega. rewrite H1. erewrite f_mono.
      rewrite eq1. erewrite f_mono. rewrite eq.
      autorewrite with list. reflexivity.
      1,3:now apply Nat.max_case_strong;omega.
      1-2:congruence.
     + cbn.        edestruct IHs' as [n1 eq1].
       3:{eexists (S _).
       cbn. 
       autorewrite with list.
       cbn. rewrite eq1. reflexivity. }
       eassumption.
       instantiate (1 := S n).
       cbn. rewrite eq. now destruct Q.
  Qed.

  Lemma f_correct a s s' k:
    unfolds H a k s s' ->
    exists n', f (compile s) a k n' = Some (compile s').
  Proof.
    intros H'.
    specialize (f_correct' (n:=1) (Q:=@nil Tok) (Q':=@nil Tok) H') as [n eq].
    reflexivity.
    autorewrite with list in eq.
    eexists. rewrite eq. reflexivity.
  Qed.
  

  Lemma f_correct_final P a s:
    reprC H (P,a) s ->
    exists t, s = lam t /\ exists n, f P a 1 n = Some (compile t).
  Proof.
    intros H'. inv H'. inv H4. inv H6.
    specialize (f_correct H2) as eq. eauto.
  Qed.
  
End UnfoldPro.

Lemma unfolds_inj H k s a s1 s2 :
  unfolds H k s a s1 -> unfolds H k s a s2 -> s1=s2.
Proof.
  induction 1 in s2|-*;intros H';inv H';try congruence;try omega.
  -apply IHunfolds.
   replace b with b0 in * by congruence.
   inv H2. inv H7.
   replace s1 with s in * by (apply compile_inj;congruence). tauto.
  -f_equal. apply IHunfolds. auto.
  -f_equal. all:auto.
Qed.    

