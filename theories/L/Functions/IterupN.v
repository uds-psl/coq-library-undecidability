From Undecidability.L.Datatypes Require Import LProd LOptions.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LBinNums.


Definition iterupN {X} i max x f :=
  fst (@N.peano_rect (fun _ => X*N)%type (x,i%N) (fun _ '(x,i) => (f i x,N.succ i)) (max-i)).

Lemma iterupN_eq {X} i max {x:X} f :
  iterupN i max x f = if (i <? max)%N then iterupN (N.succ i) max (f i x) f else x.
Proof.
  revert x f.
  revert i.
  refine (@N.left_induction' _ _ max _ _).
  all:intros n H.  2:intros IH. all:intros x f.
  -unfold iterupN.
   edestruct (N.ltb_spec0 n max). exfalso;Lia.lia.
   rewrite (proj2 (N.sub_0_le _ _)). 2:Lia.lia. reflexivity.
  -(* Todo:generalize over internal state*)
Admitted.
   
  

Lemma iterupN_geq {X} i max {x:X} f :
  (i >= max)%N -> iterupN i max x f = x.
Proof.
  intros. rewrite iterupN_eq. destruct (N.ltb_spec0 i max). all:easy.
Qed.

Lemma iterupN_lt {X} i max {x:X} f :
  (i < max)%N -> iterupN i max x f = iterupN (N.succ i) max (f i x) f.
Proof.
  intros H. rewrite iterupN_eq. destruct (N.ltb_spec0 i max). all:easy.
Qed.

Instance term_iterupN X `{H:registered X} : computable (iterupN (X:=X)).
Proof.
  pose (s := rho (λ F i max x f, (!!(ext N.ltb) i max) (λ _ , F (!!(ext N.succ) i) max (f i x) f) (λ _ , x) I)).
  cbv [convert TH minus] in s.
  
  exists s. unfold s. Intern.recRem P.
  eapply computesExpStart. now Lproc.
  eexists.
  eapply computesExpStep. now Lsimpl. now Lproc.
  intros i iExt iExts. cbn in iExts. subst iExt.

  eexists.
  eapply computesExpStep. Intern.recStepUnnamed. now Lsimpl. now Lproc.
  intros max yExt yExts. cbn in yExts. subst yExt.

  
  remember ((max - i)%N) as d eqn:eqd.
  revert i max eqd.
  induction d using N.peano_rect.
  all:intros i max eqd.
  all:eexists.
  all:split.
  1,3:now Intern.recStepUnnamed;Intern.extractCorrectCrush_new.

  all:eapply computesTyArr;[Lproc| intros x xExt xExts].
  all:change xExt with (@ext _ _ x (Build_computable xExts)).
  all:eexists;split.
  1,3:Intern.extractCorrectCrush_new.
  all:intros.

  all:eapply computesTyArr;[Lproc| intros f fExt fExts].
  all:change fExt with (@ext _ _ f (Build_computable fExts)).
  2:  apply f_equal with (f:=N.pred) in eqd;rewrite N.pred_succ,<- N.sub_succ_r in eqd.
  all:eexists;split.
  1,2:assert (N.ltb i max = false) by (apply N.ltb_ge;Lia.lia).
  1:{Intern.extractCorrectCrush_new. congruence. }
  {rewrite H3. rewrite iterupN_geq. 2:Lia.lia. reflexivity. }
  {Intern.extractCorrectCrush_new. } 
  intros.
  destruct (N.ltb_spec0 i max).
  rewrite iterupN_lt. 2:easy.
  reflexivity.
  rewrite iterupN_geq. all:easy.
  Unshelve. all:now try constructor;try exact _;try eauto;try exact 0.
Qed.
