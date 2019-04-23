From Undecidability.L.Computability Require Export EnumInt Acceptability Equality Enum Seval.
Require Import PslBase.Bijection.
From Undecidability.L.Tactics Import ComputableTactics.Local.

(** * Definition of Recursive Enumerability *)

Definition RE P := exists (f : term), proc f /\ (forall n, f(enc n) == enc (@None term) \/ exists s, f (enc n) == enc (Some s) /\ P s) /\ forall s, P s -> exists n, f (enc n) == enc (Some s).

(** * The Enumeration combinator and its properties *)

Section Fix_f.

  Variable f : term.
  Hypothesis proc_f : proc f.
  Hypothesis total_f : forall n:nat, exists s:option term, f (enc n) == enc s.

  Definition Re := rho (.\ "Re", "n", "s"; (!!f "n") (.\"t"; ( !!(lam((int term_eqb) 0)) "t" "s" !!I (.\ "", ""; "Re" (!!(int S) "n") "s") !!I))
                                                                     (.\ ""; "Re" (!!(int S) "n") "s") !!I).

  Lemma Re_closed : proc Re.
  Proof.
    unfold Re;simpl. Lproc.
  Qed.

  Hint Resolve Re_closed : LProc.

  Lemma Re_S (n:nat) (s:term) : converges (Re (enc (S n)) (enc s)) -> converges (Re (enc n) (enc s)).
  Proof.
    intros H. apply Eval.eval_converges in H as [x [Hx lx]].
    assert (clx : closed x) by (rewrite <- Hx; Lproc).  
    destruct (total_f n) as [t H]. eapply eval_converges. unfold Re. simpl. recRem P.
    recStep P. Lsimpl. rewrite H.
    Lsimpl. instantiate (1:=match t with None => _ | _ => _ end). destruct t;Lsimpl.
    instantiate (1:=match term_eqb t0 s with true => _ | _ => _ end).
    destruct (term_eqb_spec t s);Lsimpl.
  Qed.

  Lemma Re_ge n m s : n >= m -> converges (Re (enc n) (enc s)) -> converges (Re (enc m) (enc s)).
  Proof.
    induction 1; eauto using Re_S.
  Qed.

  Lemma Re_converges (n:nat) s : converges (Re (enc n) (enc s)) -> exists n:nat, f (enc n) == enc (Some s).
  Proof.
    intros H. apply Eval.eval_converges in H as [v [Hv lx]].
    assert (clx : closed v) by (rewrite <- Hv;Lproc).
    
    apply star_pow in Hv. destruct Hv as [m H].
    revert n H.
    eapply complete_induction with (x := m). clear m; intros m IHm n H.
    destruct (total_f n) as [t Ht].
    -eassert (H':(Re (enc n)) (enc s) >* _).
     etransitivity. unfold Re. rewrite rho_correct;fold Re. 1-3:cbn. 2-3:Lproc.
     Lsimpl. apply equiv_lambda in Ht;[|Lproc]. 
     rewrite Ht. etransitivity. Lsimpl.
     etransitivity. 
     refine (_:_ >* match t with None => _ | Some _ => _ end).
     destruct t;Lsimpl'.
     +Lsimpl'. refine (_ : _ >* if term_eqb t s then _ else _).
      destruct (term_eqb t s).
      Lsimpl;reflexivity.
      Lsimpl. 
     +Lsimpl.
     +reflexivity.
     +eapply star_pow in H' as [n' H'].
      edestruct (parametrized_confluence uniform_confluence H H') as (i1&i2&u&le1&le2&R1&R2&eq_i).
      assert (n'>0).
      {destruct n'. 2:omega. hnf in H'. destruct t. destruct term_eqb in H'. inv H'. inv H'. eapply eq_subrelation in H1. eapply enc_extinj in H1. omega. exact _. inv H'. eapply eq_subrelation in H1. eapply enc_extinj in H1. omega. exact _. }
      destruct i1.
      2:{inv R1. destruct H1. inv lx;inv H1. }
      inv R1. 
      
      destruct t. destruct (term_eqb_spec t s).
      *subst s. eauto. 
      *eapply IHm. 2:exact R2. omega.
      *eapply IHm. 2:exact R2. omega.
  Qed.
  
        
End Fix_f.

(** * Recursive Enumerability implies semi decidability *)
 
Lemma RE_Acc P : RE P -> lacc P.
Proof.
  intros [f [f_cls [f_total f_enum]]].
  

  pose (test_n := fun f t n =>
               let u := g_inv n in
               match f u with
                 Some t' => term_eqb t t'
               | None => false
               end).
  Local Arguments fst : clear implicits.
  Local Arguments snd : clear implicits.
  assert (computable test_n). unfold test_n.
  extract.
  unfold lacc. 
  exists (lam (mu (lam ((int test_n) f 1 0)))).
  split;[Lproc|].
  intros t.
  split. 
  - intros H.
    eapply f_enum in H. destruct H as [n H].
    unfold pi.
    eapply eval_converges.
    Lsimpl.
    match goal with | |- eval (app mu ?F) _ => edestruct (mu_complete (P:=F)) as [v R] end.
    +Lproc.
    +intros. eexists;Lsimpl.  
     pose  mu_complete.
Admitted. 
     (*
    eapply LTactics.star_step_app_proper;[symmetry|reflexivity|]. 
    rewrite (mu_complete _). ;intros H'.
    
    Check mu_complete. 
    Check mu_complete. 
    edestruct (mu_complete (n:=n)). 
    SearchAbout mu. 
    SearchAbout converges. 
    eexists. 
    assert (converges (Re f (enc n) (tenc t))). exists I;split;[|Lproc].
    assert (E : Eq (tenc t) (tenc t) == true) by (eapply Eq_correct; reflexivity). 
    rewrite Re_rec, H;auto. Lsimpl.
    unfold pi. 
    rewrite Hu. eapply Re_ge. Lproc. firstorder. omega. eassumption.
  - intros. unfold pi in H. rewrite Hu in H.
    assert (A : forall n, f (enc n) == none \/ exists s, f (enc n) == some (tenc s)) by firstorder.
    destruct (Re_converges f_cls A H) as [n B]. destruct (f_total n) as [C | C].
    + rewrite B in C. simpl in C. eapply eq_lam in C. inv C.
    + destruct C as [t' C]. assert (t = t'). destruct C as [C1 C2]. rewrite C1 in B.
      eapply eqTrans with (s := oenc (Some t')) in B. simpl in B.     
      eapply eq_lam in B. inv B. now eapply tenc_injective. 
      symmetry; clear B; Lsimpl.
      subst. firstorder.
Qed.*)

(** * Semi decidability implies recursive enumerability *)


Lemma pi_eval u s : pi u s -> exists v, eval (u (enc s)) v.
Proof.
  intros [v [? ?]]. exists v.
  split. now eapply equiv_lambda. assumption.
Qed.

Theorem Acc_RE P : lacc P -> RE P.
Proof.
  intros [u [proc_u Hu]]. unfold RE.
  pose (f := fun (x : term) =>
               let i := c (g x) in
               let t := g_inv (snd _ _ i) in
               match eva (fst _ _ i) (app u (enc t)) with
                 Some _ => Some t
               | None => None
               end).
assert (computable f).
Local Arguments fst : clear implicits.
Local Arguments snd : clear implicits.
 unfold f, enc. cbn. 
  internalize auto.
  exists (int f).
  split;[|split].
  -Lproc. 
  -intros.
   remember (f n) as o eqn: eqo.
   assert (o=f n) by auto.
   unfold f in eqo;cbn in eqo;subst o. 
   destruct (eva _ _) eqn: R;[right|left].
   +apply eva_seval in R. apply seval_eval in R. 
    eexists. rewrite H. split. Lsimpl.
    apply Hu. destruct R as [R ?]. exists t. split;try Lproc. now rewrite R.
   +Lsimpl. now rewrite <- H.
  -intros s Ps.
   apply Hu in Ps. apply Eval.eval_converges in Ps as [t Ps]. apply eval_seval in Ps as [n Ps].
   apply seval_eva in Ps. 
   unfold pi in Ps. unfold f.
   eexists (g_inv (c_inv((n,g s))));cbn. Lsimpl. 
   rewrite g_g_inv, c_c_inv. simpl.  rewrite g_inv_g. now rewrite Ps. 
Qed.

