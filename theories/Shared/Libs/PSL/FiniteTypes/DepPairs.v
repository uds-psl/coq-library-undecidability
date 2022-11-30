(* Instance declaration for dependent pairs *)

From Undecidability.Shared.Libs.PSL Require Import Base FinTypes.
From Coq Require Import EqdepFacts List.

#[global]
Instance eqType_depPair (F : eqType) (a : F -> eqType) : eq_dec {f : F & a f}.
Proof.
  intros [x fx] [y fy]. eapply dec_transfer. now rewrite eq_sigT_iff_eq_dep.
  decide (x=y).
  subst y. decide (fx = fy).
  +subst fy. left. reflexivity.
  +right. intros eq. apply n. apply Eqdep_dec.eq_dep_eq_dec in eq. auto. intros. decide (x0=y);econstructor;eassumption;eauto.
  +right. intros eq. now inv eq.
Qed.

#[global]
Instance finType_depPair (F : finType) (a : F -> finType) : finTypeC (EqType( {f : F & a f} )).
Proof.
  exists (nodup (@eqType_dec _) (concat (map (fun f => map (fun x => existT a _ x) (elem (a f))) (elem F)))).
  intros H. hnf in H. apply dupfreeCount. now apply NoDup_nodup.
  apply nodup_In. apply in_concat.
  exists ((fun f : F => map (fun x : a f => existT (fun x0 : F => a x0) f x) (elem (a f))) (projT1 H)).
  split.
  -rewrite in_map_iff. eexists. split. reflexivity.
   apply countIn. setoid_rewrite enum_ok. lia. 
  -rewrite in_map_iff. destruct H. cbn. exists e. split.
   +reflexivity.
   +apply countIn. setoid_rewrite enum_ok. lia.
Qed.

#[export] Hint Extern 4 (finTypeC (EqType ({_ : _ & _}))) => eapply finType_depPair : typeclass_instances.
