From Undecidability.FOLP Require Import FOL.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Local Notation "[||]" := (Vector.nil _) : vector_scope.
Local Notation "h ':::' t" := (Vector.cons _ h _ t) (at level 60, right associativity) : vector_scope.

Local Notation " [| x |] " := (x ::: [||]) : vector_scope.
(* Notation " [| x ; y ; .. ; z |] " := (Vector.cons x (Vector.cons y .. (Vector.cons z (Vector.nil)) ..)) : vector_scope. *)

(** ** Pseudo-HOAS representation for parsing *)

Inductive bterm `{Signature} :=
| bVar : nat -> bterm
| bFapp (f : Funcs) (v : list bterm) : bterm
| bApp : bterm -> bterm -> bterm
| bEmbedT : term -> bterm.

Inductive bform `{Signature} :=
  bImpl : bform -> bform -> bform
| bAll : (nat -> bform) -> bform
| bPred (P : Preds) (v : list bterm) : bform
| bPapp : bform -> bterm -> bform
| bFree : (nat -> bform) -> bform
| bEmbed : form -> list bterm -> bform.
Arguments bPred {H} _ _%vector_scope.

Notation "'∀' x .. y , p" := (bAll (fun x => .. (bAll (fun y => p)) ..))
  (at level 100, x binder, right associativity,
   format "'[' '∀'  '/  ' x  ..  y ,  '/  ' p ']'").

Notation "'free' x .. y , p" := (bFree (fun x => .. (bFree (fun y => p)) ..))
  (at level 100, x binder, right associativity,
   format "'[' 'free'  '/  ' x  ..  y ,  '/  ' p ']'").

Notation "x --> y" := (bImpl x y) (at level 55, right associativity).

Coercion bApp : bterm >-> Funclass.
Coercion bPapp : bform >-> Funclass.

Notation "! P" := (bPred P List.nil) (at level 10).

Notation "! P" := (existT _ _ P) (at level 10, format "'!' P").
Notation "! P" := (bPred (existT _ _ P) List.nil) (at level 10, format "'!' P").
Notation "$ f" := (bFapp (existT _ _ f) List.nil) (at level 2, format "'$' f").

(* Conversion *)

Fixpoint ofold {X} (v : list (option X)) : option (list X) :=
  match v with
    nil => Some nil
  | cons x v => match x, ofold v with Some y, Some v => Some (cons y v) | _, _ => None end
  end.

Definition to_vec {X} n (l : list X) : option (vector X n).
Proof.
  destruct (PeanoNat.Nat.eq_dec n (length l)).
  - subst. exact (Some (Vector.of_list l)).
  - exact None.
Defined.

Fixpoint rmApps `{Signature} (t : bterm) : bterm :=
  match t with
  | bApp t1 t2 => match rmApps t1 with bFapp f v => bFapp f (List.app v (cons (rmApps t2) nil)) | t1 => bApp t1 (rmApps t2) end
  | bFapp f v => bFapp f (List.map rmApps v)
  | bEmbedT t  => bEmbedT t
  | x => x
  end.    

Fixpoint rmPapps `{Signature} (t : bform) : bform :=
  match t with
  | bPapp t1 t2 => match rmPapps t1 with
                  | bPred P v => bPred P (List.app v (cons (rmApps t2) nil)) 
                  | bEmbed f v => bEmbed f (List.app v (cons (rmApps t2) nil)) 
                  | t1 => bPapp t1 (rmApps t2) end
  | bPred P v => bPred P (List.map rmApps v)
  | bAll f => bAll (fun x => rmPapps (f x))
  | bFree f => bFree (fun x => rmPapps (f x))
  | bImpl p1 p2 => bImpl (rmPapps p1) (rmPapps p2)
  | bEmbed f v => bEmbed f (List.map rmApps v)
  end.    

Fixpoint conv_ter `{Signature} i t {struct t} : option (term) :=
  match t with
  | bVar m => Some (var_term (i - m)) 
  | bFapp f v => match ofold (List.map (conv_ter i) v) with Some v => match to_vec (fun_ar f) v with Some v => Some (Func f v) | _ => None end | _ => None end
  | _ => None
  end.

(* Definition subst_list `{sig} n (L : list (term n)) : fin (length L)  -> term. *)
(* Proof. *)
(*   intros. eapply to_nat in X as [m ?]. *)
(*   eapply nth_error_Some in l. *)
(*   destruct (nth_error L m). exact t. *)
(*   tauto. *)
(* Defined.   *)

Lemma ofold_cases X (L : list (option X)) : {y | ofold L = Some y /\ length y = length L} + {ofold L = None}.
Proof.
  induction L.
  - cbn. left. exists nil. eauto.
  - cbn. destruct a.
    + destruct IHL as [ (? & ? & ?) | ].
      * rewrite H. left. eexists. split; eauto. cbn. congruence.
      * rewrite e. eauto.
    + eauto.
Defined.



Lemma map_length A B f : forall l, length (@map A B f l) = length l.
Proof.
  induction l; simpl; auto.
Defined.
  
(* Definition conv_form `{Signature} (i : nat) : form -> list bterm -> option form. *)
(* Proof. *)
(*   intros. epose (List.map (conv_ter i) X0). *)
(*   destruct (ofold_cases l) as [(? & ? & ?) | ]. *)
(*   + pose (subst_list x). *)
(*     assert (length X0 = length l ) by (subst l; now rewrite map_length). *)
(*     rewrite <- H1 in *. rewrite <- H2 in *. *)
(*     apply Some. *)
(*      eapply (subst_form t X). *)
(*     + exact None. *)
(*   - exact None. *)
(* Defined. *)
    
Fixpoint conv `{Signature} i (phi : bform) : option (form) :=
  match phi with
  | bImpl phi psi => match conv i phi, conv i psi with Some phi, Some psi => Some (Impl phi psi) | _, _ => None end
  | bAll f => match conv (S i) (f (S i)) with Some phi => Some (All phi) | _ => None end
  | bFree f => match conv (S i) (f (S i)) with Some phi => Some phi | _ => None end                              
  | bPred P v => match ofold (List.map (conv_ter i) v) with Some v => match to_vec (pred_ar P) v with Some v => Some (Pred P v) | _ => None end | _ => None end
  | bEmbed phi v => Some phi
  | _ => None
  end.

(* Fixpoint countfree `{sig} t : nat := *)
(*   match t with *)
(*   | bImpl phi psi => countfree phi + countfree psi *)
(*   | bAll f => countfree (f 0) *)
(*   | bPapp phi _ => countfree phi *)
(*   | bPred P v => 0 *)
(*   | bFree f => 1 + countfree (f 0) *)
(*   | bEmbed _ _ => 0 *)
(*   end.   *)

Definition convert `{Signature} f := (@conv _ 0 (rmPapps f)).

Notation "=: f" := (ltac:(let y := eval cbv -[subst_form] in (convert f) in match y with Some ?x => exact x | _ => fail 10 end)) (at level 200).

(* Notation "=:( x ) f" := (ltac:(let y := eval cbv in (@conv _ x 0 (rmPapps f)) in match y with Some ?x => exact x | _ => fail 10 end)) (at level 5). *)


(** ** More convenient way to define signatures *)

Inductive what := pred | func.
Definition make_sig (T : what -> nat -> Type) : Signature :=
  {| Funcs := {n & T func n} ;
     fun_ar := @projT1 _ _ ;
     Preds := {n & T pred n} ;
     pred_ar := @projT1 _ _ |}.

(** ** Example *)

Module minimal.

  Inductive min_sig : what -> nat -> Type :=
    e  : min_sig func 0 
  | f1 : min_sig func 1
  | f2 : min_sig func 1
  | P  : min_sig pred 2
  | Q  : min_sig pred 0.
  Instance min : Signature := make_sig min_sig.
  Coercion V := @bVar min.

  Definition phi1 :==: ∀ x, !P x x.
  Print phi1.

  Definition phi2 :==: free y z, ∀ x, !P x y --> !P z x.
  Print phi2.
      
  Definition phi3 :==: ∀ x y, !P ($f1 $e) y --> (∀ z, !P x z) --> !Q.
  Print phi3.
End minimal.
  
Notation "£ f" := (bEmbed f List.nil) (at level 2). 
(* Notation "s ∙ L" := (subst_form (subst_list L) s) (at level 200). *)

Module PA.

  Inductive PA_sig : what -> nat -> Type :=
  | O : PA_sig func 0
  | S : PA_sig func 1
  | Eq : PA_sig pred 2.
  Instance PA : Signature := make_sig PA_sig.
  Coercion V' := @bVar PA.
  
  Definition PA_inj :==: ∀ x y, !Eq ($S x) ($S y) --> !Eq x y.
  Print PA_inj.
    
  Definition PA_ind (Phi : form) :==: ∀ x, £Phi $O --> (∀ x, £Phi x --> £Phi ($S x)) --> ∀ x, £Phi x.
  Print PA_ind.
  
  Definition functional (phi : form) :==: ∀ x y y', £phi x y --> £phi x y' --> !Eq y y'.
  Print functional.

  Definition replacement (Phi : form) :==: £(functional Phi) --> ∀ x, !Eq $O x.
  Print replacement.
 
End PA.
