Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Classical_sets.
Require Import Coq.Sets.Image.
Require Import CpdtTactics.

Set Implicit Arguments.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*             A few useful tactics              *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Ltac ifcase :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Ltac ifcaseH :=
  match goal with
  | [ H : context[if ?X then _ else _] |- _ ] => destruct X
  end.

Ltac matchcase :=
  match goal with
  | [ |- context[match ?term with
                 | _ => _
                 end] ] => destruct term
  end.

Ltac matchcaseH :=
  match goal with
  | [ H: context[match ?term with
                 | _ => _
                 end] |- _ ] => destruct term
  end.


Ltac applyH :=
  match goal with
  | [H : _ -> _ |- _] => progress (apply H)
  end.

Ltac applyHinH :=
  match goal with
  | [H1 : _ -> _ , H2 : _ |- _] => apply H1 in H2
  end.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           Value/Type Definitions              *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Axiom V : Type.
Notation Ty := (Ensemble V).

Notation emptyTy := (Empty_set V).
Notation anyTy := (Full_set V).
Notation tyOr := (Union V).
Notation tyAnd := (Intersection V).
Notation tyDiff := (Setminus V).
Notation tyNot := (tyDiff anyTy).

Notation IsEmpty t := (~ Inhabited V t).
Notation IsInhabited t := (Inhabited V t).
Axiom IsEmpty_dec : forall (t: Ty), {IsEmpty t} + {IsInhabited t}.
Notation IsA v T := (In V T v).
Axiom IsA_dec : forall (v:V) (t: Ty), {IsA v t} + {~ IsA v t}.
Notation Subtype T1 T2 := (Included V T1 T2).

Hint Unfold Included Setminus.
Hint Constructors Union Intersection Inhabited.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*         Basic Type Lemmas/Tactics             *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Lemma IsEmpty_eq : forall t,
    IsEmpty t ->
    t = emptyTy.
Proof.
  intros t Hmt.
  apply Extensionality_Ensembles. constructor.
  intros v Hv. assert False. apply Hmt. exists v. auto.
  contradiction. intros v Hv. inversion Hv.
Qed.


Lemma no_empty_val : forall v P,
    IsA v emptyTy -> P.
Proof.
  intros v P Hmt. inversion Hmt.
Qed.

Lemma no_empty_val_indirect : forall v T P,
    IsA v T -> IsEmpty T -> P.
Proof.
  intros v T P Hv Hmt. rewrite (IsEmpty_eq Hmt) in Hv.
  eapply no_empty_val; eauto.
Qed.

Lemma tyOr_empty_l : forall t,
    tyOr emptyTy t = t.
Proof. crush. Qed.

Lemma tyOr_empty_r : forall t,
    tyOr t emptyTy = t.
Proof.
  intros. rewrite Union_commutative.
  crush.
Qed.

Lemma tyAnd_empty_l : forall t,
    tyAnd emptyTy t = emptyTy.
Proof. crush. Qed.

Lemma tyAnd_empty_r : forall t,
    tyAnd t emptyTy = emptyTy.
Proof. crush. Qed.

Lemma not_IsA_tyOr : forall x T1 T2,
    ~ IsA x (tyOr T1 T2) ->
    ~ IsA x T1 /\ ~ IsA x T2.
Proof. crush. Qed.


Hint Rewrite tyOr_empty_l tyOr_empty_r tyAnd_empty_l tyAnd_empty_r.

Hint Extern 1 =>
match goal with
| [H : IsA ?x emptyTy |- ?P] =>
  apply (no_empty_val P H)
| [H : IsA ?x ?T, H' : IsEmpty ?T |- ?P] =>
  apply (no_empty_val_indirect x P H H')
end.

Hint Extern 1 (IsA _ _) =>
match goal with
| [H : IsA ?x (tyAnd ?T1 ?T2) |- IsA ?x ?T1]
  => destruct H; assumption
| [H : IsA ?x (tyAnd ?T1 ?T2) |- IsA ?x ?T2]
  => destruct H; assumption
| [H1 : IsA ?x ?T1, H2 : IsA ?x ?T2 |- IsA ?x (tyAnd ?T1 ?T2)]
  => constructor; assumption
| [H1 : IsA ?x ?T1 |- IsA ?x (tyOr ?T1 _)]
  => left; exact H1
| [H2 : IsA ?x ?T2 |- IsA ?x (tyOr _ ?T2)]
  => left; exact H2
end. 

Ltac destruct_IsA :=
  match goal with
  | [H : IsA _ _ |- _] => destruct H
  end.

Ltac inv_IsA_tyAnd :=
  match goal with
  | [H : IsA _ (tyAnd _ _) |- _] => destruct H
  end.

Ltac inv_IsA_tyOr :=
  match goal with
  | [H : IsA _ (tyOr _ _) |- _] => destruct H
  end.

Ltac inv_exists :=
  match goal with
  | [H : exists x, _ |- _] => destruct H
  end.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*       Function Related Definitions            *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* the result of function application *)
Inductive res : Type :=
| Err : res (* invalid argument/type error *)
| Bot : res (* non-termination *)
| Res : V -> res. (* a value result *)
Hint Constructors res.


(* We use a shallow embedding in Gallina's functions
   to model the target language functions. *)
Definition fn := (V -> res).



(* An `interface` is the set of arrows that describe a
   function (i.e. an intersection of 1 or more arrows). We
   use a pair for each arrow, where the fst is the domain
   and the snd is the codomain. *)
Inductive interface : Type :=
| IBase: (Ty * Ty) -> interface
| ICons : (Ty * Ty) -> interface -> interface.
Hint Constructors interface.



(* The domain for an interface is the union of each
   individual arrow's domain. *)
Fixpoint i_dom (i : interface) : Ty :=
  match i with
  | IBase (T1,_) => T1
  | ICons (T1,_) i' => tyOr T1 (i_dom i')
  end.
Hint Unfold i_dom.


(* Calculates the result type of calling a function which
   has the arrow type `a` on value `v`. *)
Fixpoint a_result (a : (Ty * Ty)) (v : V) : option Ty :=
  if IsA_dec v (fst a)
  then Some (snd a)
  else None.
Hint Unfold a_result.


(* Function Arrow *)
(* I.e., what it means for a function `f` to conform to the
   description given by arrow `a`. *)
Definition FnA (f : fn) (a : (Ty * Ty)) : Prop :=
forall x T,
  a_result a x = Some T ->
  (f x = Bot \/ exists y, f x = Res y /\ IsA y T).
Hint Unfold FnA.

(* Calculates the result type of calling a function which
   has the interface type `i` on value `v`. *)
Fixpoint i_result (i : interface) (v : V) : option Ty :=
  match i with
  | IBase a => a_result a v
  | ICons a i' => match a_result a v, i_result i' v with
                  | None, None => None
                  | Some T, None => Some T
                  | None, Some T => Some T
                  | Some T, Some T' => Some (tyAnd T T')
                  end
  end.
Hint Unfold i_result.

(* Function Interface *)
(* I.e., what it means for a function `f` to conform to the
   description given by interface `i`. *)
Definition FnI (f : fn) (i : interface) : Prop :=
  forall x T,
    i_result i x = Some T ->
    f x = Bot \/ (exists y, (f x = Res y /\ IsA y T)).
Hint Unfold FnI.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*       Function Related Lemmas/Tactics         *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma FnI_base : forall f a,
    FnI f (IBase a) ->
    FnA f a.
Proof.
  unfold FnI. unfold FnA.
  intros f [T1 T2] H x T Har.
  simpl in *.
  specialize H with x T2.
  ifcaseH; inversion Har; subst; auto.
Qed.


Ltac same_Res :=
  match goal with
  | [H1 : ?f ?v = Res ?x , H2 : ?f ?v = Res ?y |- _] =>
    rewrite H1 in H2; inversion H2; subst; clear H2
  end.


Lemma FnI_first : forall f a i,
    FnI f (ICons a i) ->
    FnA f a.
Proof.
  unfold FnI. unfold FnA.
  intros f [T1 T2] i H x T Har.
  specialize (H x).
  unfold a_result in *. simpl in *.
  ifcaseH; matchcaseH; crush.
  specialize (H (tyAnd T e)); crush.
  inv_IsA_tyAnd; crush; eauto.
Qed.
  
Lemma FnI_rest : forall f a i,
    FnI f (ICons a i) ->
    FnI f i.
Proof.
  intros f [T1 T2] i Hfi.
  unfold FnI in *.
  intros x T Hres.
  specialize (Hfi x).
  simpl in *.
  ifcaseH; matchcaseH; inversion Hres; subst; eauto.
  specialize (Hfi (tyAnd T2 T));
    intuition; crush; inv_IsA_tyAnd; eauto.
Qed.

Lemma FnI_cons : forall f a i,
    FnA f a ->
    FnI f i ->
    FnI f (ICons a i).
Proof.
  intros f [T1 T2] i Ha Hi.
  unfold FnI in *. unfold FnA in *.
  intros x T Hres.
  specialize (Ha x). specialize (Hi x).
  simpl in *.
  destruct (IsA_dec x T1) as [Hx1 | Hx1].
  remember (i_result i x) as Hxr.
  destruct Hxr as [T'|]; inversion Hres; subst.
  destruct (Ha T2 eq_refl). left; assumption.
  destruct (Hi T' eq_refl). left; assumption.
  repeat inv_exists. crush.
  same_Res.
  right.
  match goal with
  | [H : f x = Res ?y |- _] => exists y
  end; crush.
  destruct (Ha T eq_refl); crush; eauto.
  remember (i_result i x) as Hxr.
  destruct Hxr as [T'|]; inversion Hres; subst.
  apply Hi; auto.
Qed.


Ltac inv_FnI :=
  match goal with
  | [H : FnI _ _ |- _] => inversion H; subst
  end.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*        Function Inversion Definitions         *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* Consider function `f` of type `a`. This function
   calculates what type an argument `x` must _not_
   have had  if `(f x) ↝ v` and `v ∈ outT` *)
Fixpoint a_neg (a : (Ty * Ty)) (outT : Ty) : Ty :=
  if IsEmpty_dec (tyAnd (snd a) outT)
  then (fst a)
  else emptyTy.

(* Consider function `f` of type `i`. This function
   calculates what type an argument `x` must _not_ 
   have had if `(f x) ↝ v` and `v ∈ outT` *)
Fixpoint i_neg (i : interface) (outT : Ty) : Ty :=
  match i with
  | IBase a => a_neg a outT
  | ICons (S1,S2) i' =>
    let T1 := a_neg (S1,S2) outT in
    let T2 := i_neg i' outT in
    let T3 := tyAnd S1 (i_neg i' (tyAnd S2 outT)) in
    tyOr T1 (tyOr T2 T3)
  end.

(* Consider function `f` of type `i`. This function
   calculates what type an argument `x` must _have_
   had if `(f x) ↝ v` and `v ∈ outT` *)
Definition i_inv (i : interface) (outT : Ty) : Ty :=
  tyDiff (i_dom i) (i_neg i outT).


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*      Function Inversion Lemmas/Tactics        *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma FnA_res_ty : forall T1 T2 f x y,
    IsA x T1 ->
    f x = Res y ->
    FnA f (T1,T2) ->
    IsA y T2.
Proof.
  intros T1 T2 f x y Hx Hfx Hfa.
  assert (f x = Bot \/ (exists y, (f x = Res y /\ IsA y T2)))
    as Hex.
  eapply Hfa; crush.
  ifcase; crush.
  crush.
Qed.

Hint Extern 1 (IsA _ _) =>
match goal with
| [Hx : IsA ?x ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnA ?f (?T1,?T2)
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy HFnA)
| [Hx : IsA ?x ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (IBase (?T1,?T2))
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
| [Hx : IsA ?x ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (ICons (?T1,?T2) _)
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
  end.


Lemma i_neg_sub : forall i T1 T2,
    Subtype T2 T1 ->
    Subtype (i_neg i T1) (i_neg i T2).
Proof with auto.
  intros i. induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros T T' Hsub x Hx. simpl in *.
    destruct (IsEmpty_dec (tyAnd T2 T'))
      as [Hmt' | Hnmt']...
    destruct (IsEmpty_dec (tyAnd T2 T))
      as [Hmt | Hnmt]...
    destruct (IsEmpty_dec (tyAnd T2 T))
      as [Hmt | Hnmt]...
    assert False. apply Hmt.
    destruct Hnmt' as [y Hy]. exists y; eauto.
    contradiction.
  }
  {
    intros T T' Hsub x Hx.
    simpl in *.
    destruct (IsEmpty_dec (tyAnd T2 T)) as [Hmt | Hnmt].
    {
      destruct (IsEmpty_dec (tyAnd T2 T')) as [Hmt' | Hnmt'].
      {
        destruct Hx as [x Hx | x Hx]...
        destruct Hx as [x Hx | x Hx]...
        right; left; eapply IH; eauto.
      }
      {
        right.
        assert False as impossible.
        {
          eapply Hmt.
          destruct Hnmt' as [y Hy1].
          exists y. eauto.
        }
        contradiction.
      }
    }
    destruct (IsEmpty_dec (tyAnd T2 T')) as [Hmt' | Hnmt'].
    {
      right.
      destruct Hx as [x Hx | x Hx]...
      destruct Hx as [x Hx | x Hx]...
      {
        left; eapply IH; eauto.
      }
      {
        destruct Hx...
        right; split...
        apply (IH (tyAnd T2 T) (tyAnd T2 T'))...
      }
    }                  
    {
      destruct Hx as [x Hx | x Hx]...
      destruct Hx as [x Hx | x Hx]...
      right. left. eapply IH; eauto.
      right. right; split...
      destruct Hx as [x Hx' Hx'']...
      apply (IH (tyAnd T2 T) (tyAnd T2 T'))...
    }
  }
Qed.

Ltac apply_fun :=
  match goal with
  | [H1 : IsA ?x ?T1,
          Hf : FnI ?f (IBase (?T1,?T2)),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (IsA y T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  | [H1 : IsA ?x ?T1,
          Hf : FnA ?f (?T1,?T2),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (IsA y T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  end.

Lemma in_i_neg : forall i v v' f T,
    FnI f i ->
    IsA v (i_neg i T) ->
    f v = Res v' ->
    ~ IsA v' T.
Proof with auto.
  intros i.
  induction i as [[T1 T2] | [T1 T2] i' IH];
    intros v v' f T Hfi Hv Hfv Hcontra.
  (* IBase (Arrow T1 T2) *)
  {
    simpl in *.
    ifcaseH; crush.
    applyH.
    match goal with
    | [H : ?f ?v = Res ?v' |- _] => exists v'
    end.
    apply_fun...
  }
  (* ICons (Arrow T1 T2) i' *)
  {
    simpl in *.
    assert (FnA f (T1,T2)) as Hfa by (eapply FnI_first; eauto).
    assert (FnI f i') as Hfi' by (eapply FnI_rest; eauto).
    destruct (IsEmpty_dec (tyAnd T2 T)) as [Hmt | Hnmt]...
    {
      inv_IsA_tyOr.
      {
        apply_fun. apply Hmt; eauto.
      }
      {
        inv_IsA_tyOr.
        {
          eapply IH; eauto. 
        }
        {
          inv_IsA_tyAnd.
          apply_fun. apply Hmt; eauto.
        }
      }
    }
    {
      rewrite tyOr_empty_l in *.
      destruct Hv as [v Hv | v Hv].
      {
        eapply IH; eauto.
      }
      {
        destruct Hv as [v Hv1 Hv2].
        eapply IH; eauto.
      }
    }
  }
Qed.

Lemma not_in_i_neg : forall i v v' f T,
    FnI f i ->
    f v = Res v' ->
    IsA v' T ->
    ~ IsA v (i_neg i T).
Proof.
  intros i v v' f T Hfi Hfv Hv' Hcontra.
  eapply in_i_neg; eauto.
Qed.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           Inversion Definition                *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Definition Inv (i : interface) (outT inT: Ty) : Prop :=
  forall (f:fn),
    FnI f i ->
    forall (v v':V),
      IsA v (i_dom i) ->
      f v = Res v' ->
      IsA v' outT ->
      IsA v inT.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                 Soundness                     *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* Interface Inversion Soundness 
   i.e. the input type we predict is correct *)
Theorem i_inv_sound : forall i outT,
    Inv i outT (i_inv i outT).
Proof with crush.
  intros i outT f Hint v v' Hv Hf Hv'.
  unfold i_inv in *.
  constructor; auto.
  intros Hcontra.
  eapply in_i_neg; eauto.
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*         Axioms for proving minimality         *)
(*                                               *)
(* i.e. basically we assume if a codomain is     *)
(* inhabited, then there exists a function which *)
(* will map inputs to those codomain values.     *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Definition MapsTo (f : fn) (i : interface) : Prop :=
  forall v T,
    i_result i v = Some T ->
    IsInhabited T ->
    exists v', f v = Res v' /\ IsA v' T.


Definition MapsToTarget (f : fn) (i : interface) (tgt : Ty) : Prop :=
  forall v T,
    i_result i v = Some T ->
    IsInhabited (tyAnd T tgt) ->
    exists v', f v = Res v'
               /\ IsA v' (tyAnd T tgt).

Axiom exists_fn : forall i,
    exists f, FnI f i /\ MapsTo f i.

Axiom exists_target_fn : forall i outT,
    exists f, FnI f i /\ MapsToTarget f i outT.



(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*         Lemmas related to i_result            *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)
  
Lemma i_result_None : forall i x outT,
    IsA x (i_dom i) ->
    i_result i x = None ->
    IsA x (i_neg i outT).
Proof with auto.
  intros i; induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros x outT Hdom Hires.
    simpl in *.
    destruct (IsA_dec x T1) as [Hx | Hx]; crush.
  }
  {
    intros x outT Hx Hires.
    simpl in *.
    destruct (IsA_dec x T1) as [Hx1 | Hx1].
    {
      destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt | Hnmt].
      {
        left. assumption.
      }
      {
        right.
        remember (i_result i' x) as ires'.
        destruct ires' as [T' |].
        inversion Hires. inversion Hires.
      }      
    }
    {
      destruct Hx as [x Hx | x Hx]; try solve[contradiction].
      right. left.
      apply IH... matchcaseH; crush.
    }
  }
Qed.

  
Lemma i_result_Some : forall i x T outT,
    i_result i x = Some T ->
    IsEmpty (tyAnd T outT) ->
    IsA x (i_neg i outT).
Proof with auto.
  intros i x; induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros T outT Hires Hmt.
    simpl in *.
    destruct (IsA_dec x T1) as [Hx1 | Hx1]; crush.
    destruct (IsEmpty_dec (tyAnd T outT)) as [Hmt' | Hmt']...
    assert False as contradiction. apply Hmt.
    {
      destruct Hmt' as [y Hy].
      exists y...
    }
    contradiction.
  }
  {
    intros T outT Hires Hmt.
    simpl in *.
    destruct (IsA_dec x T1) as [Hx1 | Hx1].
    {
      destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt2 | Hnmt2].
      {
        left...
      }
      {
        right.
        destruct (i_result i' x) as [S |]; try solve[crush].
        specialize (IH S).
        inversion Hires; subst. clear Hires.
        assert (IsEmpty (tyAnd S (tyAnd T2 outT))) as Hmt3.
        {
          intros Hcontra. apply Hmt. inversion Hcontra as [y Hy].
          exists y. repeat inv_IsA_tyAnd. split...
        }
        right. split...
      }
    }
    {
      destruct (i_result i' x) as [S |]; try solve[crush].
      inversion Hires; subst.
      specialize (IH T outT eq_refl Hmt).
      auto.
    }
  }
Qed.    

  
(* Interface Inversion Minimality
   i.e. the input type we predict is minimal *)
Lemma i_inv_exists_fn : forall i outT x,
    IsA x (i_inv i outT) ->
    exists f y, FnI f i /\ f x = Res y /\ IsA y outT.
Proof with auto.
  intros i outT x Hx.
  unfold i_inv in Hx.
  destruct Hx as [HxIs HxNot].
  remember (i_result i x) as xres.
  destruct xres as [S |].
  {
    symmetry in Heqxres.
    destruct (IsEmpty_dec (tyAnd S outT)) as [Hmt | Hnmt].
    {
      assert (IsA x (i_neg i outT)) as impossible.
      {
        eapply i_result_Some; eauto.
      }
      contradiction.
    }
    {
      destruct (exists_target_fn i outT)
        as [f [Hfi Hmaps]].
      unfold MapsToTarget in Hmaps.
      destruct (Hmaps x S Heqxres Hnmt) as [y [Hfx Hy]].
      exists f. exists y...
    }
  }
  {
    assert (IsA x (i_neg i outT)) as impossible.
    {
      eapply i_result_None; eauto.
    }
    contradiction.
  }
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                   Minimality                  *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Theorem i_inv_minimal : forall i outT inT,
    Inv i outT inT ->
    Subtype (i_inv i outT) inT.
Proof with auto.
  intros i outT inT Hinv x Hx.
  unfold Inv in Hinv.
  destruct (i_inv_exists_fn Hx) as [f [y [Hf [Hres Hy]]]].
  specialize (Hinv f Hf x y). eapply Hinv; eauto.
  destruct Hx...
Qed.


