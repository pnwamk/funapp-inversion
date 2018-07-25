Require Import Coq.ZArith.BinInt.
Require Import List.
Require Import Omega.
Require Import Ensembles.
Require Import Classical_sets.
Require Import Coq.Logic.Classical_Prop.
Require Import Powerset.
Require Import Image.
Require Import Relations.
Require Import CpdtTactics.
Require Import LibTactics.
Require Import Misc.

Set Implicit Arguments.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*       Set/Type/Value Definitions              *)
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


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           Function Definitions                *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)



(* A single function arrow *)
Inductive arrow : Type :=
| Arrow : Ty -> Ty -> arrow.
Hint Constructors arrow.

Inductive res : Type :=
| Err : res (* invalid argument/type error *)
| Bot : res (* non-termination *)
| Res : V -> res. (* a value result *)
Hint Constructors res.

Definition fn := (V -> res).


Ltac destruct_IsA :=
  match goal with
  | [H : IsA _ _ |- _] => destruct H
  end.

Ltac same_Res :=
  match goal with
  | [H1 : ?f ?v = Res ?x , H2 : ?f ?v = Res ?y |- _] =>
    rewrite H1 in H2; inversion H2; subst; clear H2
  end.


Inductive interface : Type :=
| IBase: arrow -> interface
| ICons : arrow -> interface -> interface.
Hint Constructors interface.

Fixpoint i_dom (i : interface) : Ty :=
  match i with
  | IBase (Arrow T1 _) => T1
  | ICons (Arrow T1 _) i' => tyOr T1 (i_dom i')
  end.
Hint Unfold i_dom.


Fixpoint a_result (a : arrow) (v : V) : option Ty :=
  match a with
  | Arrow T1 T2 => if IsA_dec v T1
                   then Some T2
                   else None
  end.
Hint Unfold a_result.

Definition FnA (f : fn) (a : arrow) : Prop :=
forall x T,
  a_result a x = Some T ->
  (f x = Bot \/ exists y, f x = Res y /\ IsA y T).
Hint Unfold FnA.

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
Definition FnI (f : fn) (i : interface) : Prop :=
  forall x T,
    i_result i x = Some T ->
    f x = Bot \/ (exists y, (f x = Res y /\ IsA y T)).
Hint Unfold FnI.

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

Definition a_neg (a : arrow) (outT : Ty) : Ty :=
  match a with
  | Arrow T1 T2 => if IsEmpty_dec (tyAnd T2 outT)
                   then T1
                   else emptyTy
  end.

Fixpoint i_neg (i : interface) (outT : Ty) : Ty :=
  match i with
  | IBase a => a_neg a outT
  | ICons (Arrow S1 S2) i' =>
    let T1 := a_neg (Arrow S1 S2) outT in
    let T2 := i_neg i' outT in
    let T3 := tyAnd S1 (i_neg i' (tyAnd S2 outT)) in
    tyOr T1 (tyOr T2 T3)
  end.

Fixpoint i_pos (i : interface) (outT : Ty) : Ty :=
  match i with
  | IBase (Arrow T1 T2) =>
    if IsEmpty_dec (tyAnd T2 outT)
    then emptyTy
    else T1
  | ICons (Arrow T1 T2) i' =>
    let T := if IsEmpty_dec (tyAnd T2 outT)
             then emptyTy
             else T1
    in tyOr T (i_pos i' outT)
  end.

Definition i_inv (i : interface) (outT : Ty) : Ty :=
  tyDiff (i_pos i outT) (i_neg i outT).

Lemma FnA_res_ty : forall T1 T2 f x y,
    IsA x T1 ->
    f x = Res y ->
    FnA f (Arrow T1 T2) ->
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
              HFnA : FnA ?f (Arrow ?T1 ?T2)
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy HFnA)
| [Hx : IsA ?x ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (IBase (Arrow ?T1 ?T2))
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
| [Hx : IsA ?x ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (ICons (Arrow ?T1 ?T2) _)
   |- IsA ?y ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
  end.

Lemma Subtype_trans : forall T1 T2 T3,
    Subtype T1 T2 ->
    Subtype T2 T3 ->
    Subtype T1 T3.
Proof.
  crush.
Qed.

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
          Hf : FnI ?f (IBase (Arrow ?T1 ?T2)),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (IsA y T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  | [H1 : IsA ?x ?T1,
          Hf : FnA ?f (Arrow ?T1 ?T2),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (IsA y T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  end.

Lemma in_i_pos : forall i v v' f T,
    FnI f i ->
    IsA v (i_dom i) ->
    f v = Res v' ->
    IsA v' T ->
    IsA v (i_pos i T).
Proof with auto.
  intros i.
  induction i as [[T1 T2] | [T1 T2] i' IH];
    intros v v' f T Hfi Hv Hfv Hv'.
  {
    apply_fun.
    simpl in *.
    destruct (IsEmpty_dec (tyAnd T2 T)) as [Hmt2 | Hnmt2]; crush.
    {
      assert False as impossible. applyH. exists v'; auto.
      contradiction.
    }
  }
  {
    assert (FnA f (Arrow T1 T2)) as Hfa by (eapply FnI_first; eauto).
    simpl in *.
    destruct Hv as [v Hv | v Hv].
    {
      destruct (IsEmpty_dec (tyAnd T2 T)) as [Hmt2 | Hnmt2].
      {
        assert False as impossible.
        apply_fun. apply Hmt2. exists v'; eauto.
        contradiction.        
      }
      {
        left; auto.
      }
    }
    {
      assert (FnI f i') as Hfi' by (eapply FnI_rest; eauto).
      right.
      eapply IH; eauto.
    }
  }
Qed.  

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
    assert (FnA f (Arrow T1 T2)) as Hfa by (eapply FnI_first; eauto).
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

(* Interface Inversion Soundness 
   i.e. the input type we predict is correct *)
Lemma i_inv_sound : forall i outT,
    forall (f:fn),
      FnI f i ->
      forall (v v':V),
        IsA v (i_dom i) ->
        f v = Res v' ->
        IsA v' outT ->
        IsA v (i_inv i outT).
Proof with crush.
  intros i outT f Hint v v' Hv Hf Hv'.
  unfold i_inv in *.
  constructor; auto.
  eapply in_i_pos; eauto.
  intros Hcontra.
  eapply in_i_neg; eauto.
Qed.

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


Lemma not_IsA_tyOr : forall x T1 T2,
    ~ IsA x (tyOr T1 T2) ->
    ~ IsA x T1 /\ ~ IsA x T2.
Proof. crush. Qed.

(* Interface Inversion Minimality
   i.e. the input type we predict is minimal *)
Lemma i_pos_dom : forall i T,
    Subtype (i_pos i T) (i_dom i).
Proof.
  intros i; induction i as [[T1 T2] | [T1 T2] i' IH];
    intros T x Hx.
  simpl in *. ifcaseH; crush.
  simpl in *.
  ifcaseH.
  right. inversion Hx; subst; eauto. eapply IH; eauto.
  inversion Hx; subst; eauto. right; eapply IH; eauto.
Qed.


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
Lemma i_inv_minimal : forall i outT x,
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
      exists f y...
    }
  }
  {
    assert (IsA x (i_neg i outT)) as impossible.
    {
      eapply i_result_None; eauto.
      eapply i_pos_dom; eauto.
    }
    contradiction.
  }
Qed.



