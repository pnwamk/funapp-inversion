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
Axiom V_eq_dec : forall (v1 v2: V), {v1 = v2} + {v1 <> v2}.
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
Notation Subtype T1 T2 := (Included V T1 T2).
Axiom Subtype_dec : forall T1 T2, {Subtype T1 T2} + {~ Subtype T1 T2}.
Notation IsA v T := (In V T v).
Axiom IsA_dec : forall (v:V) (t: Ty), {IsA v t} + {~ IsA v t}.

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
Proof.
  Admitted.

Lemma tyOr_empty_r : forall t,
    tyOr t emptyTy = t.
Proof.
  Admitted.

Lemma tyAnd_empty_l : forall t,
    tyAnd emptyTy t = emptyTy.
Proof.
  Admitted.

Lemma tyAnd_empty_r : forall t,
    tyAnd t emptyTy = emptyTy.
Proof.
  Admitted.

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


Fixpoint a_apply (a : arrow) (argT : Ty) : option Ty :=
  match a with
  | Arrow T1 T2 => if IsEmpty_dec (tyDiff argT T1)
                   then Some T2
                   else None
  end.
Hint Unfold a_apply.

Definition FnA (f : fn) (a : arrow) : Prop :=
  forall x T1 T2,
    IsA x T1 ->
    a_apply a T1 = Some T2 ->
  (f x = Bot \/ exists y, f x = Res y /\ IsA y T2).
Hint Unfold FnA.

Definition mTyAnd (oT1 oT2 : option Ty) : option Ty :=
  match oT1, oT2 with
  | None, _ => oT2
  | _, None => oT1
  | Some T1, Some T2  => Some (tyAnd T1 T2)
  end.

Fixpoint i_apply (i : interface) (argT : Ty) : option Ty :=
  match i with
  | IBase a => a_apply a argT
  | ICons (Arrow S1 S2) i' =>
    let T1 := a_apply (Arrow S1 S2) argT in
    let T2 := i_apply i' argT in
    let T3 := mTyAnd (Some S2) (i_apply i' (tyDiff argT S1)) in
    mTyAnd T1 (mTyAnd T2 T3)
  end.  

(* Function Interface *)
Definition FnI (f : fn) (i : interface) : Prop :=
  forall x T1 T2,
    IsA x T1 ->
    i_apply i T1 = Some T2 ->
    (f x = Bot \/ exists y, f x = Res y /\ IsA y T2).
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
  | ICons a i' =>
    let T1 := a_neg a outT in
    let T2 := i_neg i' outT in
    let T3 := tyAnd T1 (i_neg i' (tyAnd T2 outT)) in
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
          destruct Hnmt' as [y Hy1 Hy2].
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
      }
    }                  
    {
      destruct Hx as [x Hx | x Hx]...
      destruct Hx as [x Hx | x Hx]...
      right. left. eapply IH; eauto.
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
  intros i. induction i as [[T1 T2] | [T1 T2] i' IH]; crush.
  (* IBase (Arrow T1 T2) *)
  {
    ifcaseH; crush.
    applyH.
    match goal with
    | [H : ?f ?v = Res ?v' |- _] => exists v'
    end.
    apply_fun...
  }
  (* ICons (Arrow T1 T2) i' *)
  {
    forwards: FnI_first; eauto.
    forwards: FnI_rest; eauto.
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
      rewrite tyAnd_empty_l in *.
      rewrite tyOr_empty_l in *.
      rewrite tyOr_empty_r in *.
      eapply IH; eauto.
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
Proof. Admitted.
Lemma not_IsA_tyAnd : forall x T1 T2,
    ~ IsA x (tyAnd T1 T2) ->
    ~ IsA x T1 \/ ~ IsA x T2.
Proof. Admitted.

Lemma i_neg_empty : forall i,
    i_neg i emptyTy = i_dom i.
Proof.
Admitted.

Lemma i_pos_empty : forall i,
    i_pos i emptyTy = emptyTy.
Proof.
Admitted.


Lemma i_inv_empty : forall i,
    i_inv i emptyTy = emptyTy.
Proof.
Admitted.

Hint Rewrite i_neg_empty i_pos_empty i_inv_empty.

(* Interface Inversion Minimality
   i.e. the input type we predict is minimal *)
Lemma i_pos_dom : forall i T,
    Subtype (i_pos i T) (i_dom i).
Proof.
Admitted.

Lemma must_be : forall i x T T',
    i_result i x = Some T ->
    IsInhabited T' ->
    IsEmpty (tyAnd T T') ->
    IsA x (i_neg i T').
Proof with auto.
  intros i; induction i as [[T1 T2] | [T1 T2] i' IH];
    intros x T T' Hres Hnmt Hmt.
  (* (IBase (Arrow T1 T2) *)
  {
    simpl in *.
    destruct (IsA_dec x T1) as [HxIs | HxNot]; crush.
    destruct (IsEmpty_dec (tyAnd T T')) as [Hmt' | Hnmt']...
    contradiction.
  }
  (* (ICons (Arrow T1 T2) i') *)  
  {
    simpl in *.
    destruct (IsA_dec x T1) as [HxIs | HxNot]...
    destruct (IsEmpty_dec (tyAnd T2 T')) as [Hmt' | Hnmt']...
    {
      right.
      remember (i_result i' x) as xres.
      destruct xres as [Tx |]; inversion Hres; crush.
      clear Hres.
      eapply IH; eauto.
      intro H'. apply Hmt.
    }
    {
      
    }
  }
  
(* Interface Inversion Minimality
   i.e. the input type we predict is minimal *)
Lemma i_inv_minimal : forall i outT x,
    IsA x (i_pos i outT) ->
    ~ IsA x (i_neg i outT) ->
    exists f y, FnI f i /\ f x = Res y /\ IsA y outT.
Proof with auto.
  intros i.
  induction i as [[T1 T2] | [T1 T2] i' IH];
    intros outT x HxIn HxNot.
  (* (IBase (Arrow T1 T2)) *)
  {    
    simpl in *.
    ifcaseH...
    destruct (exists_target_fn (IBase (Arrow T1 T2)) outT)
      as [f [Hfi Hmaps]].
    assert (exists y : V, f x = Res y /\ IsA y (tyAnd T2 outT))
      as [y [Hy1 Hy2]] by (apply Hmaps; crush; ifcase; crush).
    eauto.
  }
  (* (ICons (Arrow T1 T2) i') *)
  {
    simpl in *.
    apply not_IsA_tyOr in HxNot. destruct HxNot as [HxNot1 HxNot2].
    apply not_IsA_tyOr in HxNot2. destruct HxNot2 as [HxNot2 HxNot3].
    apply not_IsA_tyAnd in HxNot3.
    destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt2o | Hnmt2o].
    (* IsEmpty (tyAnd T2 outT), ∴ ~ IsA x T1 *)
    {
      clear HxNot3.
      rewrite tyOr_empty_l in *.
      destruct (IH outT x HxIn HxNot2) as [f [y [Hf [Hfx Hy]]]].
      remember (fun (v:V) =>
                  if (IsA_dec v T1)
                  then Bot
                  else (f v))
        as f'.      
      assert (FnA f' (Arrow T1 T2)) as Hfa.
      {
        unfold FnA.
        intros v T Hares.
        simpl in *.
        subst.
        destruct (IsA_dec v T1); inversion Hares; subst.
        left; reflexivity.
      }
      assert (FnI f' i') as Hfi'.
      {
        unfold FnI.
        intros v T Hres.
        subst.
        destruct (IsA_dec v T1).
        left; reflexivity.
        specialize (Hf v T Hres).
        assumption.
      }
      assert (FnI f' (ICons (Arrow T1 T2) i')) as Hfai by
          (eapply FnI_cons; eauto).
      exists f' y; split... split...  subst.
      destruct (IsA_dec x T1); try solve[contradiction]; auto.
    }
    {
      clear HxNot1. clear HxNot3.
      assert (.
      destruct HxIn as [x HxIn | x HxIn].
      {
        destruct Hnmt2o as [y Hy].
        remember (fun (v:V) =>
                    if (V_eq_dec v x)
                    then Res y
                    else Bot)
          as f'.
        exists f' y. split; try split.
        unfold FnI.
        intros v T Hres.
        subst. simpl in *.
        destruct (V_eq_dec v x) as [Heq | Hneq]. subst; simple.
        destruct (IsA_dec x T1)...
        remember (i_result i' x) as xres.
        destruct xres. inversion Hres; subst.
        right. exists y; split...
        split; try solve[simpl crush | ifcase; crush]. split.

      }
      {
        
      }
      destruct (IsA_dec x (i_pos i' outT)) as [HxIn' | HxNot'].
      {
        
      }
      {

      }
      unfold FnI. simpl in *.
      destruct (IsA_dec x (i_pos i' (tyAnd T2 outT))) as [HxPos | HxPos].
      {
        destruct (IsA_dec x (i_neg i' (tyAnd T2 outT))) as [HxNeg | HxNeg].
        {
          

          (*
            Lemma i_neg_sub : forall i T1 T2,
            Subtype T2 T1 ->
            Subtype (i_neg i T1) (i_neg i T2).
           *)
          
        }
        {

        }
      }
      {
        
      }
       ~ IsA x (i_neg i' outT) ->
      
      destruct (IsA_dec x (i_pos i' outT)) as [HxIn' | HxNot'].
      {
        destruct (IH outT x HxIn' HxNot2) as [f [y [Hf [Hfx Hy]]]].
        remember (fun (v:V) =>
                    if (IsA_dec v T1)
                    then Bot
                    else (f v))
          as f'.      
      }
      {
        
      }

      
      destruct (IsA_dec x T1) as [HxIn1 | HxNot1].
      {
        clear HxIn.
        remember (i_result i' x) as optT'.        
        destruct optT' as [T' |].
        {
          destruct (IsEmpty_dec (tyAnd (tyAnd T2 T') outT)) as [Hmt | Hnmt].
          {
            
              }
                  {
                    
                  }
                }
                {
                }
                
                
              }
          }
          {
            
          }
          unfold FnI in Hf.
        }
        {
          
        }
      }
      {
        
      }

        
      destruct (IsA_dec x T1) as [HxIn1 | HxNot1].
      {
        clear HxIn.
        clear HxIn1'.
        
        {
          
        }
        {
          
        }
        simpl in *.
      }
      {
        
      }
      (* BOOKMARK *)
    }

  }
Qed.
      


