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

Open Scope list_scope.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                 Definitions                   *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Axiom V : Type.
Axiom V_eq_dec : forall (v1 v2: V), {v1 = v2} + {v1 <> v2}.
Notation Ty := (Ensemble V).
Definition IsEmpty (t:Ty) : Prop := ~ (Inhabited V t).
Axiom IsEmpty_dec : forall (t: Ty), {IsEmpty t} + {~ IsEmpty t}.
Notation IsA v T := (In V T v).
Axiom IsA_dec : forall (v:V) (t: Ty), {IsA v t} + {~ IsA v t}.
Notation "T1 <: T2" := (Included V T1 T2) (at level 70).

Definition emptyTy : Ty := Empty_set V.
Definition anyTy : Ty := Full_set V.
Definition tyOr : Ty -> Ty -> Ty := Union V.
Definition tyAnd : Ty -> Ty -> Ty := Intersection V.
Definition tyDiff : Ty -> Ty -> Ty := Setminus V.
Definition tyNot : Ty -> Ty := tyDiff anyTy.

Hint Unfold emptyTy.
Hint Unfold anyTy.
Hint Unfold tyOr.
Hint Unfold tyAnd.
Hint Unfold tyDiff.
Hint Unfold tyNot.

(* A single function arrow *)
Inductive arrow : Type :=
| Arrow : Ty -> Ty -> arrow.

Hint Constructors arrow.

Definition a_meet (a1 a2 : arrow) : arrow :=
  match a1, a2 with
  | Arrow d1 r1, Arrow d2 r2 => Arrow (tyAnd d1 d2) (tyAnd r1 r2)
  end.

Definition a_dom (a : arrow) : Ty :=
  match a with
  | Arrow t1 _ => t1
  end.

Definition a_rng (a : arrow) : Ty :=
  match a with
  | Arrow _ t2 => t2
  end.

Inductive res : Type :=
| Err : res (* invalid argument/type error *)
| Bot : res (* non-termination *)
| Res : V -> res. (* a value result *)

Hint Constructors res.

Definition fn := (V -> res).

Inductive FnArrow : fn -> arrow -> Prop :=
| FnA : forall T1 T2 f,
    (forall v,
        IsA v T1 ->
        (f v = Bot
         \/ (exists v', IsA v' T2 /\ f v = Res v'))) ->
    FnArrow f (Arrow T1 T2).

Hint Constructors FnArrow.

Inductive interface : Type :=
| IBase : arrow -> interface
| ICons : arrow -> interface -> interface.

Hint Constructors interface.

Fixpoint i_dom (i : interface) : Ty :=
  match i with
  | IBase a => a_dom a
  | ICons a i' => tyOr (a_dom a) (i_dom i')
  end.

Inductive FnInterface : fn -> interface -> Prop :=
| FnIBase : forall f a,
    FnArrow f a ->
    FnInterface f (IBase a)
| FnICons : forall f a i',
    FnArrow f a ->
    FnInterface f i' ->
    FnInterface f (ICons a i').

Hint Constructors FnInterface.


Fixpoint i_app (i1 i2 : interface) : interface :=
  match i1 with
  | IBase a => ICons a i2
  | ICons a i1' => ICons a (i_app i1' i2)
  end.

Fixpoint i_map (f : arrow -> arrow) (i : interface) : interface :=
  match i with
  | IBase a => IBase (f a)
  | ICons a i' => ICons (f a) (i_map f i')
  end.

(* non-empty subsets of an interface, as arrows with
   pointwise intersected domain and codomains *)
Fixpoint i_powerset (i : interface) : interface :=
  match i with
  | IBase a => IBase a
  | ICons a i' => let p := i_powerset i' in
                  i_app p (i_map (a_meet a) p)
  end.

Lemma i_app_i : forall i i' f,
    FnInterface f i ->
    FnInterface f i' ->
    FnInterface f (i_app i i').
Proof.
  intros i i' f Hi Hi'.
  induction Hi; crush.
Qed.

Ltac destruct_arrows :=
  match goal with
  | [a : arrow |- _] => destruct a
  end.

Ltac destruct_IsA :=
  match goal with
  | [H : IsA _ _ |- _] => destruct H
  end.


Lemma a_meet_arrow_fn : forall a a' f,
    FnArrow f a  ->
    FnArrow f a' ->
    FnArrow f (a_meet a a').
Proof with crush.
  intros a a' f Ha Ha'.
  repeat (match goal with
          | [H : FnArrow _ _ |- _] => destruct H
          end).
  constructor. intros.
  destruct_IsA.
  repeat applyHinH...
  right.
  match goal with
  | [H : _ _ = Res ?v |- _] => exists v; rewrite H in *
  end...
  constructor; auto.
Qed.

Hint Resolve a_meet_arrow_fn.

  
Lemma a_meet_i : forall i f a,
    FnInterface f i ->
    FnArrow f a ->
    FnInterface f (i_map (a_meet a) i).
Proof with crush.
  intros i f a Hfi Hfa.
  induction Hfi...
Qed.


Lemma i_powerset_interface : forall i f,
    FnInterface f i ->
    FnInterface f (i_powerset i).
Proof with crush.
  intros i f Hfi.
  induction i... 
  assert (FnInterface f (i_powerset i)) as Hp...
  inversion Hfi; crush.
  apply i_app_i...
  apply a_meet_i...
  inversion Hfi...
Qed.



Definition overlap (t1 t2:Ty) : bool :=
  if (IsEmpty_dec (tyAnd t1 t2)) then false else true.

Hint Unfold overlap.

Definition a_inv (a:arrow) (out:Ty) : Ty :=
  if overlap (a_rng a) out
  then (a_dom a)
  else emptyTy.

Hint Unfold a_inv.

Definition ArrowInv
           (a:arrow)
           (outT inT : Ty) : Prop :=
forall (f:fn),
  FnArrow f a ->
  forall (v v':V),
    IsA v (a_dom a) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.

Hint Unfold ArrowInv.

Lemma no_overlap_empty : forall t1 t2,
    false = overlap t1 t2 ->
    IsEmpty (tyAnd t1 t2).
Proof.
  intros.
  unfold overlap in *.
  destruct (IsEmpty_dec (tyAnd t1 t2)); crush.
Qed.

Ltac same_Res :=
  match goal with
  | [H1 : ?f ?v = Res ?x , H2 : ?f ?v = Res ?y |- _] =>
    rewrite H1 in H2; inversion H2; subst; clear H2
  end.

Ltac inv_FnArrow :=
  match goal with
  | [H : FnArrow _ _ |- _] => inversion H; subst
  end.


(* Arrow Inversion Soundness *)
Theorem a_inv_sound : forall a outT inT,
    a_inv a outT = inT ->
    ArrowInv a outT inT.
Proof with crush.
  unfold ArrowInv.
  intros.
  destruct a as [T1 T2].
  simpl in *.
  unfold a_inv in *.
  remember (overlap (a_rng (Arrow T1 T2)) outT) as Hoverlap.
  ifcaseH...
  inv_FnArrow.
  applyHinH...
  same_Res.
  forwards: no_overlap_empty. eauto.
  unfold IsEmpty in *.
  assert (Inhabited V (tyAnd T2 outT)).
  apply (Inhabited_intro _ _ x). unfold tyAnd... crush.
Qed.

Lemma no_empty_val : forall v,
    ~ IsA v emptyTy.
Proof.
  intros v Hmt. inversion Hmt.
Qed.
  
Lemma empty_no_overlap_l : forall T T',
    IsEmpty T -> overlap T T' = false.
Proof.
  intros T T' Hmt.
  unfold overlap.
  ifcase. auto.
  assert False.
  intuition.
  applyH.
  unfold IsEmpty in *.
  intros Hin.
  inversion Hin as [v Hv].
  inversion Hv; subst.
  apply Hmt. apply (Inhabited_intro V T v).
  auto.
  crush.
Qed.
  
Lemma not_empty_exists : forall T,
    ~ IsEmpty T ->
    exists v, IsA v T.
Proof.
  intros T HTmt.
  unfold IsEmpty in *.
  apply NNPP in HTmt.
  inversion HTmt.
  eexists. eauto.
Qed.
  
  
(* Arrow Inversion Completeness *)
Theorem a_inv_complete : forall a outT inT,
    a_inv a outT = inT ->
    forall inT',
      ArrowInv a outT inT' ->
      inT <: inT'.
Proof.
  intros a outT intT Hinveq inT' Hinv.
  destruct a as [T1 T2].
  unfold a_inv in *. simpl in *.
  unfold overlap in *.
  remember (IsEmpty_dec (tyAnd T2 outT)) as Hmt.
  destruct Hmt as [Hmt | Hnmt].
  (* IsEmpty (tyAnd T2 outT) *)
  {
    subst. unfold Included; intros.
    assert False. eapply no_empty_val. eassumption. crush.
  }
  (* ~ IsEmpty (tyAnd T2 outT) *)
  {
    assert (exists v, IsA v (tyAnd T2 outT)) as Hex.
    apply not_empty_exists. auto. destruct Hex as [v Hv].
    remember (fun (_:V) => Res v) as f.
    (* f is a function that maps all T1 to 
       some value in (T2 ∩ outT) 
      *)
    assert (FnArrow f (Arrow T1 T2)) as Hf.
    {
     constructor; intros.
     right. exists v. crush.
     inversion Hv. crush.
    }
    unfold Included. intros.
    unfold ArrowInv in *.
    apply (Hinv f Hf x v); crush.
    inversion Hv; crush.
  }
Qed.



Fixpoint i_inv_aux (p: interface) (out:Ty) : Ty :=
  match p with
  | IBase a => (a_inv a out)
  | ICons a p' => tyOr (a_inv a out) (i_inv_aux p' out)
  end.

Definition i_inv (i:interface) (out:Ty) : Ty :=
  let p := (i_powerset i) in
  let pos := i_inv_aux p out in
  let neg := i_inv_aux p (tyNot out) in
  tyDiff pos neg.



Definition InterfaceInv
           (i:interface)
           (outT inT : Ty) : Prop :=
forall (f:fn),
  FnInterface f i ->
  forall (v v':V),
    IsA v (i_dom i) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.


(* Interface Inversion Soundness *)
Theorem i_inv_sound : forall i outT inT,
      i_inv i outT = inT ->
      InterfaceInv i inT outT.
Proof.
  Admitted.
  

(* Interface Inversion Completeness *)
Theorem i_inv_complete : forall i outT inT,
    i_inv i outT = inT ->
    forall inT',
      InterfaceInv i outT inT' ->
      inT <: inT'.
Proof.
  Admitted.

    
(* A disjunction of interfaces *)
Inductive dnf : Type :=
| DBase : interface -> dnf
| DCons : interface -> dnf -> dnf.

Fixpoint d_dom (d : dnf) : Ty :=
  match d with
  | DBase i => i_dom i
  | DCons i d' => tyAnd (i_dom i) (d_dom d')
  end.

Inductive FnDnf : fn -> dnf -> Prop :=
| FnDBase : forall f i,
    FnInterface f i ->
    FnDnf f (DBase i)
| FnDCons : forall f i d,
    FnInterface f i -> 
    FnDnf f (DCons i d)
| FnDRest : forall f i d,
    FnDnf f d -> 
    FnDnf f (DCons i d).


Fixpoint d_inv (d:dnf) (out:Ty) : Ty :=
  match d with
  | DBase i => i_inv i out
  | DCons i d' => tyOr (i_inv i out) (d_inv d' out)
  end. 

Definition DnfInv
           (d:dnf)
           (outT inT : Ty) : Prop :=
forall (f:fn),
  FnDnf f d ->
  forall (v v':V),
    IsA v (d_dom d) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.


(* Dnf Inversion Soundness *)
Theorem d_inv_sound : forall d outT inT,
      d_inv d outT = inT ->
      DnfInv d outT inT.
Proof.
  Admitted.


(* Dnf Inversion Completeness *)
Theorem d_inv_complete : forall d outT inT,
    d_inv d outT = inT ->
    forall inT',
      DnfInv d outT inT' ->
      inT <: inT'.
Proof.
  Admitted.
