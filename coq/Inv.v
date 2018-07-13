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
Notation "T1 <: T2" := (Included V T1 T2) (at level 70).

Hint Unfold Included Setminus.
Hint Constructors Union Intersection Inhabited.


Lemma no_empty_val : forall v,
    ~ IsA v emptyTy.
Proof.
  intros v Hmt. inversion Hmt.
Qed.



(* A single function arrow *)
Inductive arrow : Type :=
| Arrow : Ty -> Ty -> arrow.
Hint Constructors arrow.

Definition a_meet (a1 a2 : arrow) : arrow :=
  match a1, a2 with
  | Arrow d1 r1, Arrow d2 r2 => Arrow (tyAnd d1 d2) (tyAnd r1 r2)
  end.
Hint Unfold a_meet.

Definition a_dom (a : arrow) : Ty :=
  match a with
  | Arrow t1 _ => t1
  end.
Hint Unfold a_dom.

Definition a_rng (a : arrow) : Ty :=
  match a with
  | Arrow _ t2 => t2
  end.
Hint Unfold a_rng.


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


Ltac destruct_IsA :=
  match goal with
  | [H : IsA _ _ |- _] => destruct H
  end.

Definition a_inv_pos (a:arrow) (out:Ty) : Ty :=
  if (IsEmpty_dec (tyAnd (a_rng a) out))
  then emptyTy
  else (a_dom a).

Definition a_inv_neg (a:arrow) (out:Ty) : Ty :=
  if (IsEmpty_dec (tyAnd (a_rng a) out))
  then (a_dom a)
  else emptyTy.

Hint Unfold a_inv_pos a_inv_neg.

Definition ArrowInvPos 
           (a:arrow)
           (outT inT : Ty) : Prop :=
forall (f:fn),
  FnArrow f a ->
  forall (v v':V),
    IsA v (a_dom a) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.

Definition ArrowInvNeg 
           (a:arrow)
           (outT inT : Ty) : Prop :=
forall (f:fn),
  FnArrow f a ->
  forall (v v':V),
    f v = Res v' ->
    ~ (IsA v' outT /\ IsA v inT).

Hint Unfold ArrowInvPos ArrowInvNeg.

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
Lemma a_inv_pos_sound : forall a outT inT,
    a_inv_pos a outT = inT ->
    ArrowInvPos a outT inT.
Proof with crush.
  unfold ArrowInvPos.
  intros [T1 T2] outT inT Hinv f Hf v v' Hin Hfv Hout.
  unfold a_inv_pos in *. simpl in *. 
  destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt | Hnmt]...
  inv_FnArrow.
  applyHinH...
  same_Res.
  assert (Inhabited V (tyAnd T2 outT)) as impossible...
  exists x...
Qed.

Lemma a_inv_neg_sound : forall a outT inT,
    a_inv_neg a outT = inT ->
    ArrowInvNeg a outT inT.
Proof with crush.
  unfold ArrowInvNeg.
  intros [T1 T2] outT inT Hinv f Hf v v' Hfv.
  unfold a_inv_neg in *. simpl in *. 
  destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt | Hnmt]...
  (* ~ IsInhabited (tyAnd T2 outT) *)
  {
    apply Hmt. exists v'. split; crush.
    inv_FnArrow.
    applyHinH...
  }
  (* IsInhabited (tyAnd T2 outT) *)
  {
    eapply no_empty_val; eauto.
  }
Qed.
  
  
(* Arrow Inversion Completeness *)
Theorem a_inv_pos_complete : forall a outT inT,
    a_inv_pos a outT = inT ->
    forall inT',
      ArrowInvPos a outT inT' ->
      inT <: inT'.
Proof.
  intros [T1 T2] outT inT Hinveq inT' Hinv.
  unfold a_inv_pos in *. simpl in *.
  destruct (IsEmpty_dec (tyAnd T2 outT)); subst; crush.
  assert (exists v, IsA v (tyAnd T2 outT)) as Hex.
  {
    match goal with
    | [H : IsInhabited _ |- _] => inversion i
    end.
    match goal with
    | [H : IsA ?x (tyAnd T2 outT) |- _] => exists x; crush
    end.
  }
  destruct Hex as [v Hv].
  remember (fun (_:V) => Res v) as f.
  (* f is a function that maps all T1 to 
     som e value in (T2 ∩ outT) 
   *)
  assert (FnArrow f (Arrow inT T2)) as Hf.
  {
    constructor; intros.
    right. exists v. crush.
    inversion Hv. crush.
  }
  unfold Included. intros.
  unfold ArrowInvPos in *.
  apply (Hinv f Hf x v); crush.
  inversion Hv; crush.
Qed.

Theorem a_inv_neg_complete : forall a outT inT,
    a_inv_neg a outT = inT ->
    forall inT',
      ArrowInvNeg a outT inT'  ->
      inT' <: inT.
Proof.
  intros [T1 T2] outT inT Hinv inT' H' x Hx.
  unfold a_inv_neg in Hinv. simpl in *.
  unfold ArrowInvNeg in *.
  (* BOOKMARK STUCK *)

  destruct (IsEmpty_dec (tyAnd T2 outT)) as [Hmt | Hnmt]; subst.
  {
    destruct (IsEmpty_dec outT) as [Homt | Honmt]; subst.
    
  }
  
  destruct (IsA_dec x inT); auto.
  assert False.
  {
    
  }
  {
    eapply H'.
    (* we need a v in inT' s.t. (x)
       f v = Res v' and
       v' in outT  *)
    unfold a_inv_neg in Hinv.
    simpl in *.
    destruct (IsEmpty_dec (tyAnd T2 outT)); subst.
    simpl in *.
  } 
  ; crush.  
  {
    destruct (IsEmpty_dec outT).
    {
      (* if outT is empty...  *)
    }
    (* we need an f s.t. 
       f : inT -> T2 *)
    destruct (IsA_dec x inT); auto.
    remember (fun (_:V) => Res x) as f.
    

    (* BOOKMARK *)
    destruct (IsEmpty_dec T2); crush.
    remember (fun (_:V) => Res x) as f.
    assert (FnArrow f (Arrow inT T2)) as Hf.
    {
      constructor. intros v Hv.
      crush.
    }
  }
  {

  }
  
Inductive interface : Type :=
| IBase : arrow -> interface
| ICons : arrow -> interface -> interface.
Hint Constructors interface.

Fixpoint i_dom (i : interface) : Ty :=
  match i with
  | IBase a => a_dom a
  | ICons a i' => tyOr (a_dom a) (i_dom i')
  end.
Hint Unfold i_dom.

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


Fixpoint i_inv_pos (p: interface) (out:Ty) : Ty :=
  match p with
  | IBase a => (a_inv_pos a out)
  | ICons a p' => tyOr (a_inv_pos a out) (i_inv_pos p' out)
  end.

Fixpoint i_inv_neg (p: interface) (out:Ty) : Ty :=
  match p with
  | IBase a => (a_inv_neg a out)
  | ICons a p' => tyOr (a_inv_neg a out) (i_inv_neg p' out)
  end.
Definition i_inv (i:interface) (out:Ty) : Ty :=
  let p := (i_powerset i) in
  let pos := i_inv_pos p out in
  let neg := i_inv_neg p (tyNot out) in
  tyDiff pos neg.
Hint Unfold i_inv i_inv_aux i_app i_map i_powerset.


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

Ltac inv_FnInterface :=
  match goal with
  | [H : FnInterface _ _ |- _] => inversion H; subst
  end.

Lemma in_tyDiff : forall v T1 T2,
    IsA v T1 ->
    ~ IsA v T2 ->
    IsA v (tyDiff T1 T2).
Proof.
  crush.
Qed.


(* Interface Inversion Soundness *)
Lemma i_inv_sound : forall i outT inT,
      i_inv i outT = inT ->
      InterfaceInv i outT inT.
Proof with crush.
  intros i; induction i.
  (* i =  (IBase a) *)
  {
    intros outT inT Hinv f Hint v v' Hv Hf Hv'.
    destruct a as [T1 T2].
    inv_FnInterface...
    inv_FnArrow.
    assert (IsA v T1) as temp; auto.
    applyIn temp...
    same_Res.
    unfold i_inv. unfold i_powerset. unfold i_inv_aux.
    apply in_tyDiff.
    (* Goal:  IsA v (a_inv (Arrow T1 T2) outT) *)
    {
      eapply a_inv_sound; eauto.
    }
    (* Goal: ~ IsA v (a_inv (Arrow T1 T2) (tyNot outT)) *)
    {
      unfold a_inv in *. simpl in *.
      intro Hv''.
      destruct (IsEmpty_dec (tyAnd T2 (tyNot outT))).
      {
        eapply no_empty_val. eassumption.
      }
      {
        assert ().
        match goal with
        | [H : IsInhabited _ |- _] => inversion H
        end.
        inv_FnArrow.
        assert (f v = Bot \/ (exists v' : V, IsA v' T2 /\ f v = Res v'))
          as Habsurd. auto.
        inversion Habsurd; subst. crush.
        match goal with
        | [H : IsInhabited _ |- _] => inversion H
        end.
        
      }
      eapply a_inv_sound in H1; eauto.
      eapply H1 in Hv'.
    }
    
    unfold Setminus.
    unfold a_inv. simpl in *.
    ifcase. crush.
    ifcase.
    cbv.
    intros.
    
    crush.
    
     (@a_inv_sound (Arrow T1 T2) outT).
    simpl in *.
  }
  (* i =  (ICons a i') *)
  {
  }
  intros i outT inT Hinv f Hint v v' Hv Hf Hv'...
  inv_FnInterface...
  (* FnInterface f (IBase a) *)
  {
    
  }
  (* FnInterface f (ICons a) *)
  {

  }
  Admitted.
  

(* Interface Inversion Completeness *)
Lemma i_inv_complete : forall i outT inT,
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
