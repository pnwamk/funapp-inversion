Require Import Coq.ZArith.BinInt.
Require Import List.
Require Import Omega.
Require Import Ensembles.
Require Import Classical_sets.
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
Definition IsEmpty : Ty -> Prop := Inhabited V.
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

(* A single function arrow *)
Inductive arrow : Type :=
| Arrow : Ty -> Ty -> arrow.

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

Definition fn := (V -> res).

Definition FnArrow (f : fn) (a : arrow) : Prop :=
  match a with
  | Arrow T1 T2 =>
    forall v,
      (IsA v T1) ->
      (f v = Bot \/ exists v', IsA v' T2 /\ f v = Res v')
  end.

Hint Unfold FnArrow.

Inductive interface : Type :=
| IBase : arrow -> interface
| ICons : arrow -> interface -> interface.


Fixpoint i_dom (i : interface) : Ty :=
  match i with
  | IBase a => a_dom a
  | ICons a i' => tyOr (a_dom a) (i_dom i')
  end.


Fixpoint FnInterface (f : fn) (i : interface) : Prop :=
  match i with
  | IBase a  => FnArrow f a
  | ICons a i' => (FnArrow f a) /\ (FnInterface f i')
  end.

Hint Unfold FnInterface.


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
  intro i.
  induction i; crush.
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
  repeat destruct_arrows...
  destruct_IsA.
  repeat applyHinH...
  right.
  match goal with
  | [H : _ _ = Res ?v |- _] => exists v; rewrite H in *
  end...
  constructor; auto.
Qed.
  
Lemma a_meet_i : forall i f a,
    FnInterface f i ->
    FnArrow f a ->
    FnInterface f (i_map (a_meet a) i).
Proof with crush.
  intro i.
  induction i as [a' | a' i']; intros; simpl; crush;
  apply a_meet_arrow_fn...
Qed.  

Lemma i_powerset_interface : forall i i' f,
    FnInterface f i ->
    i_powerset i = i' ->
    FnInterface f i'.
Proof with crush.
  intro i.
  induction i...
  assert (FnInterface f (i_powerset i)) as Hp...
  apply i_app_i...
  apply a_meet_i...
Qed.
    
    
(* A disjunction of interfaces *)
Inductive dnf : Type :=
| DBase : interface -> dnf
| DCons : interface -> dnf -> dnf.

Fixpoint d_dom (d : dnf) : Ty :=
  match d with
  | DBase i => i_dom i
  | DCons i d' => tyAnd (i_dom i) (d_dom d')
  end.

Fixpoint FnDnf (f : fn) (d : dnf) : Prop :=
  match d with
  | DBase i  => FnInterface f i
  | DCons i d' => (FnInterface f i) \/ (FnDnf f d')
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


Definition overlap (t1 t2:Ty) : bool :=
  boolean (IsEmpty_dec (tyAnd t1 t2)).
                 

Definition a_inv (a:arrow) (out:Ty) : Ty :=
  if overlap (a_rng a) out
  then (a_dom a)
  else emptyTy.

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

Fixpoint d_inv (d:dnf) (out:Ty) : Ty :=
  match d with
  | DBase i => i_inv i out
  | DCons i d' => tyOr (i_inv i out) (d_inv d' out)
  end. 


Theorem InvSound : forall d f,
    FnDnf f d ->
    forall outT inT,
      d_inv d outT = inT ->
      DnfInv d inT outT.
Proof.
  Admitted.


Theorem InvComplete : forall d f outT inT,
    FnDnf f d ->
    d_inv d outT = inT ->
    forall inT',
      DnfInv d inT' outT ->
      inT <: inT'.
Proof.
  Admitted.
