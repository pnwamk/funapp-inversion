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

Definition ameet (a1 a2 : arrow) : arrow :=
  match a1, a2 with
  | Arrow d1 r1, Arrow d2 r2 => Arrow (tyAnd d1 d2) (tyAnd r1 r2)
  end.

Definition dom (a : arrow) : Ty :=
  match a with
  | Arrow t1 _ => t1
  end.

Definition rng (a : arrow) : Ty :=
  match a with
  | Arrow _ t2 => t2
  end.

Inductive res : Type :=
| Err : res (* invalid argument/type error *)
| Bot : res (* non-termination *)
| Res : V -> res. (* a value result *)

Definition fn := (V -> res).

Definition FnArrow (a : arrow) (f : fn) : Prop :=
  match a with
  | Arrow T1 T2 =>
    forall v,
      (IsA v T1) ->
      (f v = Bot \/ exists v', IsA v' T2 /\ f v = Res v')
  end.


Inductive interface : Type :=
| IBase : arrow -> interface
| ICons : arrow -> interface -> interface.


Fixpoint idom (i : interface) : Ty :=
  match i with
  | IBase a => dom a
  | ICons a i' => tyOr (dom a) (idom i')
  end.


Fixpoint FnInterface (i : interface) (f : fn) : Prop :=
  match i with
  | IBase a  => FnArrow a f
  | ICons a i' => (FnArrow a f) /\ (FnInterface i' f)
  end.


Definition InterfaceInput
           (i:interface)
           (inT outT : Ty) : Prop :=
forall (f:fn),
  FnInterface i f ->
  forall (v v':V),
    IsA v (idom i) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.

Fixpoint iapp (i1 i2 : interface) : interface :=
  match i1 with
  | IBase a => ICons a i2
  | ICons a i1' => ICons a (iapp i1' i2)
  end.

Fixpoint imap (f : arrow -> arrow) (i : interface) : interface :=
  match i with
  | IBase a => IBase (f a)
  | ICons a i' => ICons (f a) (imap f i')
  end.

(* non-empty subsets of an interface, as arrows with
   pointwise intersected domain and codomains *)
Fixpoint ipowerset (i : interface) : interface :=
  match i with
  | IBase a => IBase a
  | ICons a i' => let p := ipowerset i' in
                  iapp p (imap (ameet a) p)
  end.

Lemma interface_app : forall i i' f,
    FnInterface i f ->
    FnInterface i' f ->
    FnInterface (iapp i i') f.
Proof.
  intro i.
  induction i; crush.
Qed.


Lemma ameet_arrow_fn : forall a a' f,
    FnArrow a f ->
    FnArrow a' f ->
    FnArrow (ameet a a') f.
Proof.
  intros a a' f. intros.
  destruct a as [d r]. destruct a' as [d' r'].
  simpl. intros.
  match goal with
  | [H : IsA _ _ |- _] => inversion H
  end.
  repeat
    (match goal with
     | [H1 : FnArrow _ _ , H2 : IsA _ _ |- _] => apply H1 in H2
     end).
  crush.
  right.
  match goal with
  | [H : _ _ = Res ?v |- _] => exists v; rewrite H in *
  end.
  crush.
  constructor; auto.
Qed.
  
Lemma ameet_preserves_interface : forall i f a,
    FnInterface i f ->
    FnArrow a f ->
    FnInterface (imap (ameet a) i) f.
Proof.
  intro i.
  induction i as [a' | a' i']; intros.
  simpl.
  apply ameet_arrow_fn; crush.
  simpl. split.
  apply ameet_arrow_fn; crush.
  crush.
Qed.  

Lemma ipowerset_preserves_interface : forall i i' f,
    FnInterface i f ->
    ipowerset i = i' ->
    FnInterface i' f.
Proof with crush.
  intro i.
  induction i...
  assert (FnInterface (ipowerset i) f) as Hp...
  apply interface_app...
  apply ameet_preserves_interface...
Qed.
    
    
    
    
(* A disjunction of interfaces *)
Inductive dnf : Type :=
| DBase : interface -> dnf
| DCons : interface -> dnf -> dnf.

Fixpoint ddom (d : dnf) : Ty :=
  match d with
  | DBase i => idom i
  | DCons i d' => tyAnd (idom i) (ddom d')
  end.

Fixpoint DnfFn (d : dnf) (f : fn) : Prop :=
  match d with
  | DBase i  => InterfaceFn i f
  | DCons i d' => (InterfaceFn i f) \/ (DnfFn d' f)
  end.


Definition DnfInput
           (d:dnf)
           (inT outT : Ty) : Prop :=
forall (f:fn),
  DnfFn d f ->
  forall (v v':V),
    IsA v (ddom d) ->
    f v = Res v' ->
    IsA v' outT ->
    IsA v inT.


Definition overlap (t1 t2:Ty) : bool :=
  boolean (IsEmpty_dec (tyAnd t1 t2)).
                 

Definition ainput (a:arrow) (out:Ty) : Ty :=
  if overlap (rng a) out
  then (dom a)
  else emptyTy.

Fixpoint iinput_aux (p: interface) (out:Ty) : Ty :=
  match p with
  | IBase a => (ainput a out)
  | ICons a p' => tyOr (ainput a out) (iinput_aux p' out)
  end.

Definition iinput (i:interface) (out:Ty) : Ty :=
  iinput_aux (ipowerset i) out.

(* TODO actual definition *)
Fixpoint dinput (d:dnf) (out:Ty) : Ty :=
  match d with
  | DBase i => iinput i out
  | DCons i d' => tyOr (iinput i out) (dinput d' out)
  end. 


Theorem InputSound : forall d f outT inT,
    DnfFn d f ->
    dinput d outT = inT ->
    DnfInput d inT outT.
Proof.
  Admitted.


Theorem InputComplete : forall d f outT inT inT',
    DnfFn d f ->
    dinput d outT = inT ->
    DnfInput d inT' outT ->
    Subtype inT inT'.
Proof.
  Admitted.
