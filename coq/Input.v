Require Import Coq.ZArith.BinInt.
Require Import ListSet.
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


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                 Definitions                   *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Axiom V : Type.
Definition Ty := Ensemble V.
Definition IsA v T := In V T v.
Definition Subtype T1 T2 := Included V T1 T2.

(* A single function arrow *)
Inductive arrow : Type :=
| Arrow : Ty -> Ty -> arrow.

(* Since an empty intersection/disjunction of arrows *)
(* has an empty domain we can omit it WLOG so our *)
(* proofs can focus on the interesting cases. *)

(* An intersection of arrows (i.e. a clause in the DNF rep)*)
Inductive clause : Type :=
| CBase : arrow -> clause
| CCons : arrow -> clause -> clause.

(* A disjunction of intersection of arrows *)
Inductive dnf : Type :=
| DBase : clause -> dnf
| DCons : clause -> dnf -> dnf.

Inductive res : Type :=
| Err : res (* invalid argument/type error *)
| Bot : res (* non-termination *)
| Res : V -> res. (* A value result *)


Inductive  TypedArrow : (V -> res) -> arrow -> Prop :=
| TyArrow : forall (T1 T2 : Ty) (f:(V -> res)),
    (forall v, (~ IsA v T1) -> f v = Err) ->
    (forall v,
        (IsA v T1) ->
        (f v = Bot \/ exists v', IsA v' T2 /\ f v = Res v')) ->
    TypedArrow f (Arrow T1 T2).


Inductive TypedClause : (V -> res) -> clause -> Prop :=
| TyCBase : forall (f:(V -> res)) a,
    TypedArrow f a ->
    TypedClause f (CBase a)
| TyCCons : forall (f:(V -> res)) a c,
    TypedArrow f a ->
    TypedClause f c ->
    TypedClause f (CCons a c).

Inductive TypedDNF : (V -> res) -> dnf -> Prop :=
| TyDBase : forall (f:(V -> res)) c,
    TypedClause f c ->
    TypedDNF f (DBase c)
| TyDHead : forall (f:(V -> res)) c d,
    TypedClause f c ->
    TypedDNF f (DCons c d)
| TyDTail : forall (f:(V -> res)) c d,
    TypedDNF f d ->
    TypedDNF f (DCons c d).

Inductive InputType : (V -> res) -> Ty -> Ty -> Prop :=
| InTy :  forall (f:(V -> res)) inT outT,
    (forall v v',
        (f v = Res v' /\ IsA v' outT) ->
        IsA v inT) ->
    InputType f outT inT.

(* TODO actual definition *)
Fixpoint calcIn (f : (V -> res)) (fty:dnf) (t:Ty) : Ty := t. 


Theorem calcInSound : forall f t outT inT,
    TypedDNF f t ->
    calcIn f t outT = inT ->
    InputType f outT inT.
Proof.
  Admitted.


Theorem calcInComplete : forall f t outT inT inT',
    TypedDNF f t ->
    calcIn f t outT = inT ->
    InputType f outT inT' ->
    Subtype inT inT'.
Proof.
  Admitted.
