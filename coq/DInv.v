Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Classical_sets.
Require Import Coq.Sets.Image.
Require Import CpdtTactics.
Require Import Inv.

Set Implicit Arguments.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           DNF Function Definitions            *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


(* A `dnf` is a union of interfaces, at least one of which
  describes a function (i.e. an DNF with 1 or more
  clauses). *)
Inductive dnf : Type :=
| DBase : interface -> dnf
| DCons : interface -> dnf -> dnf.
Hint Constructors dnf.

(* The domain for a dnf is the intersection of each
   individual interface's domain. *)
Fixpoint d_dom (d : dnf) : Ty :=
  match d with
  | DBase i => (i_dom i)
  | DCons i d' => tyAnd (i_dom i) (d_dom d')
  end.
Hint Unfold d_dom.

(* Disjunction of Function Arrows *)
(* I.e., what it means for a function `f` to conform to the
   description given by arrow `a`. *)
Fixpoint FnD (f : fn) (d : dnf) : Prop :=
  match d with
  | DBase i => FnI f i
  | DCons i d' => FnI f i \/ FnD f d'
  end.
Hint Unfold FnD.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                  DNF Lemmas                   *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma FnD_base : forall f i,
    FnD f (DBase i) ->
    FnI f i.
Proof.
  intros f i H.
  crush.
Qed.

Lemma FnD_Cons_i : forall i d f,
    FnI f i ->
    FnD f (DCons i d).
Proof. crush. Qed.

Lemma FnD_Cons_d : forall i d f,
    FnD f d ->
    FnD f (DCons i d).
Proof. crush. Qed.



(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           DNF Inversion Definitions           *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Fixpoint d_inv_aux (d : dnf) (outT : Ty) : Ty :=
  match d with
  | DBase i => i_inv i outT
  | DCons i d' => tyOr (i_inv i outT) (d_inv_aux d' outT)
  end.

(* Calculates the result type of calling a function which
   has the interface type `i` on value `v`. *)
Definition d_inv (d : dnf) (outT : Ty) : Ty :=
 tyAnd (d_dom d) (d_inv_aux d outT).
Hint Unfold d_inv d_inv_aux.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*          DNF Inversion Definition             *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Definition InvD (d : dnf) (outT inT: Ty) : Prop :=
  forall (f:fn),
    FnD f d ->
    forall (v v':V),
      IsA v (d_dom d) ->
      f v = Res v' ->
      IsA v' outT ->
      IsA v inT.
Hint Unfold InvD.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                 Soundness                     *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* Interface Inversion Soundness 
   i.e. the input type we predict is correct *)
Theorem d_inv_sound : forall d outT,
    InvD d outT (d_inv d outT).
Proof with auto.
  intros d.
  induction d as [i | i d' IH].
  {
    unfold InvD.
    intros outT f Hfd v v' Hv Hf Hv'. simpl in *.
    split...
    eapply i_inv_sound; eauto.
  }
  {
    unfold InvD.
    intros outT f Hfd v v' Hv Hfv Hv'.
    simpl in *.
    destruct Hfd as [Hfi | Hfd].
    {
      split...
      left; eapply i_inv_sound; eauto.
    }
    {
      split...
      assert (IsA v (d_inv d' outT)) by (eapply IH; eauto).      
      right... unfold d_inv in *...
    }      
  }
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                   Minimality                  *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma InvD_implies_InvI : forall i d outT inT,
    InvD (DCons i d) outT inT ->
    Inv i outT inT.
Proof.
(* BOOKMARK
   This is not true, since InvD is reasoning about a
   potentially smaller set of inputs as Inv =\ Not
   sure how to fix at the moment. *)
Admitted.  
  
Lemma InvD_implies_InvD : forall i d outT inT,
    InvD (DCons i d) outT inT ->
    InvD d outT inT.
Proof.
(* BOOKMARK
   Also not true for basically the same reason =\ *)
Admitted.

Theorem d_inv_minimal : forall d outT inT,
    InvD d outT inT ->
    Subtype (d_inv d outT) inT.
Proof with auto.
  intros d. induction d as [i | i d' IH].
  {
    intros outT inT Hinv x Hx.
    unfold InvD in Hinv. unfold d_inv in Hx.
    simpl in *.
    assert (Inv i outT inT) as Hinv' by eauto.
    eapply i_inv_minimal; eauto.
  }
  {
    intros outT inT Hinv x Hx. unfold d_inv in *.  simpl in *.
    destruct Hx as [x Hx1 Hx3].
    destruct Hx1 as [x Hx1 Hx2].
    destruct Hx3 as [x Hx3 | x Hx3].
    {
      eapply i_inv_minimal; eauto.
      eapply InvD_implies_InvI; eauto.      
    }
    {
      eapply IH; eauto.
      eapply InvD_implies_InvD; eauto.
    }
  }
Qed.  
