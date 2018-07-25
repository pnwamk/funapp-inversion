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


(* Calculates the result type of calling a function which
   has the interface type `i` on value `v`. *)
Fixpoint d_result (i : dnf) (v : V) : option Ty :=
  match i with
  | DBase i => i_result i v
  | DCons i d' => match i_result i v, d_result d' v with
                  | None, None => None
                  | Some T, None => Some T
                  | None, Some T => Some T
                  | Some T, Some T' => Some (tyOr T T')
                  end
  end.
Hint Unfold d_result.


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

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*           DNF Inversion Definitions           *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* Calculates the result type of calling a function which
   has the interface type `i` on value `v`. *)
Fixpoint d_inv (i : dnf) (outT : Ty) : Ty :=
  match i with
  | DBase i => i_inv i outT
  | DCons i d' => tyOr (i_inv i outT) (d_inv d' outT)
  end.
Hint Unfold d_inv.


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
    eapply i_inv_sound; eauto.
  }
  {
    unfold InvD.
    intros outT f Hfd v v' Hv Hfv Hv'.
    simpl in *.
    destruct Hfd as [Hfi | Hfd].
    {
      left; eapply i_inv_sound; eauto.
    }
    {
      right; eapply IH; eauto.
    }      
  }
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                   Minimality                  *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


(* BOOKMARK *)
Theorem d_inv_minimal : forall d outT inT,
    InvD d outT inT ->
    Subtype (d_inv d outT) inT.
Proof with auto.
  intros d. induction d as [i | i d' IH].
  {
    intros outT inT Hinv x Hx. simpl in *.
    unfold InvD in Hinv.
    assert (Inv i outT inT) as Hinv' by eauto.
    eapply i_inv_minimal; eauto.
  }
  {
    intros outT inT Hinv x Hx.  simpl in *.
    destruct Hx as [x Hx | x Hx].
    {
      destruct (i_inv_exists_fn Hx) as [f [y [Hfi [Hyres Hy]]]].
      assert (FnD f (DCons i d')) as Hfd by eauto.
      unfold InvD in Hinv.
      eapply i_inv_minimal; eauto.
      unfold Inv.
      intros f' Hf' v v' Hv Hres' Hv'.
      eapply Hinv. simpl. left; eassumption. simpl.
    }
    {
      
    }
  }
  
