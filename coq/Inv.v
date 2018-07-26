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

Notation "'0'" := (Empty_set V).
Notation "'1'" := (Full_set V).
Notation "T1 '∩' T2" :=
  (Intersection V T1 T2) (at level 52, right associativity).
Notation "T1 '∪' T2" :=
    (Union V T1 T2) (at level 53, right associativity).
Notation "T1 '∖' T2" :=
  (Setminus V T1 T2) (at level 54, right associativity).
Notation "'¬' T" :=
  (1 ∖ T) (at level 51, right associativity).

Notation IsEmpty t := (~ Inhabited V t).
Notation IsInhabited t := (Inhabited V t).
Axiom IsEmpty_dec : forall (t: Ty), {IsEmpty t} + {IsInhabited t}.
Notation "x '∈' T" :=
  (In V T x) (at level 55, right associativity).
Notation "x '∉' T" :=
  (~ In V T x) (at level 55, right associativity).
Axiom in_dec : forall (v:V) (t: Ty), {v ∈ t} + {v ∉ t}.
Notation "T1 '<:' T2" :=
  (Included V T1 T2) (at level 55, right associativity).

Hint Unfold Included Setminus.
Hint Constructors Union Intersection Inhabited.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*         Basic Type Lemmas/Tactics             *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Lemma IsEmpty_eq : forall t,
    IsEmpty t -> t = 0.
Proof.
  intros t Hmt.
  apply Extensionality_Ensembles. constructor.
  intros v Hv. assert False. apply Hmt. exists v. auto.
  contradiction. intros v Hv. inversion Hv.
Qed.


Lemma no_empty_val : forall v P,
    v ∈ 0 -> P.
Proof.
  intros v P Hmt. inversion Hmt.
Qed.

Lemma no_empty_val_indirect : forall v T P,
    v ∈ T -> IsEmpty T -> P.
Proof.
  intros v T P Hv Hmt. rewrite (IsEmpty_eq Hmt) in Hv.
  eapply no_empty_val; eauto.
Qed.

Lemma union_empty_l : forall t,
    0 ∪ t = t.
Proof. crush. Qed.

Lemma union_empty_r : forall t,
    t ∪ 0 = t.
Proof.
  intros. rewrite Union_commutative.
  crush.
Qed.

Lemma intersection_empty_l : forall t,
    0 ∩ t = 0.
Proof. crush. Qed.

Lemma intersection_empty_r : forall t,
    t ∩ 0 = 0.
Proof. crush. Qed.

Lemma demorgan : forall x T1 T2,
    x ∉ (T1 ∪ T2) ->
    x ∉ T1 /\ x ∉ T2.
Proof. crush. Qed.


Hint Rewrite
     union_empty_l
     union_empty_r
     intersection_empty_l
     intersection_empty_r.

Hint Extern 1 =>
match goal with
| [H : ?x ∈ 0 |- ?P] =>
  apply (no_empty_val P H)
| [H : ?x ∈ ?T, H' : IsEmpty ?T |- ?P] =>
  apply (no_empty_val_indirect x P H H')
end.

Hint Extern 1 (_ ∈ _) =>
match goal with
| [H : ?x ∈ (?T1 ∩ ?T2) |- ?x ∈ ?T1]
  => destruct H; assumption
| [H : ?x ∈ (?T1 ∩ ?T2) |- ?x ∈ ?T2]
  => destruct H; assumption
| [H1 : ?x ∈ ?T1, H2 : ?x ∈ ?T2 |- ?x ∈ (?T1 ∩ ?T2)]
  => constructor; assumption
| [H1 : ?x ∈ ?T1 |- ?x ∈ (?T1 ∪ _)]
  => left; exact H1
| [H2 : ?x ∈ ?T2 |- ?x ∈ (_ ∪ ?T2)]
  => left; exact H2
end. 

Ltac inv_in_intersection :=
  match goal with
  | [H : _ ∈ (_ ∩ _) |- _] => destruct H
  end.

Ltac inv_in_union :=
  match goal with
  | [H : _ ∈ (_ ∪ _) |- _] => destruct H
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
  | ICons (T1,_) i' => T1 ∪ (i_dom i')
  end.
Hint Unfold i_dom.


(* Calculates the result type of calling a function which
   has the arrow type `a` on value `v`. *)
Fixpoint a_result (a : (Ty * Ty)) (v : V) : option Ty :=
  if in_dec v (fst a)
  then Some (snd a)
  else None.
Hint Unfold a_result.


(* Function Arrow *)
(* I.e., what it means for a function `f` to conform to the
   description given by arrow `a`. *)
Definition FnA (f : fn) (a : (Ty * Ty)) : Prop :=
forall x T,
  a_result a x = Some T ->
  (f x = Bot \/ exists y, f x = Res y /\ y ∈ T).
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
                  | Some T, Some T' => Some (T ∩ T')
                  end
  end.
Hint Unfold i_result.

(* Function Interface *)
(* I.e., what it means for a function `f` to conform to the
   description given by interface `i`. *)
Definition FnI (f : fn) (i : interface) : Prop :=
  forall x T,
    i_result i x = Some T ->
    f x = Bot \/ (exists y, (f x = Res y /\ y ∈ T)).
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
  specialize (H (T ∩ e)); crush.
  inv_in_intersection; crush; eauto.
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
  specialize (Hfi (T2 ∩ T));
    intuition; crush; inv_in_intersection; eauto.
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
  destruct (in_dec x T1) as [Hx1 | Hx1].
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
(*         Function Inversion Algorithm          *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

(* Consider function `f` of type `a`. This function
   calculates what type an argument `x` must _not_
   have had  if `(f x) ↝ v` and `v ∈ outT` *)
Fixpoint a_neg (a : (Ty * Ty)) (outT : Ty) : Ty :=
  if IsEmpty_dec ((snd a) ∩ outT)
  then (fst a)
  else 0.

(* Consider function `f` of type `i`. This function
   calculates what type an argument `x` must _not_ 
   have had if `(f x) ↝ v` and `v ∈ outT` *)
Fixpoint i_neg (i : interface) (outT : Ty) : Ty :=
  match i with
  | IBase a => a_neg a outT
  | ICons (S1,S2) i' =>
    let T1 := a_neg (S1,S2) outT in
    let T2 := i_neg i' outT in
    let T3 := S1 ∩ (i_neg i' (S2 ∩ outT)) in
    T1 ∪ T2 ∪ T3
  end.

(* Consider function `f` of type `i`. This function
   calculates what type an argument `x` must _have_
   had if `(f x) ↝ v` and `v ∈ outT` *)
Definition i_inv (i : interface) (outT : Ty) : Ty :=
  (i_dom i) ∖ (i_neg i outT).


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*      Function Inversion Lemmas/Tactics        *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma FnA_res_ty : forall T1 T2 f x y,
    x ∈ T1 ->
    f x = Res y ->
    FnA f (T1,T2) ->
    y ∈ T2.
Proof.
  intros T1 T2 f x y Hx Hfx Hfa.
  assert (f x = Bot \/ (exists y, (f x = Res y /\ y ∈ T2)))
    as Hex.
  eapply Hfa; crush.
  ifcase; crush.
  crush.
Qed.

Hint Extern 1 (_ ∈ _) =>
match goal with
| [Hx : ?x ∈ ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnA ?f (?T1,?T2)
   |- ?y ∈ ?T2]
  => apply (FnA_res_ty x Hx Hfy HFnA)
| [Hx : ?x ∈ ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (IBase (?T1,?T2))
   |- ?y ∈ ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
| [Hx : ?x ∈ ?T1,
        Hfy : ?f ?x = Res ?y,
              HFnA : FnI ?f (ICons (?T1,?T2) _)
   |- ?y ∈ ?T2]
  => apply (FnA_res_ty x Hx Hfy (FnI_first HFnA))
  end.


Lemma i_neg_sub : forall i T1 T2,
    T2 <: T1 ->
    (i_neg i T1) <: (i_neg i T2).
Proof with auto.
  intros i. induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros T T' Hsub x Hx. simpl in *.
    destruct (IsEmpty_dec (T2 ∩ T'))
      as [Hmt' | Hnmt']...
    destruct (IsEmpty_dec (T2 ∩ T))
      as [Hmt | Hnmt]...
    destruct (IsEmpty_dec (T2 ∩ T))
      as [Hmt | Hnmt]...
    assert False. apply Hmt.
    destruct Hnmt' as [y Hy]. exists y; eauto.
    contradiction.
  }
  {
    intros T T' Hsub x Hx.
    simpl in *.
    destruct (IsEmpty_dec (T2 ∩ T)) as [Hmt | Hnmt].
    {
      destruct (IsEmpty_dec (T2 ∩ T')) as [Hmt' | Hnmt'].
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
    destruct (IsEmpty_dec (T2 ∩ T')) as [Hmt' | Hnmt'].
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
        apply (IH (T2 ∩ T) (T2 ∩ T'))...
      }
    }                  
    {
      destruct Hx as [x Hx | x Hx]...
      destruct Hx as [x Hx | x Hx]...
      right. left. eapply IH; eauto.
      right. right; split...
      destruct Hx as [x Hx' Hx'']...
      apply (IH (T2 ∩ T) (T2 ∩ T'))...
    }
  }
Qed.

Ltac apply_fun :=
  match goal with
  | [H1 : ?x ∈ ?T1,
          Hf : FnI ?f (IBase (?T1,?T2)),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (y ∈ T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  | [H1 : ?x ∈ ?T1,
          Hf : FnA ?f (?T1,?T2),
               Hres : ?f ?x = Res ?y
     |- _] =>
    assert (y ∈ T2)
      by (exact (FnA_res_ty x H1 Hres (FnI_base Hf)))
  end.

Lemma in_i_neg : forall i v v' f T,
    FnI f i ->
    v ∈ (i_neg i T) ->
    f v = Res v' ->
    v' ∉ T.
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
    destruct (IsEmpty_dec (T2 ∩ T)) as [Hmt | Hnmt]...
    {
      inv_in_union.
      {
        apply_fun. apply Hmt; eauto.
      }
      {
        inv_in_union.
        {
          eapply IH; eauto. 
        }
        {
          inv_in_intersection.
          apply_fun. apply Hmt; eauto.
        }
      }
    }
    {
      rewrite union_empty_l in *.
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
    v' ∈ T ->
    v ∉ (i_neg i T).
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
      v ∈ (i_dom i) ->
      f v = Res v' ->
      v' ∈ outT ->
      v ∈ inT.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*               i_inv soundness                 *)
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
    exists v', f v = Res v' /\ v' ∈ T.


Definition MapsToTarget (f : fn) (i : interface) (tgt : Ty) : Prop :=
  forall v T,
    i_result i v = Some T ->
    IsInhabited (T ∩ tgt) ->
    exists v', f v = Res v'
               /\ v' ∈ (T ∩ tgt).

Axiom exists_fn : forall i,
    exists f, FnI f i /\ MapsTo f i.

Axiom exists_target_fn : forall i outT,
    exists f, FnI f i /\ MapsToTarget f i outT.



(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*         Lemmas related to i_result            *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)
  
Lemma i_result_None : forall i x outT,
    x ∈ (i_dom i) ->
    i_result i x = None ->
    x ∈ (i_neg i outT).
Proof with auto.
  intros i; induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros x outT Hdom Hires.
    simpl in *.
    destruct (in_dec x T1) as [Hx | Hx]; crush.
  }
  {
    intros x outT Hx Hires.
    simpl in *.
    destruct (in_dec x T1) as [Hx1 | Hx1].
    {
      destruct (IsEmpty_dec (T2 ∩ outT)) as [Hmt | Hnmt].
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
    IsEmpty (T ∩ outT) ->
    x ∈ (i_neg i outT).
Proof with auto.
  intros i x; induction i as [[T1 T2] | [T1 T2] i' IH].
  {
    intros T outT Hires Hmt.
    simpl in *.
    destruct (in_dec x T1) as [Hx1 | Hx1]; crush.
    destruct (IsEmpty_dec (T ∩ outT)) as [Hmt' | Hmt']...
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
    destruct (in_dec x T1) as [Hx1 | Hx1].
    {
      destruct (IsEmpty_dec (T2 ∩ outT)) as [Hmt2 | Hnmt2].
      {
        left...
      }
      {
        right.
        destruct (i_result i' x) as [S |]; try solve[crush].
        specialize (IH S).
        inversion Hires; subst. clear Hires.
        assert (IsEmpty (S ∩ T2 ∩ outT)) as Hmt3.
        {
          intros Hcontra. apply Hmt. inversion Hcontra as [y Hy].
          exists y. repeat inv_in_intersection. split...
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
    x ∈ (i_inv i outT) ->
    exists f y, FnI f i /\ f x = Res y /\ y ∈ outT.
Proof with auto.
  intros i outT x Hx.
  unfold i_inv in Hx.
  destruct Hx as [HxIs HxNot].
  remember (i_result i x) as xres.
  destruct xres as [S |].
  {
    symmetry in Heqxres.
    destruct (IsEmpty_dec (S ∩ outT)) as [Hmt | Hnmt].
    {
      assert (x ∈ (i_neg i outT)) as impossible.
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
    assert (x ∈ (i_neg i outT)) as impossible.
    {
      eapply i_result_None; eauto.
    }
    contradiction.
  }
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*             i_inv minimality                  *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Theorem i_inv_minimal : forall i outT inT,
    Inv i outT inT ->
    (i_inv i outT) <: inT.
Proof with auto.
  intros i outT inT Hinv x Hx.
  unfold Inv in Hinv.
  destruct (i_inv_exists_fn Hx) as [f [y [Hf [Hres Hy]]]].
  specialize (Hinv f Hf x y). eapply Hinv; eauto.
  destruct Hx...
Qed.




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
  | DCons i d' => (i_dom i) ∩ (d_dom d')
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
(*      DNF Function Inversion Algorithm         *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Fixpoint d_inv_aux (d : dnf) (outT : Ty) : Ty :=
  match d with
  | DBase i => i_inv i outT
  | DCons i d' => (i_inv i outT) ∪ (d_inv_aux d' outT)
  end.

(* Calculates the result type of calling a function which
   has the interface type `i` on value `v`. *)
Definition d_inv (d : dnf) (outT : Ty) : Ty :=
 (d_dom d) ∩ (d_inv_aux d outT).
Hint Unfold d_inv d_inv_aux.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*          DNF Inversion Definition             *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)


Definition InvD (d : dnf) (outT inT: Ty) : Prop :=
  forall (f:fn),
    FnD f d ->
    forall (v v':V),
      v ∈ (d_dom d) ->
      f v = Res v' ->
      v' ∈ outT ->
      v ∈ inT.
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
      assert (v ∈ (d_inv d' outT)) by (eapply IH; eauto).      
      right... unfold d_inv in *...
    }      
  }
Qed.

(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*            Lemma for Minimality               *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

Lemma d_inv_exists_fn : forall d outT x,
    x ∈ (d_inv d outT) ->
    exists f y, FnD f d /\ f x = Res y /\ y ∈ outT.
Proof with auto.
  intros d.
  induction d as [i | i d' IH];
    intros outT x Hx.
  {
    unfold d_inv in Hx.
    simpl in *. eapply i_inv_exists_fn...
  }
  {
    unfold d_inv in Hx.
    simpl in *.
    destruct Hx as [x Hx1 Hx2].
    destruct Hx2 as [x Hx2 | x Hx2].
    {
      assert (x ∈ (i_inv i outT)) as Hx by auto.
      destruct (i_inv_exists_fn Hx) as [f [y [H]]].
      exists f. exists y...
    }
    {
      unfold d_inv in Hx1.
      assert (x ∈ (d_inv d' outT)) as Hx.
      unfold d_inv...
      destruct (IH outT x Hx) as [f [y [H1 [H2 H3]]]].
      exists f. exists y...
    }    
  }
Qed.


(* * * * * * * * * * * * * * * * * * * * * * * * *)
(*                   Minimality                  *)
(* * * * * * * * * * * * * * * * * * * * * * * * *)

  
Theorem d_inv_minimal : forall d outT inT,
    InvD d outT inT ->
    (d_inv d outT) <: inT.
Proof with auto.
  intros d outT inT Hinv x Hx.
  destruct (d_inv_exists_fn Hx) as [f [y [H1 [H2 H3]]]].
  unfold d_inv in *. destruct Hx as [x Hx1 Hx2].
  unfold InvD in Hinv. 
  specialize (Hinv f H1 x y Hx1 H2 H3)...
Qed.  
