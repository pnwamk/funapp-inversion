
Require Import CpdtTactics.
Require Import Bool.
Require Import Nat.
Require Import String.
Require Import Ensembles.
Require Import Classical_sets.
Require Import List.
Require Import Permutation.
Import ListNotations.

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

Ltac eapplyH :=
  match goal with
  | [H : _ -> _ |- _] => progress (eapply H)
  end.

Ltac applyHinH :=
  match goal with
  | [H1 : _ -> _ , H2 : _ |- _] => apply H1 in H2
  end.


(**********************************************************)
(* Language Grammar                                       *)
(**********************************************************)

Inductive op : Set :=
  opAdd1
| opSub1
| opStrLen
| opNot
| opIsNat
| opIsStr
| opIsProc
| opIsZero.
Hint Constructors op.

Inductive const : Set :=
  cNat  : nat -> const
| cStr  : string -> const
| cBool : bool -> const
| cOp   : op -> const.
Hint Constructors const.

Inductive bty : Set := btNat | btTrue | btFalse | btStr.
Hint Constructors bty.

Inductive ty : Set :=
  tAny   : ty
| tEmpty : ty
| tBase  : bty -> ty
| tArrow : ty -> ty -> ty
| tOr    : ty -> ty -> ty
| tAnd   : ty -> ty -> ty
| tNot   : ty -> ty.
Hint Constructors ty.

Notation tTrue  := (tBase btTrue).
Notation tFalse := (tBase btFalse).
Notation tBool  := (tOr tTrue tFalse).
Notation tNat   := (tBase btNat).
Notation tStr   := (tBase btStr).

Inductive var : Set :=
  Var : nat -> var.
Hint Constructors var.

Definition interface := list (ty * ty).

Inductive exp : Set :=
  eVar   : var -> exp
| eVal   : val -> exp 
| eApp   : exp -> exp -> exp
| eIf    : exp -> exp -> exp -> exp
| eLet   : var -> exp -> exp -> exp

with

val : Set :=
  vConst : const -> val
| vAbs : var -> interface -> exp -> val.
  
  
Hint Constructors exp.

Definition vNat (n:nat) : val := (vConst (cNat n)).
Definition vStr (s:string) : val := (vConst (cStr s)).
Definition vBool (b:bool) : val := (vConst (cBool b)).
Definition vOp (o:op) : val := (vConst (cOp o)).
                
Inductive obj : Set :=
  oTop  : obj
| oVar : var -> obj.
Hint Constructors obj.

Inductive prop : Set :=
  Trivial : prop
| Absurd  : prop
| And     : prop -> prop -> prop
| Or      : prop -> prop -> prop
| Is      : var -> ty -> prop.
Hint Constructors prop.

Definition gamma := list prop.
Hint Unfold gamma.

Inductive tres : Set :=
  Res : ty -> prop -> prop -> obj -> tres.
Hint Constructors tres.

Hint Resolve PeanoNat.Nat.eq_dec.
Hint Resolve string_dec.
Hint Resolve bool_dec.


Definition op_dec : forall (x y : op),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve op_dec.

Definition const_dec : forall (x y : const),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve const_dec.

Definition bty_dec : forall (x y : bty),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve bty_dec.

Definition ty_dec : forall (x y : ty),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve ty_dec.

Definition var_dec : forall (x y : var),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve var_dec.

Definition int_dec : forall (x y : interface),
    {x = y} + {x <> y}.
Proof.
  Hint Resolve list_eq_dec.
  repeat decide equality.
Defined.
Hint Resolve int_dec.

Fixpoint exp_dec (x y : exp) : {x = y} + {x <> y}
with val_dec (x y : val) : {x = y} + {x <> y}.
Proof. decide equality. decide equality. Defined.
Hint Resolve exp_dec val_dec.

Definition obj_dec : forall (x y : obj),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve obj_dec.

Definition prop_dec : forall (x y : prop),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve prop_dec.

Definition tres_dec : forall (x y : tres),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve tres_dec.

Fixpoint fvsO (o:obj) : list var :=
  match o with
  | oVar x => [x]
  | oTop => []
  end.
Hint Unfold fvsO.


Fixpoint fvsP (p:prop) : list var :=
  match p with
  | Trivial => []
  | Absurd => []
  | And p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Or p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Is x t => [x]
  end.
Hint Unfold fvsP.

Fixpoint fvsR (R:tres) : list var :=
  match R with
  | Res t p q (oVar x) => [x] ++ (fvsP p) ++ (fvsP q)
  | Res t p q _ => (fvsP p) ++ (fvsP q)
  end.
Hint Unfold fvsP.


Fixpoint fvs (Γ:gamma) : list var :=
  match Γ with
  | [] => []
  | p::ps => (fvsP p) ++ (fvs ps)
  end.
Hint Unfold fvs.


(**********************************************************)
(* Dynamic Semantics                                      *)
(**********************************************************)

Definition apply_op (o:op) (arg:val) : option val :=
  match o , arg with
  | opAdd1   , (vConst (cNat n))      => Some (vConst (cNat (n + 1)))
  | opAdd1   , _                      => None
  | opSub1   , (vConst (cNat n))      => Some (vConst (cNat (n - 1)))
  | opSub1   , _                      => None
  | opStrLen , (vConst (cStr s))      => Some (vConst (cNat (String.length s)))
  | opStrLen , _                      => None
  | opNot    , (vConst (cBool false)) => Some (vConst (cBool true))
  | opNot    , _                      => Some (vConst (cBool false))
  | opIsNat  , (vConst (cNat _))      => Some (vConst (cBool true))
  | opIsNat  , _                      => Some (vConst (cBool false))
  | opIsStr  , (vConst (cStr _))      => Some (vConst (cBool true))
  | opIsStr  , _                      => Some (vConst (cBool false))
  | opIsProc , (vConst (cOp _))       => Some (vConst (cBool true))
  | opIsProc , (vAbs _ _ _)           => Some (vConst (cBool true))
  | opIsProc , _                      => Some (vConst (cBool false))
  | opIsZero , (vConst (cNat 0))      => Some (vConst (cBool true))
  | opIsZero , (vConst (cNat _))      => Some (vConst (cBool false))
  | opIsZero , _                      => None
  end.
Hint Unfold apply_op.

Fixpoint substitute (e:exp) (x:var) (v:val) : exp :=
  match e with
  | eVar y => if var_dec x y then (eVal v) else e
  | (eVal (vConst c)) => e
  | (eVal (vAbs y i e')) =>
    if var_dec x y then e
    else eVal (vAbs y i (substitute e' x v))
  | eApp e1 e2 => eApp (substitute e1 x v) (substitute e2 x v)
  | eIf e1 e2 e3 => eIf (substitute e1 x v)
                        (substitute e2 x v)
                        (substitute e3 x v)
  | eLet y e1 e2 =>
    let e1' := (substitute e1 x v) in
    let e2' := if var_dec x y then e2 else (substitute e2 x v) in
    eLet y e1' e2'
  end.

Inductive Step : exp -> exp -> Prop :=
| S_App_Cong1 : forall e1 e1' e2,
    Step e1 e1' ->
    Step (eApp e1 e2) (eApp e1' e2)
| S_App_Cong2 : forall v e2 e2',
    Step e2 e2' ->
    Step (eApp (eVal v) e2) (eApp (eVal v) e2')
| S_App_Op : forall o v v',
    apply_op o v = Some v' ->
    Step (eApp (eVal (vOp o)) (eVal v)) (eVal v')
| S_App_Abs : forall i x body v e',
    e' = substitute body x v ->
    Step (eApp (eVal (vAbs x i body)) (eVal v)) e'
| S_If_Cong : forall e1 e1' e2 e3,
    Step e1 e1' ->
    Step (eIf e1 e2 e3) (eIf e1' e2 e3)
| S_If_False : forall e e',
    Step (eIf (eVal (vBool false)) e e') e'
| S_If_NonFalse : forall v e e',
    v <> (vBool false) ->
    Step (eIf (eVal v) e e') e
| S_Let_Cong : forall x e1 e1' e2,
    Step e1 e1' ->
    Step (eLet x e1 e2) (eLet x e1' e2)
| S_Let : forall x v e,
    Step (eLet x (eVal v) e) (substitute e x v).
Hint Constructors Step.


Inductive Steps : exp -> exp -> Prop :=
| S_Null : forall e,
    Steps e e
| S_Cons : forall e1 e2 e3,
    Step e1 e2 ->
    Steps e2 e3 ->
    Steps e1 e3.
Hint Constructors Steps.

Lemma S_Trans : forall e1 e2 e3,
    Steps e1 e2 ->
    Steps e2 e3 ->
    Steps e1 e3.
Proof.
  intros e1 e2 e3 H12.
  generalize dependent e3.
  induction H12.
  {
    crush.
  }
  {
    intros e4 H34.
    eapply S_Cons. eassumption.
    applyH. assumption.
  }
Qed.  
  
(**********************************************************)
(* Subtyping                                              *)
(**********************************************************)

Notation "x '∈' T" :=
  (Ensembles.In val T x) (at level 55, right associativity).
Notation "x '∉' T" :=
  (~ Ensembles.In val T x) (at level 55, right associativity).

(* the domain types are denoted into *)
Axiom tInterp : ty -> (Ensemble val).
Axiom interp_tAny : tInterp tAny = (Full_set val).
Hint Rewrite interp_tAny.
Axiom interp_tEmpty : tInterp tEmpty = (Empty_set val).
Hint Rewrite interp_tEmpty.
Axiom interp_tOr : forall t1 t2,
    tInterp (tOr t1 t2) = Union val (tInterp t1) (tInterp t2).
Hint Rewrite interp_tOr.
Axiom interp_tAnd : forall t1 t2,
    tInterp (tAnd t1 t2) = Intersection val (tInterp t1) (tInterp t2).
Hint Rewrite interp_tAnd.
Axiom interp_tNot : forall t,
    tInterp (tNot t) = Setminus val (Full_set val) (tInterp t).
Hint Rewrite interp_tNot.
Axiom interp_tTrue : tInterp tTrue = (Singleton val (vBool true)).
Hint Rewrite interp_tTrue.
Axiom interp_tFalse : tInterp tFalse = (Singleton val (vBool false)).
Hint Rewrite interp_tFalse.
Axiom interp_tNat_exists : forall (v:val),
    v ∈ (tInterp tNat) ->
    exists (n:nat), v = (vConst (cNat n)).
Axiom interp_tNat_full : forall (n:nat),
    (vConst (cNat n)) ∈ (tInterp tNat).
Hint Resolve interp_tNat_full.
Axiom interp_tStr_exists : forall (v:val),
    v ∈ (tInterp tStr) ->
    exists (s:string), v = (vConst (cStr s)).
Axiom interp_tStr_full : forall (s:string),
    (vConst (cStr s)) ∈ (tInterp tStr).
Hint Resolve interp_tStr_full.

Notation "A '⊆' B" :=
  (Included val A B) (at level 55, right associativity).

Definition Subtype (t1 t2:ty) : Prop := (tInterp t1) ⊆ (tInterp t2).


Definition IsEmpty (t: ty) := (tInterp t) = (Empty_set val).
Hint Unfold IsEmpty.

Axiom empty_dec : forall (t: ty), {IsEmpty t} + {~ IsEmpty t}.
Axiom domain : ty -> option ty.
Axiom codomain : ty -> option ty.

Axiom domain_tArrow : forall t1 t2, domain (tArrow t1 t2) = Some t1.
Axiom codomain_tArrow : forall t1 t2, codomain (tArrow t1 t2) = Some t2.

Lemma Subtype_refl : forall t, Subtype t t.
Proof. crush. Qed.

Lemma Subtype_trans : forall t1 t2 t3,
    Subtype t1 t2 ->
    Subtype t2 t3 ->
    Subtype t1 t3.
Proof.
  intros.
  unfold Subtype in *.
  crush.
Qed.

Lemma Subtype_tAnd_L : forall t1 t2 t3,
    Subtype t1 t2 ->
    Subtype (tAnd t1 t3) (tAnd t2 t3).
Proof.
  intros t1 t2 t3 H12.
  unfold Subtype.
  intros x Hx.
  crush.
  apply Intersection_inv in Hx.
  crush.
Qed.

Lemma Subtype_tAnd_LL : forall t1 t2 t3 t4,
    Subtype t1 t2 ->
    Subtype (tAnd t2 t3) t4 ->
    Subtype (tAnd t1 t3) t4.
Proof.
Admitted.

Lemma Subtype_Empty : forall t1 t2,
    Subtype t1 t2 ->
    IsEmpty t2 ->
    IsEmpty t1.
Proof.
  intros.
  unfold Subtype in *.
  unfold IsEmpty in *. rewrite H0 in H.
  crush.
Qed.

Lemma Subtype_tAnd_LFalse : forall t1 t2,
    Subtype (tAnd t1 tFalse) t2 ->
    Subtype (tAnd t1 tFalse) (tAnd t2 tFalse).
Proof.
Admitted.

Lemma Subtype_tAnd_LNotFalse : forall t1 t2,
    Subtype (tAnd t1 (tNot tFalse)) t2 ->
    Subtype (tAnd t1 (tNot tFalse)) (tAnd t2 (tNot tFalse)).
Proof.
Admitted.

Lemma Subtype_L_tAnd : forall t1 t2 t3,
    Subtype t1 t3 ->
    Subtype (tAnd t1 t2) t3.
Proof.
  intros.
  unfold Subtype in *.
  intros x Hx.
  rewrite interp_tAnd in Hx.
  apply Intersection_inv in Hx. crush.
Qed.

Inductive Subobj : gamma -> obj -> obj -> Prop :=
| SO_Refl : forall Γ o,
    Subobj Γ o o
| SO_Top : forall Γ o,
    Subobj Γ o oTop.
Hint Constructors Subobj.

Lemma Subobj_trans : forall Γ o1 o2 o3,
    Subobj Γ o1 o2 ->
    Subobj Γ o2 o3 ->
    Subobj Γ o1 o3.
Proof.
  intros Γ o1 o2 o3 H12.
  generalize dependent o3.
  induction H12; crush.
  inversion H; crush.
Qed.

Inductive WellFormedProp : gamma -> prop -> Prop :=
| WFP : forall Γ p,
    incl (fvsP p) (fvs Γ) ->
    WellFormedProp Γ p.
Hint Constructors WellFormedProp.



Inductive Proves : gamma -> prop -> Prop :=
| P_Atom : forall Γ p,
    In p Γ ->
    Proves Γ p
| P_Trivial : forall Γ,
    Proves Γ Trivial
| P_Combine : forall Γ x t1 t2,
    Proves Γ (Is x t1) ->
    Proves Γ (Is x t2) ->
    Proves Γ (Is x (tAnd t1 t2))
| P_Empty : forall Γ x p t,
    IsEmpty t ->
    Proves Γ (Is x t) ->
    incl (fvsP p) (fvs Γ) ->
    Proves Γ p
| P_Sub : forall Γ x t1 t2,
    Proves Γ (Is x t1) ->
    Subtype t1 t2 ->
    Proves Γ (Is x t2)
| P_Absurd : forall Γ p,
    Proves Γ Absurd ->
    incl (fvsP p) (fvs Γ) ->
    Proves Γ p
| P_AndE_L : forall Γ p1 p2,
    Proves Γ (And p1 p2) ->
    Proves Γ p1
| P_AndE_R : forall Γ p1 p2,
    Proves Γ (And p1 p2) ->
    Proves Γ p2
| P_AndI : forall Γ p1 p2,
    Proves Γ p1 ->
    Proves Γ p2 ->
    Proves Γ (And p1 p2)
| P_OrE : forall Γ p1 p2 p,
    Proves Γ (Or p1 p2) ->
    Proves (p1::Γ) p ->
    Proves (p2::Γ) p ->
    Proves Γ p
| P_OrI_L : forall Γ p1 p2,
    Proves Γ p1 ->
    incl (fvsP p2) (fvs Γ) ->
    Proves Γ (Or p1 p2)
| P_OrI_R : forall Γ p1 p2,
    Proves Γ p2 ->
    incl (fvsP p1) (fvs Γ) ->
    Proves Γ (Or p1 p2).
Hint Constructors Proves.

Lemma Proves_dec : forall Γ p,
    Proves Γ p \/ ~ Proves Γ p.
Proof.
Admitted.
  
Lemma P_Cut : forall Γ p q,
    Proves Γ p ->
    Proves (p::Γ) q ->
    Proves Γ q.
Proof.
Admitted.


Lemma P_Env_Cut : forall Γ Γ' p,
    Forall (Proves Γ) Γ' ->
    Proves Γ' p ->
    Proves Γ p.
Proof.
Admitted.


Lemma Proves_sound : ~ Proves [] Absurd.
Proof.
Admitted.

Lemma fvs_inP_inΓ : forall x p Γ,
    In x (fvsP p) ->
    In p Γ ->
    In x (fvs Γ).
Proof.
  intros x p Γ Hin1 Hin2.
  induction Γ.
  {
    inversion Hin2.
  }
  {
    inversion Hin2; subst.
    simpl.
    apply in_app_iff. left. auto.
    simpl.
    apply in_app_iff. right. auto.        
  }
Qed.

Hint Unfold incl.

Lemma fvs_incl : forall Γ Γ',
    incl Γ Γ' ->
    incl (fvs Γ) (fvs Γ').
Proof.
  intros Γ.
  induction Γ; crush.
  unfold incl. intros b Hb. apply in_app_iff in Hb. destruct Hb.
  assert (In a Γ') as HIn by
        (apply H; left; auto).
  eapply fvs_inP_inΓ. eassumption. assumption.
  apply IHΓ.
  unfold incl. intros x Hx.
  apply H.
  right; auto. assumption.
Qed.

Lemma P_Subset : forall Γ Γ' p,
    Proves Γ p ->
    incl Γ Γ' ->
    Proves Γ' p.
Proof with crush.
  intros Γ Γ' p Hproves.
  generalize dependent Γ'. 
  induction Hproves...
  {
    eapply P_Empty... assumption. 
    eapply incl_tran. eassumption.
    apply fvs_incl. assumption.
  }
  {
    eapply P_Sub...
  }
  {
    apply P_Absurd.
    applyH. auto.
    eapply incl_tran. eassumption.
    apply fvs_incl. assumption.
  }
  {
    eapply P_AndE_L...
  }
  {
    eapply P_AndE_R...
  }
  {
    eapply P_OrE...
  }
  {
    eapply P_OrI_L; auto. eapply incl_tran.
    eassumption. apply fvs_incl. assumption.
  }
  {
    eapply P_OrI_R; auto. eapply incl_tran.
    eassumption. apply fvs_incl. assumption.
  }
Qed.

Lemma Proves_fvs_incl : forall Γ p,
    Proves Γ p ->
    incl (fvsP p) (fvs Γ).
Proof.
  intros Γ p Hp.
  induction Hp; crush.
  {
    intros x Hx.
    eapply fvs_inP_inΓ; eauto.
  }
  {
    eapply incl_tran. eassumption.
    apply incl_app; crush.
  }
Qed.    
  

Definition isa (o:obj) (t:ty) : prop :=
  match o with
  | oVar x => Is x t
  | oTop => if empty_dec t then Absurd else Trivial
  end.
Hint Unfold isa.


Lemma Prove_sub_isa : forall Γ o1 o2 t1 t2,
    Subobj Γ o1 o2 ->
    Subtype t1 t2 ->
    Proves Γ (isa o1 t1) ->
    Proves Γ (isa o2 t2).
Proof with crush.
  intros Γ o1 o2 t1 t2 HSO HS HP.
  inversion HSO; subst.
  {
    destruct o2...
    {
      unfold isa in *.
      destruct (empty_dec t1)...
      apply P_Absurd... ifcase...
      ifcase.
      assert (IsEmpty t1) as Hmt1 by (eapply Subtype_Empty; eauto).
      contradiction.
      crush.
    }
    {
      eapply P_Sub; eauto.
    }
  }
  {
    unfold isa in *.
    ifcase...
    ifcaseH.
    destruct o1...
    assert (IsEmpty t1) as Hmt1 by (eapply Subtype_Empty; eauto).
    eapply P_Empty; try eassumption.
    crush.
    assert (IsEmpty t1) as Hmt1 by (eapply Subtype_Empty; eauto).
    contradiction.
  }
Qed.

Inductive WellFormedRes : gamma -> tres -> Prop :=
| WFR : forall Γ R,
    incl (fvsR R) (fvs Γ) ->
    WellFormedRes Γ R.
Hint Constructors WellFormedRes.

Inductive Subres : gamma -> tres -> tres -> Prop :=
| SR_Sub : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    WellFormedRes Γ (Res t1 p1 q1 o1) ->
    Subtype t1 t2 ->
    Subobj Γ o1 o2 ->
    Proves (p1::Γ) p2 ->
    Proves (q1::Γ) q2 ->
    WellFormedRes Γ (Res t2 p2 q2 o2) ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2).
Hint Constructors Subres.


Lemma Subobj_Weakening : forall Γ Γ' o1 o2,
    Subobj Γ o1 o2 ->
    incl Γ Γ' ->
    Subobj Γ' o1 o2.
Proof with crush.
  intros Γ Γ' o1 o2 Hsub Hincl.
  destruct Hsub...
Qed.

Lemma Subtype_tAnds_False_trans : forall t1 t2 t3,
    Subtype (tAnd t1 tFalse) t2 ->
    Subtype (tAnd t2 tFalse) t3 ->
    Subtype (tAnd t1 tFalse) t3.
Proof.
Admitted.
  
Lemma Proves_incl : forall Γ Γ',
    incl Γ' Γ ->
    Forall (Proves Γ) Γ'.
Proof.
Admitted.

Lemma Subres_refl : forall Γ R,
    WellFormedRes Γ R ->
    Subres Γ R R.
Proof.
  intros Γ R Hwfr.
  destruct R.
  apply SR_Sub; crush.
Qed.
  
Lemma Subres_trans : forall Γ R1 R2 R3,
    Subres Γ R1 R2 ->
    Subres Γ R2 R3 ->
    Subres Γ R1 R3.
Proof with crush.
  intros Γ R1 R2 R3 H12.
  generalize dependent R3.
  inversion H12; intros R3 H23.  
  assert (Forall (Proves (p1 :: Γ)) (p2 :: Γ))
    as Hp1.
  {
    constructor. assumption.
    apply Proves_incl...
  }
  assert (Forall (Proves (q1 :: Γ)) (q2 :: Γ))
    as Hp2.
  {
    constructor. assumption.
    apply Proves_incl...        
  }
  inversion H23; subst.
  apply SR_Sub...
  {
    eapply Subtype_trans; eassumption.        
  }
  {
    eapply Subobj_trans; eassumption.        
  }
  {
    eapply P_Env_Cut; try eassumption.
  }
  {
    eapply P_Env_Cut; try eassumption.
  }
Qed.


(**********************************************************)
(* Type System                                            *)
(**********************************************************)

Definition predicate (t : ty) :=
  (tAnd (tArrow       t  tTrue)
        (tArrow (tNot t) tFalse)).
Hint Unfold predicate.

Definition op_type (o:op) : ty :=
  match o with
    opAdd1   => (tArrow tNat tNat)
  | opSub1   => (tArrow tNat tNat)
  | opStrLen => (tArrow tStr tNat)
  | opNot    => predicate tFalse
  | opIsNat  => predicate tNat
  | opIsStr  => predicate tStr
  | opIsProc => predicate (tArrow tEmpty tAny)
  | opIsZero => tArrow tNat tBool
  end.
Hint Unfold op_type.

Definition const_type (c:const) : ty :=
  match c with
  | cNat _  => tNat
  | cStr _  => tStr
  | cBool b => if b
               then tTrue
               else tFalse
  | cOp o => op_type o
  end.
Hint Unfold const_type.

Definition const_tres (c:const) : tres :=
  match c with
  | cBool false => (Res tFalse Absurd Trivial oTop)
  | _ => (Res (const_type c) Trivial Absurd oTop)
  end.
Hint Unfold const_tres.

Inductive InInterface : ty -> ty -> interface -> Prop :=
| InI_First : forall t1 t2 i,
    InInterface t1 t2 ((t1,t2)::i)
| InI_Rest : forall t1 t2 t3 t4 i,
    InInterface t1 t2 i ->
    InInterface t1 t2 ((t3,t4)::i).
Hint Constructors InInterface.

Fixpoint interface_ty (i:interface) : ty :=
  match i with
  | [] => tArrow tEmpty tAny
  | (t1,t2)::i' => (tAnd (tArrow t1 t2)
                         (interface_ty i'))
  end.
Hint Unfold interface_ty.

Fixpoint neg_interface_ty (i:interface) : ty :=
  match i with
  | [] => tAny
  | (t1,t2)::i' => (tAnd (tNot (tArrow t1 t2))
                         (neg_interface_ty i'))
  end.
Hint Unfold interface_ty.


Axiom pred_inv : ty -> ty -> (ty * ty).
(* Metafunction to determine what types a function
   is a predicate for. In another module we formally
   define and prove properties about such an algorithm.
   For this module, we just keep this abstract.  *)

Inductive TypeOf : gamma -> exp -> tres -> Prop :=
| T_Var : forall Γ x t R,
    Proves Γ (Is x t) ->
    Subres Γ
           (Res t
                (Is x (tAnd t (tNot tFalse)))
                (Is x (tAnd t tFalse))
                (oVar x))
           R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVar x) R 
| T_Const : forall Γ c R,
    Subres Γ (const_tres c) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVal (vConst c)) R
| T_Abs : forall Γ x i i' e t R,
    ~ In x (fvs Γ) ->
    t = (tAnd (interface_ty i) (neg_interface_ty i')) ->
    ~ IsEmpty t ->
    (forall t1 t2,
        InInterface t1 t2 i ->
        TypeOf ((Is x t1)::Γ) e (Res t2 Trivial Trivial oTop)) ->
    Subres Γ (Res t Trivial Absurd oTop) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVal (vAbs x i e)) R
| T_App : forall Γ e1 e2 t1 t2 o2 t tpos tneg R,
    TypeOf Γ e1 (Res t1 Trivial Trivial oTop) ->
    TypeOf Γ e2 (Res t2 Trivial Trivial o2) ->
    Subtype t1 (tArrow t2 t) ->
    pred_inv t1 t2 = (tpos , tneg) ->
    Subres Γ (Res t (isa o2 tpos) (isa o2 tneg) oTop) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eApp e1 e2) R
| T_If : forall Γ e1 e2 e3 t1 p1 q1 o1 R,
    TypeOf Γ e1 (Res t1 p1 q1 o1) ->
    TypeOf (p1::Γ) e2 R ->
    TypeOf (q1::Γ) e3 R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eIf e1 e2 e3) R.
Hint Constructors TypeOf.

Inductive TypeOfVal : val -> ty -> Prop :=
| TOV : forall v t,
    TypeOf [] (eVal v) (Res t Trivial Trivial oTop) ->
    TypeOfVal v t.
Hint Constructors TypeOfVal.

(* See Inv.v for details/proofs/etc about function inversion. *)
Axiom pred_inv_props : forall funty argty tpos tneg,
    pred_inv funty argty = (tpos, tneg) ->
    forall v1 v2 v3,
      TypeOfVal v1 funty ->
      TypeOfVal v2 argty ->
      Steps (eApp (eVal v1) (eVal v2)) (eVal v3) ->
      ((v3 <> (vBool false) /\ TypeOfVal v2 tpos)
       \/
       (v3 = (vBool false) /\ TypeOfVal v2 tneg)).


(*
  Consider fty ≤ fty' examples:

  1)  (A ∪ B) → C  ≤  A → C

  2)  (A → True)∩(¬A → False)  <:  Any → Bool

  And consider pred_inv(fty,  Any) = (tpos,  tneg)
  and          pred_inv(fty', Any) = (tpos', tneg')

  For example 1:
     pred_inv((A ∪ B) → C, Any) = ((A ∪ B), (A ∪ B))
     pred_inv(A → C,       Any) = (A, A)
     
     So fty ≤ fty', tpos' ≤ tpos, and tneg' ≤ tneg.
     
  For example 2:
     pred_inv((A → True)∩(¬A → False), Any) = (A, ¬A)
     pred_inv(Any → Bool,              Any) = (Any, Any)
     
     So fty ≤ fty', tpos ≤ tpos', and tneg ≤ tneg'.

*)


Axiom pred_inv_tNat_tNat :
  pred_inv (tArrow tNat tNat) tNat = (tNat, tEmpty).
Axiom pred_inv_tStr_tNat :
  pred_inv (tArrow tStr tNat) tStr = (tStr, tEmpty).
Axiom pred_inv_tNat_tBool :
  pred_inv (tArrow tNat tBool) tNat = (tNat, tNat).
Axiom pred_inv_predicate : forall t,
  pred_inv (predicate t) tAny = (t, (tNot t)).

Axiom domain_predicate : forall t, domain (predicate t) = Some tAny.
Axiom codomain_predicate : forall t, codomain (predicate t) = Some tBool.


Lemma Pred_pos_arg : forall funty argty tpos tneg,
    pred_inv funty argty = (tpos, tneg) ->
    Subtype tpos argty.
Proof.
Admitted.

Lemma Pred_neg_arg : forall funty argty tpos tneg,
    pred_inv funty argty = (tpos, tneg) ->
    Subtype tneg argty.
Proof.  
Admitted.
  

(**********************************************************)
(* Soundness                                              *)
(**********************************************************)

Lemma TypeOf_arrow_val : forall v t t1 t2,
    TypeOf [] (eVal v) (Res t Trivial Trivial oTop) ->
    Subtype t (tArrow t1 t2) ->
    (exists o, v = (vOp o))
    \/ (exists x i e, v = (vAbs x i e)).
Proof.
Admitted.

Lemma TypeOf_Op_Subtype : forall Γ o t,
    TypeOf Γ (eVal (vOp o)) (Res t Trivial Trivial oTop) ->
    Subtype (op_type o) t.
Proof.
Admitted.

Lemma Subtype_tArrow_dom : forall t1 t2 t3 t4,
    Subtype (tArrow t1 t2) (tArrow t3 t4) ->
    Subtype t3 t1.
Proof.
Admitted.

Lemma Subtype_tArrow_cdom : forall t1 t2 t3 t4,
    Subtype (tArrow t1 t2) (tArrow t3 t4) ->
    Subtype t2 t4.
Proof.
Admitted.

Lemma tArrow_R_dom_sub : forall t1 t2 t t',
    Subtype t (tArrow t1 t2) ->
    domain t = Some t' ->
    Subtype t1 t'.
Proof.
Admitted.

Lemma tArrow_R_cdom_sub : forall t1 t2 t t',
    Subtype t (tArrow t1 t2) ->
    codomain t = Some t' ->
    Subtype t' t2.
Proof.
Admitted.


Lemma TypeOf_Sub_type : forall Γ e t1 t2 p q o,
    TypeOf Γ e (Res t1 p q o) ->
    Subtype t1 t2 ->
    TypeOf Γ e (Res t2 p q o).
Proof.
Admitted.


Lemma TypeOf_tNat : forall Γ v p q o,
    TypeOf Γ (eVal v) (Res tNat p q o) ->
    exists n, v = vConst (cNat n).
Proof.
Admitted.

Lemma TypeOf_cNat_obj : forall Γ n t p q o,
    TypeOf Γ (eVal (vNat n)) (Res t p q o) ->
    o = oTop.
Proof.
Admitted.
  
Lemma TypeOf_tStr : forall Γ v p q o,
    TypeOf Γ (eVal v) (Res tStr p q o) ->
    exists s, v = vConst (cStr s).
Proof.
Admitted.

Lemma TypeOf_tTrue : forall Γ v p q o,
    TypeOf Γ (eVal v) (Res tTrue p q o) ->
    v = vConst (cBool true).
Proof.
Admitted.

Lemma TypeOf_tFalse : forall Γ v p q o,
    TypeOf Γ (eVal v) (Res tFalse p q o) ->
    v = vConst (cBool false).
Proof.
Admitted.

Lemma Empty_neq_tBase : forall bty1 bty2,
    bty1 <> bty2 ->
    IsEmpty (tAnd (tBase bty1) (tBase bty2)).
Proof.
Admitted.

Lemma tNat_not_tFalse_not_empty : ~ IsEmpty (tAnd tNat (tNot tFalse)).
Proof.
Admitted.

Lemma tNat_tFalse_empty : IsEmpty (tAnd tNat tFalse).
Proof.
Admitted.

Lemma tStr_not_tFalse_not_empty : ~ IsEmpty (tAnd tStr (tNot tFalse)).
Proof.
Admitted.

Lemma tStr_tFalse_empty : IsEmpty (tAnd tStr tFalse).
Proof.
Admitted.


Lemma TypeOf_Nat_lower_bound : forall Γ n t p q o,
    TypeOf Γ (eVal (vNat n)) (Res t p q o) ->
    Subtype tNat t.
Proof.
Admitted.

Lemma tNat_not_empty : forall t,
    Subtype tNat t ->
    ~ IsEmpty t.
Proof.
Admitted.

Lemma tNat_and_tFalse_not_empty : forall t,
    Subtype tNat t ->
    ~ IsEmpty (tAnd t (tNot tFalse)).
Proof.
Admitted.



Lemma Progress_App_op : forall t1 t2 o2 t tpos tneg R v2 o,
    TypeOf [] (eVal v2) (Res t2 Trivial Trivial o2) ->
    TypeOf [] (eVal (vOp o)) (Res t1 Trivial Trivial oTop) ->
    pred_inv t1 t2 = (tpos, tneg) ->
    WellFormedRes [] R ->
    Subres [] (Res t (isa o2 tpos) (isa o2 tneg) oTop) R ->
    Subtype (op_type o) (tArrow t2 t) ->
    (exists e' : exp, Step (eApp (eVal (vOp o)) (eVal v2)) e').
Proof with crush.
  intros funty argty o2 t tpos tneg R v2 o Hfunty Hargty
         Hpred Hwfr Hsres Hargsub.
  destruct o; simpl in *.
  { (* opAdd1 *)
    assert (Subtype argty tNat) as Hargty2
        by (eapply Subtype_tArrow_dom; eassumption).
    assert (exists n, v2 = vConst (cNat n)) as Hex
        by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto; crush).
    destruct Hex as [n Hn]; subst.
    exists (eVal (vNat (n + 1))).
    apply S_App_Op...
  }
  { (* opSub1 *)
    assert (Subtype argty tNat) as Hargty2
        by (eapply Subtype_tArrow_dom; eassumption).
    assert (exists n, v2 = vConst (cNat n)) as Hex
        by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto; crush).
    destruct Hex as [n Hn]; subst.
    exists (eVal (vNat (n - 1))).
    apply S_App_Op...
  }
  { (* opStrLen *)
    assert (Subtype argty tStr) as Hargty2
        by (eapply Subtype_tArrow_dom; eassumption).
    assert (exists s, v2 = vConst (cStr s)) as Hex
        by (eapply TypeOf_tStr; eapply TypeOf_Sub_type; eauto; crush).
    destruct Hex as [s Hs]; subst.
    exists (eVal (vNat (String.length s))).
    apply S_App_Op...
  }
  { (* opNot *)
    destruct (val_dec v2 (vBool false)) as [Hfalse | Hnonfalse].
    {
      exists (eVal (vBool true)).
      apply S_App_Op...
    }
    {
      exists (eVal (vBool false)).
      apply S_App_Op; destruct v2; simpl;
        repeat first[matchcase | ifcase | crush]...
    }
  }
  { (* opIsNat *)
    destruct v2.
    destruct c; try solve[exists (eVal (vBool false));
                                 apply S_App_Op; simpl;
                                 repeat first[matchcase | ifcase | crush]].
    { (* vNat *)
      exists (eVal (vBool true)); apply S_App_Op...
    }
    { (* vAbs *)
      exists (eVal (vBool false)).
      apply S_App_Op; simpl;
        repeat first[matchcase | ifcase | crush]...
    }
  }
  { (* opIsStr *)
    destruct v2.
    destruct c; try solve[exists (eVal (vBool false));
                                 apply S_App_Op; simpl;
                                 repeat first[matchcase | ifcase | crush]].
    { (* vStr *)
      exists (eVal (vBool true)); apply S_App_Op...
    }
    { (* vAbs *)
      exists (eVal (vBool false)).
      apply S_App_Op; simpl;
        repeat first[matchcase | ifcase | crush]...
    }
  }
  { (* opIsProc *)
    destruct v2.
    destruct c; try solve[exists (eVal (vBool false));
                                 apply S_App_Op; simpl;
                                 repeat first[matchcase | ifcase | crush]].
    { (* vOp *)
      exists (eVal (vBool true)); apply S_App_Op...
    }
    { (* vAbs *)
      exists (eVal (vBool true)); apply S_App_Op...
    }
  }
  { (* opIsZero *)
    assert (Subtype argty tNat) as Hargty2
        by (eapply Subtype_tArrow_dom; eassumption).
    assert (exists n, v2 = vConst (cNat n)) as Hex
        by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto; crush).
    destruct Hex as [n Hn]; subst.
    destruct n.
    exists (eVal (vBool true)); apply S_App_Op...
    exists (eVal (vBool false)); apply S_App_Op...
  }
Qed.


Lemma Progress : forall Γ e R,
    Γ = [] ->
    TypeOf Γ e R ->
    (exists v, e = (eVal v)) \/ (exists e', Step e e').
Proof with crush.
  intros Γ e R Hlive Htype.
  induction Htype; subst.
  { (* T_Var *)
    assert (incl (fvsP (Is x t)) (fvs [])) as Hcrazy.
    {
      apply Proves_fvs_incl. assumption.
    }
    simpl in *.
    unfold incl in Hcrazy.
    assert (In x []) as crazy.
    {
      apply Hcrazy. left; auto.
    }
    inversion crazy.
  }
  {
    left. exists (vConst c). reflexivity.
  }
  {
    left. exists (vAbs x i e). reflexivity.
  }
  {
    right. intuition.
    {
      match goal with
      | [H : (exists _, e1 = eVal _) |- _] =>  destruct H as [v1 Hv1]
      end.
      match goal with
      | [H : (exists _, e2 = eVal _) |- _] =>  destruct H as [v2 Hv2]
      end.
      subst.
      assert ((exists o : op, v1 = (vOp o))
              \/ (exists x i e, v1 = vAbs x i e))
        as Hv1opts.
      {
        eapply TypeOf_arrow_val. eassumption. eassumption.
      }
      destruct Hv1opts as [[o Ho] | [x [i [e Habs]]]]; subst.
      { 
        eapply Progress_App_op; eauto.
        eapply Subtype_trans.
        eapply TypeOf_Op_Subtype. eassumption. assumption.
      }
      { (* (vAbs x i e) *)
        exists (substitute e x v2). crush.
      }
    }
    {
      match goal with
      | [H : (exists _, Step _ _) |- _]
        =>  destruct H as [e1' Hstep1]
      end.
      exists (eApp e1' e2). apply S_App_Cong1...
    }
    {
      match goal with
      | [H : (exists _, _ = eVal _) |- _]
        =>  destruct H as [v1 Hv1]
      end.
      subst.
      match goal with
      | [H : (exists _, Step _ _) |- _]
        =>  destruct H as [e2' Hstep2]
      end.
      exists (eApp (eVal v1) e2'). apply S_App_Cong2...
    }
    {
      match goal with
      | [H : (exists _, Step _ _) |- _]
        =>  destruct H as [e1' Hstep1]
      end.
      exists (eApp e1' e2). apply S_App_Cong1...
    }
  }
  {
    intuition.
    match goal with
    | [H : (exists _, _ = eVal _) |- _]
      =>  destruct H as [v1 Hv1]
    end.
    subst.
    destruct (val_dec v1 (vBool false)) as [Htrue | Hfalse].
    {
      subst. right. exists e3. apply S_If_False.
    }
    {
      right. exists e2. apply S_If_NonFalse...
    }
    match goal with
    | [H : (exists _, Step _ _) |- _]
      =>  destruct H as [e1' Hstep1]
    end.
    right. exists (eIf e1' e2 e3). apply S_If_Cong...
  }
Qed.  

Lemma Typeof_type_subsume : forall Γ e t p q o t',
    TypeOf Γ e (Res t p q o) ->
    Subtype t t' ->
    TypeOf Γ e (Res t' p q o).
Proof with crush.
  intros Γ e t p q o t' Htype Hsub.
  remember (Res t p q o) as R.
  induction Htype; subst.
  { (* eVar *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_Var... eassumption.
    eapply Subres_trans... eassumption.
    apply SR_Sub...    
  }
  { (* vConst *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_Const... 
    eapply Subres_trans... eassumption.
    apply SR_Sub...    
  }
  { (* vAbs *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_Abs...
    applyH. eassumption.
    eapply Subres_trans... eassumption.
    apply SR_Sub...
  }
  { (* eApp *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_App...
    assumption. eassumption. eassumption.
    eapply Subres_trans... eassumption.
    apply SR_Sub...
  }
  { (* eIf *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_If.
    eassumption. applyH... applyH...
    assumption.
  }
Qed.


Inductive SimpleRes : tres -> Prop :=
| SRes : forall t p q,
    (p = Trivial \/ p = Absurd) ->
    (q = Trivial \/ q = Absurd) ->
    SimpleRes (Res t p q oTop).
Hint Constructors SimpleRes.

Lemma TypeOf_minimal : forall e R,
    TypeOf [] e R ->
    exists R', Subres [] R' R /\ SimpleRes R'.
Proof.
Admitted.

Lemma TypeOf_oTop : forall e t p q o,
    TypeOf [] e (Res t p q o) ->
    o = oTop.
Proof.
Admitted.

Lemma T_Subsume : forall Γ e R R',
    TypeOf Γ e R ->
    Subres Γ R R' ->
    TypeOf Γ e R'.
Proof.
Admitted.

Lemma SimpleRes_WellFormedRes : forall Γ R,
    SimpleRes R ->
    WellFormedRes Γ R.
Proof.
Admitted.

Lemma TypeOf_WellFormedRes : forall Γ e R,
    TypeOf Γ e R ->
    WellFormedRes Γ R.
Proof.
Admitted.

Lemma TypeOfVal_lower_bound : forall c t p q o t',
    TypeOf [] (eVal (vConst c)) (Res t p q o) ->
    const_type c = t' ->
    Subtype t' t.
Proof.
Admitted.

Lemma TypeOfVal_NonEmpty : forall v t,
    TypeOfVal v t ->
    ~ IsEmpty t.
Proof.
Admitted.


Lemma pred_single_tArrow_R : forall t,
  Subtype (predicate t) (tArrow tAny tBool).
Proof.
Admitted.

Lemma some_tNat_dec : forall v,
    (exists n, v = (vConst (cNat n)))
    \/ forall n, ~ v = (vConst (cNat n)).
Proof.
Admitted.

Lemma some_tStr_dec : forall v,
    (exists s, v = (vConst (cStr s)))
    \/ forall s, ~ v = (vConst (cStr s)).
Proof.
Admitted.

Lemma some_Proc_dec : forall v,
    (exists o, v = (vConst (cOp o)))
    \/
    (exists x i e, v = (vAbs x i e))
    \/
    ((forall o, v <> (vConst (cOp o)))
     /\ (forall x i e, v <> (vAbs x i e))).
Proof.
Admitted.



Lemma pred_inv_supertype : forall fty t1 t2 tpos tneg,
    pred_inv fty t1 = (tpos, tneg) ->
    Subtype fty (tArrow t1 t2) ->
    ((IsEmpty tpos -> IsEmpty (tAnd t2 (tNot tFalse)))
     /\
     (IsEmpty tneg -> IsEmpty (tAnd t2 tFalse))).
Proof.
Admitted.
(* Proof:

  f ∈ fty
  v ∈ t1

  and (pred_inv fty t1) = (tpos, tneg)

  then
  if (f v) = v' and v' ≠ false then v ∈ tpos
  if (f v) = false             then v ∈ tneg

  - - - - - - - - - - - - - - - -

  if fty ≤ t1 → t2, then (f v) ∈ t2

  - - - - - - - - - - - - - - - -

  (Conclusion 1)
  if tpos = ∅, can there ∃b ∈ (t2 ∩ ¬False)? if so then
  there exists a g ∈ t1 → t2 s.t. for some v ∈ t1,
  (g v) = b, but b ∈ tpos then (since it is in (t2 ∩ ¬False))
  which is impossible, so (t2 ∩ ¬False) = ∅.
  

  (Conclusion 2)
  if tneg = ∅, can there ∃b ∈ (t2 ∩ False)? if so then
  there exists a g ∈ t1 → t2 s.t. for some v ∈ t1,
  (g v) = b, but b ∈ tneg then (since it is in (t2 ∩ False))
  which is impossible, so (t2 ∩ False) = ∅.

 *)


Lemma empty_tAnd_L : forall t1 t2,
    IsEmpty t1 ->
    IsEmpty (tAnd t1 t2).
Proof.
Admitted.

Lemma TypeOf_tArrow_body : forall Γ x i body t1 t2 p q o,
    TypeOf Γ (eVal (vAbs x i body)) (Res (tArrow t1 t2) p q o) ->
    TypeOf ((Is x t1)::Γ) body (Res t2 p q o).
Proof.
Admitted.


Lemma Subres_weakening : forall Γ R1 R2 x t,
    Subres (Is x t :: Γ) R1 R2 ->
    ~ In x (fvs Γ) ->
    WellFormedRes Γ R1 ->
    WellFormedRes Γ R2 ->
    Subres Γ R1 R2.
Proof.
Admitted.

Lemma Proves_not_free_sub : forall x Γ t t',
    ~ In x (fvs Γ) ->
    Proves (Is x t :: Γ) (Is x t') ->
    Subtype t t'.
Proof.
Admitted.

Lemma TypeOfVal_False : forall t,
    TypeOfVal (vBool false) t ->
    Subtype tFalse t.
Proof.
Admitted.

Lemma WellFormed_then : forall Γ t p q o,
    WellFormedRes Γ (Res t p q o) ->
    incl (fvsP p) (fvs Γ).
Proof. Admitted.
Lemma WellFormed_else : forall Γ t p q o,
    WellFormedRes Γ (Res t p q o) ->
    incl (fvsP q) (fvs Γ).
Proof. Admitted.
Lemma WellFormed_obj : forall Γ t p q o,
    WellFormedRes Γ (Res t p q o) ->
    incl (fvsO o) (fvs Γ).
Proof. Admitted.

Lemma NoAbsurd_Is_Val : forall Γ v x t,
    TypeOfVal v t ->
    ~ Proves Γ Absurd ->
    ~ Proves (Is x t :: Γ) Absurd.
Proof.
Admitted.

Lemma Proves_lemma3 : forall y t t1 Γ,
    Subtype tFalse t ->
    ~ Proves (Is y t1 :: Γ) Absurd ->
    Proves (Is y (tAnd t tFalse)
               :: Is y (tAnd t tFalse)
               :: Is y t1
               :: Γ)
           Absurd ->
    False.
Proof.
Admitted.

Lemma Subtype_tFalse_tAnd_trans : forall t t',
    Subtype tFalse t ->
    Subtype (tAnd t tFalse) t' ->
    Subtype tFalse t'.
Proof.
Admitted.

Lemma TypeOfVal_TypeOf : forall Γ v t,
    TypeOfVal v t ->
    TypeOf Γ (eVal v) (Res t Trivial Trivial oTop).
Proof.
Admitted.

Lemma TypeOfVal_Sub : forall v t t',
    TypeOfVal v t ->
    Subtype t t' ->
    TypeOfVal v t'.
Proof.
Admitted.

Lemma T_Empty_env : forall Γ v t,
    TypeOfVal v t ->
    TypeOf Γ (eVal v) (Res t Trivial Trivial oTop).
Proof.
Admitted.

Lemma Proves_lemma4 : forall y t1 t Γ p,
    Proves (isa (oVar y) (tAnd t (tNot tFalse))
                :: Is y (tAnd t (tNot tFalse))
                :: Is y t1
                :: Γ)
           p -> 
    Proves (Is y t1
               :: isa oTop (tAnd t (tNot tFalse))
               :: Trivial
               :: Γ)
           p.
Proof.
Admitted.
Lemma Proves_lemma5 : forall y t1 t Γ q,
    Proves  (isa (oVar y) (tAnd t tFalse)
                 :: Is y (tAnd t tFalse)
                 :: Is y t1
                 :: Γ)
            q ->
    Proves (Is y t1 :: isa oTop (tAnd t tFalse) :: Trivial :: Γ) q.
Proof.
Admitted.

Lemma Proves_lemma6 : forall Γ t1 t y,
    ~ IsEmpty t ->
    ~ Proves (Is y t1 :: Γ) Absurd ->
    (~ (Proves (isa (oVar y) (tAnd t (tNot tFalse))
                    :: Is y (tAnd t (tNot tFalse))
                    :: Is y t1
                    :: Γ)
               Absurd)
     \/ ~ (Proves (isa (oVar y) (tAnd t tFalse)
                       :: Is y (tAnd t tFalse)
                       :: Is y t1
                       :: Γ)
                  Absurd)).
Proof.
Admitted.

Lemma NonEmpty_floor : forall t1 t2,
    Subtype t1 t2 ->
    ~ IsEmpty t1 ->
    ~ IsEmpty t2.
Proof.
Admitted.

Lemma val_Is_dec : forall v t,
    {TypeOfVal v t} + {TypeOfVal v (tNot t)}.
Proof.
Admitted.


Fixpoint eraseP (p:prop) (x:var) (v:val) : prop :=
  match p with
   | Trivial => Trivial
   | Absurd => Absurd
   | Is y t => if var_dec x y
               then if val_Is_dec v t
                    then Trivial
                    else Absurd
               else Is y t
   | And p q => And (eraseP p x v) (eraseP q x v)
   | Or p q  => Or (eraseP p x v) (eraseP q x v)
  end.

Definition eraseO (o:obj) (x:var) : obj :=
  match o with
  | oTop => oTop
  | oVar y => if var_dec x y
              then oTop
              else oVar y
  end.

Definition eraseR (R:tres) (x:var) (v:val) : tres :=
  match R with
  | Res t p q o => Res t (eraseP p x v) (eraseP q x v) (eraseO o x)
  end.

Lemma incl_dedup_cons : forall A (x:A) l1 l2,
    incl l1 (x :: x :: l2) ->
    incl l1 (x :: l2).
Proof.
Admitted.

Lemma incl_eraseP : forall p x t Γ,
    incl (fvsP p) (x :: fvs Γ) ->
    incl (fvsP (eraseP p x t)) (fvs Γ).
Proof.
Admitted.

Lemma Proves_weakening_cons : forall p q Γ,
    Proves Γ q ->
    Proves (p::Γ) q.
Proof.
Admitted.

Lemma Proves_swap_head : forall p q r Γ,
    Proves (p::q::Γ) r ->
    Proves (q::p::Γ) r.
Proof.
Admitted.

Lemma Proves_combine_Is_tAnd : forall x t t1 t' p Γ,
    Subtype t1 t ->
    Proves (Is x (tAnd t t') :: Is x t1 :: Γ) p ->
    Proves (Is x (tAnd t1 t') :: Γ) p.
Proof.
Admitted.
Lemma eraseP_false : forall x t Γ p,
    Proves (Is x (tAnd t tFalse) :: Γ) p ->
    Proves Γ (eraseP p x (vConst (cBool false))).
Proof.
Admitted.
Lemma eraseP_nonfalse : forall x t Γ p v,
    Proves (Is x (tAnd t (tNot tFalse)) :: Γ) p ->
    v <> (vConst (cBool false)) ->
    Proves Γ (eraseP p x v).
Proof.
Admitted.
Lemma WellFormedRes_eraseR : forall Γ x t v R,
    WellFormedRes (Is x t :: Γ) R ->
    WellFormedRes Γ (eraseR R x v).
Proof.
Admitted.

Lemma WellFormedRes_Perm : forall Γ Γ' R,
    WellFormedRes Γ R ->
    Permutation Γ Γ' ->
    WellFormedRes Γ' R.
Proof.
Admitted.

Lemma TypeOf_Val_NonFalse : forall v t Γ,
    TypeOfVal v t ->
    v <> vConst (cBool false) ->
    TypeOf Γ (eVal v) (Res t Trivial Absurd oTop).
Proof.
Admitted.

Lemma Proves_neq_cons : forall x y t1 t2 Γ,
    Proves ((Is x t1)::Γ) (Is y t2) ->
    x <> y ->
    Proves Γ (Is y t2).
Proof.
Admitted.

Lemma eraseR_Subres : forall x t v Γ R R',
    TypeOfVal v t ->
    ~ In x (fvs Γ) ->
    Subres (Is x t :: Γ) R R' ->
    ~ In x (fvsR R) ->
    Subres Γ R (eraseR R' x v).
Proof.
Admitted.

Lemma WellFormedRes_const : forall Γ c,
    WellFormedRes Γ (const_tres c).
Proof.
Admitted.

Lemma Proves_Perm : forall Γ Γ' p,
    Proves Γ p ->
    Permutation Γ Γ' ->
    Proves Γ' p.
Proof.
Admitted.

Lemma Subres_Perm : forall Γ Γ' R R',
    Subres Γ R R' ->
    Permutation Γ Γ' ->
    Subres Γ' R R'.
Proof.
Admitted.

Lemma Not_In_Perm : forall Γ Γ' x,
    ~ In x (fvs Γ) ->
    Permutation Γ Γ' ->
    ~ In x (fvs Γ').
Proof.
Admitted.

Lemma eraseP_isa : forall o t x v,
    eraseP (isa o t) x v = (isa (eraseO o x) t).
Proof.
Admitted.

Lemma WellFormedRes_weakening : forall p Γ R,
    WellFormedRes Γ R ->
    WellFormedRes (p::Γ) R.
Proof.
Admitted.

Inductive MinimalValType : val -> ty -> Prop :=
| MVT : forall v t,
    TypeOfVal v t ->
    (forall t', TypeOfVal v t' ->
                Subtype t t') ->
    MinimalValType v t.

Lemma Substitution : forall Γ' body R,
    TypeOf Γ' body R ->
    forall Γ z v t1,
    ~ In z (fvs Γ) ->
    Permutation Γ' ((Is z t1)::Γ) ->
    TypeOfVal v t1 ->
    (exists R',
        TypeOf Γ (substitute body z v) R'
        /\ Subres Γ R' (eraseR R z v)).
Proof with crush.
  intros Γ body R Hbody.
  induction Hbody; intros Γ' z v tv Hfree HPerm Hv.
  { (* T_Var *)
    simpl.      
    destruct (var_dec z x); subst.
    { (* z = x *)
      assert (Proves (Is x tv :: Γ') (Is x t)) as Hp
          by (eapply Proves_Perm; eauto).
      assert (Subtype tv t) as Hsub
          by (eapply Proves_not_free_sub; eassumption).      
      destruct (val_dec v (vConst (cBool false))) as [Heq | Hneq].
      { (* v = vConst (cBool false) *)
        exists (Res tv Absurd Trivial oTop); split.
        inversion Hv; subst.
        constructor... constructor...
        match goal with
        | [ H : TypeOf _ (eVal (vConst (cBool false))) _ |- _]
          => inversion H
        end; subst.
        match goal with
        | [ H : Subres _ (const_tres (cBool false)) _ |- _]
          => inversion H
        end; subst.
        all: crush.
        destruct R.
        match goal with
        | [ H : Subres _ _ _ |- _] => inversion H
        end; subst.
        constructor...
        eapply Subtype_trans; eassumption.
        match goal with
        | [ H : Subobj _ _ _ |- _] => inversion H
        end; subst.
        simpl.
        ifcase...
        simpl. crush.
        apply P_Absurd. crush. crush.
        assert (incl (fvsP p) (fvs (Is x (tAnd t (tNot tFalse))::(Is x tv)::Γ')))
          as Hincl.
        {
          eapply Proves_fvs_incl.
          eapply Proves_Perm. eassumption. crush.
        }
        simpl in Hincl.
        apply incl_dedup_cons in Hincl.
        apply incl_eraseP. assumption.
        assert (Subtype tFalse tv) as Htv.
        {
          inversion Hv; subst.
          eapply TypeOfVal_lower_bound. eassumption.
          crush.
        }          
        assert (Proves (Is x (tAnd tv tFalse) :: Γ') p0) as Hp0.
        {
          eapply Proves_combine_Is_tAnd. eassumption.
          eapply Proves_Perm. eassumption. crush.
        }
        eapply eraseP_false.
        apply Proves_swap_head.
        apply Proves_weakening_cons. eassumption.
        assert (WellFormedRes Γ' (eraseR (Res t0 p p0 o)
                                         x
                                         (vConst (cBool false)))).
        {
          eapply WellFormedRes_eraseR.
          eapply WellFormedRes_Perm; eassumption.
        }
        crush.
      }
      { (* v <> vConst (cBool false) *)
        exists (Res tv Trivial Absurd oTop); split.
        inversion Hv; subst.
        apply TypeOf_Val_NonFalse...
        destruct R.
        match goal with
        | [ H : Subres _ _ _ |- _] => inversion H
        end; subst.
        constructor...
        eapply Subtype_trans; eassumption.
        match goal with
        | [ H : Subobj _ _ _ |- _] => inversion H
        end; subst.
        simpl.
        ifcase...
        simpl. crush.
        apply Proves_weakening_cons.
        assert (Proves ((Is x (tAnd tv (tNot tFalse)))::Γ') p) as Hproves.
        {
          eapply Proves_combine_Is_tAnd. eassumption.
          eapply Proves_Perm. eassumption. crush.
        }
        eapply eraseP_nonfalse; eauto.
        apply P_Absurd. crush.
        simpl.
        assert (incl (fvsP p0) (fvs (Is x (tAnd t tFalse)::(Is x tv)::Γ')))
          as Hincl.
        {
          eapply Proves_fvs_incl.
          eapply Proves_Perm. eassumption. crush.
        }
        simpl in Hincl.
        apply incl_dedup_cons in Hincl.
        apply incl_eraseP. assumption.
        assert (WellFormedRes Γ' (eraseR (Res t0 p p0 o) x v)).
        {
          eapply WellFormedRes_eraseR.
          eapply WellFormedRes_Perm; eassumption.
        }
        crush.
      }
    }
    { (* z <> x *)
      exists (Res t
                  (Is x (tAnd t (tNot tFalse)))
                  (Is x (tAnd t tFalse))
                  (oVar x)).
      assert (Proves Γ' (Is x t)) as Hy.
      {
        eapply Proves_neq_cons. eapply Proves_Perm; eassumption. assumption.
      }
      assert (incl (fvsP (Is x t)) (fvs Γ')) as Hincl by
            (eapply Proves_fvs_incl; crush).
      split.
      eapply T_Var. eassumption.
      apply Subres_refl.
      constructor... constructor...
      eapply eraseR_Subres; eauto. simpl.
      eapply Subres_Perm. eassumption. assumption. intros contra.
      crush.
    }
  }
  { (* T_Const *)
    simpl.
    exists (const_tres c). split. constructor. apply Subres_refl.
    apply WellFormedRes_const. apply WellFormedRes_const.
    eapply eraseR_Subres; eauto.
    eapply Subres_Perm. eassumption. assumption.
    intros contra.
    destruct c; crush.
    repeat ifcaseH...
  }
  { (* T_Abs *)
    simpl in *. subst.
    assert (~ In x (fvs (Is z tv :: Γ'))) as Hfree'
        by (eapply Not_In_Perm; eauto).
    assert (z <> x) as Hneq by crush.
    ifcase...
    exists (Res (tAnd (interface_ty i) (neg_interface_ty i'))
                Trivial Absurd oTop).
    split.
    eapply T_Abs.
    assumption.
    apply (eq_refl (tAnd (interface_ty i) (neg_interface_ty i'))).
    assumption.
    intros dom cdom HInt.
    assert (exists R' : tres,
               TypeOf ((Is x dom)::Γ') (substitute e z v) R' /\
               Subres ((Is x dom)::Γ') R' (Res cdom Trivial Trivial oTop))
      as Hex.
    {
      eapplyH. eassumption. crush.
      rewrite HPerm. apply perm_swap. 
      assumption.
    }
    destruct Hex as [R' [Htype Hsres]].
    eapply T_Subsume; eassumption.
    apply Subres_refl. crush. crush.
    assert (Subres (Is z tv :: Γ')
                   (Res (tAnd (interface_ty i) (neg_interface_ty i'))
                        Trivial
                        Absurd
                        oTop)
                   R)
      as Hsres' by (eapply Subres_Perm; eauto).
    eapply eraseR_Subres. eassumption.
    assumption. assumption.
    simpl. auto.
  }
  { (* T_App *)
    assert (exists R' : tres,
               TypeOf Γ' (substitute e1 z v) R' /\
               Subres Γ' R' (eraseR (Res t1 Trivial Trivial oTop) z v))
      as Hlhs by (eapplyH; crush).
    destruct Hlhs as [Rl [Hltype Hlsub]].
    assert (exists R' : tres,
               TypeOf Γ' (substitute e2 z v) R' /\
               Subres Γ' R' (eraseR (Res t2 Trivial Trivial o2) z v))
      as Hrhs by (eapplyH; crush).
    destruct Hrhs as [Rr [Hrtype Hrsub]].
    exists (eraseR (Res t (isa o2 tpos) (isa o2 tneg) oTop) z v).
    simpl in *.
    split.
    eapply T_App.
    eapply T_Subsume; eassumption.
    eapply T_Subsume; eassumption.
    eassumption. eassumption.
    repeat rewrite eraseP_isa. apply Subres_refl.
    assert (WellFormedRes Γ' (eraseR (Res t (isa o2 tpos) (isa o2 tneg) oTop) z v)).
    {
      eapply WellFormedRes_eraseR.
      eapply WellFormedRes_Perm.
      match goal with
      | [ H : Subres Γ _ R |- _] => inversion H
      end.
      eassumption. eassumption.
    }
    simpl in *.
    repeat rewrite eraseP_isa in *.
    crush.
    assert (WellFormedRes Γ' (eraseR (Res t (isa o2 tpos) (isa o2 tneg) oTop) z v)).
    {
      eapply WellFormedRes_eraseR.
      eapply WellFormedRes_Perm.
      match goal with
      | [ H : Subres Γ _ R |- _] => inversion H
      end.
      eassumption. eassumption.
    }
    simpl in *.
    repeat rewrite eraseP_isa in *.
    crush.
    assert (Subres (Is z tv :: Γ')
                   (Res t (isa o2 tpos) (isa o2 tneg) oTop)
                   R)
      as Hsub' by (eapply Subres_Perm; eauto).
    eapply eraseR_Subres; try eassumption.
    inversion Hsub'; subst.
    apply SR_Sub.
    apply WellFormedRes_weakening.
    assert (WellFormedRes Γ'
                          (eraseR (Res t (isa o2 tpos) (isa o2 tneg) oTop) z v)).
    {
      eapply WellFormedRes_eraseR.
      eapply WellFormedRes_Perm.
      eassumption. apply Permutation_refl.
    }
    crush.
    assumption.
    assumption.
    (* TODO lemma about how, since z is not free in Γ', then Is z tv
       and possible Is z tpos/tneg are the most specific things
       we could have used about z to prove p2/q2 respectively, and therefore
       after the erasure we can still prove p2/q2... right? 
       NOTE: it seems like maybe we should be erasing z in p2/q2 as well
             in order to prove this... did we make a wrong turn getting here?*)
    
  }
  { (* T_If *)
    
  }
  
  
  Lemma Proves_lemma1 : forall t2 tpos tneg t' o' p' q' x t,
    ~ IsEmpty t2 ->
    (IsEmpty tpos -> IsEmpty (tAnd t (tNot tFalse))) ->
    (IsEmpty tneg -> IsEmpty (tAnd t tFalse)) ->
    Proves [Is x t2; isa o' (tAnd t' (tNot tFalse)); p'] (isa oTop tpos) ->
    Proves [Is x t2; isa o' (tAnd t' tFalse); q'] (isa oTop tneg) ->
    ((Proves [isa o' (tAnd t' (tNot tFalse)); p'] (isa oTop tpos))
     /\
     (Proves [isa o' (tAnd t' tFalse); q'] (isa oTop tneg))).
Proof.
Admitted.
  
Lemma Preservation : forall e e' R,
    TypeOf [] e R ->
    Step e e' ->
    exists R', TypeOf [] e' R'
               /\ Subres [] R' R.
Proof with crush.
  intros e e' R Htype.  
  generalize dependent e'.
  remember [] as Γ.
  induction Htype;
    intros e' Hstep;
    try solve[inversion Hstep].
  { (* T_App *)
    subst.
    assert (o2 = oTop) as Ho2 by (eapply TypeOf_oTop; eassumption). subst.
    exists (Res t (isa oTop tpos) (isa oTop tneg) oTop).
    split.
    inversion Hstep; subst.
    { (* (e1 e2) --> (e1' e2) *)
      assert (exists R' : tres,
                 TypeOf [] e1' R'
                 /\ Subres [] R' (Res t1 Trivial Trivial oTop))
        as IH1 by crush.
      destruct IH1 as [[t1' p1' q1' o1'] [Htype1' HSR1']].
      subst.
      eapply T_App. eapply T_Subsume. eassumption. eassumption.
      eassumption. eassumption. eassumption. apply Subres_refl.
      apply SimpleRes_WellFormedRes...
      repeat ifcase; crush. repeat ifcase; crush.
      constructor; crush. repeat ifcase; crush.
    }
    { (* (v e2) --> (v e2') *)
      assert (exists R' : tres,
                 TypeOf [] e2' R'
                 /\ Subres [] R' (Res t2 Trivial Trivial oTop))
        as IH2 by crush.
      destruct IH2 as [[t2' p2' q2' o2'] [Htype2' HSR2']].
      eapply T_App. eassumption.
      eapply T_Subsume. eassumption. eassumption.
      eassumption. eassumption. apply Subres_refl.
      apply SimpleRes_WellFormedRes...
      repeat ifcase; crush. repeat ifcase; crush.
      constructor; crush. repeat ifcase; crush.
    }
    { (* (o v) --> v'   where Some v' = apply_op o v *)
      destruct o.
      { (* opAdd1 *)
        assert (Subtype (op_type opAdd1) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (tArrow tNat tNat) (tArrow t2 t)) as
            Hopsub by (eapply Subtype_trans; eauto).
        (* the result is a supertype of the op result *)
        assert (Subtype tNat t) as Hcdom
            by (eapply Subtype_tArrow_cdom; eauto).
        (* the arg type is a subtype of the domain *)
        assert (Subtype t2 tNat) as Hdom
            by (eapply Subtype_tArrow_dom; eauto).
        clear Hopsub.
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert (exists n, v = vConst (cNat n)) as Hnat
            by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto).
        destruct Hnat as [n Hn].
        subst.
        match goal with
        | [ H : Some (vConst (cNat _)) = Some _ |- _]
          => inversion H; subst
        end.
        assert (Subtype tNat t2) as Ht2low by
              (eapply TypeOfVal_lower_bound; eauto).
        assert (TypeOfVal (vOp opAdd1) t1) as Hval1 by crush.
        assert (TypeOfVal (vNat n) t2) as Hval2 by crush.
        assert (((vNat (n + 1)) <> (vBool false) /\ TypeOfVal (vNat n) tpos)
                \/ ((vNat (n + 1)) = (vBool false) /\ TypeOfVal (vNat n) tneg))
          as Hres.
        {
          eapply pred_inv_props; try eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
        {
          assert (~ IsEmpty tpos) as Hnmt
              by (eapply TypeOfVal_NonEmpty; eauto).
          eapply T_Subsume. apply T_Const. simpl. apply Subres_refl.
          crush. crush.
          apply SR_Sub...
          ifcase. apply P_Absurd... ifcase; crush.
          ifcase...
          assert (IsEmpty (tAnd tNat tFalse)) by (apply Empty_neq_tBase; crush).
          repeat ifcase... repeat ifcase...
        }
        {
          inversion Heq.
        }
      }
      { (* opSub1 *)
        assert (Subtype (op_type opSub1) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (tArrow tNat tNat) (tArrow t2 t)) as
            Hopsub by (eapply Subtype_trans; eauto).
        (* the result is a supertype of the op result *)
        assert (Subtype tNat t) as Hcdom
            by (eapply Subtype_tArrow_cdom; eauto).
        (* the arg type is a subtype of the domain *)
        assert (Subtype t2 tNat) as Hdom
            by (eapply Subtype_tArrow_dom; eauto).
        clear Hopsub.
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert (exists n, v = vConst (cNat n)) as Hnat
            by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto).
        destruct Hnat as [n Hn].
        subst.
        match goal with
        | [ H : Some (vConst (cNat _)) = Some _ |- _]
          => inversion H; subst
        end.
        assert (Subtype tNat t2) as Ht2low by
              (eapply TypeOfVal_lower_bound; eauto).
        assert (TypeOfVal (vOp opSub1) t1) as Hval1 by crush.
        assert (TypeOfVal (vNat n) t2) as Hval2 by crush.
        assert (((vNat (n - 1)) <> (vBool false) /\ TypeOfVal (vNat n) tpos)
                \/ ((vNat (n - 1)) = (vBool false) /\ TypeOfVal (vNat n) tneg))
          as Hres.
        {
          eapply pred_inv_props; try eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
        {
          assert (~ IsEmpty tpos) as Hnmt
              by (eapply TypeOfVal_NonEmpty; eauto).
          eapply T_Subsume. apply T_Const. simpl. apply Subres_refl.
          crush. crush.
          apply SR_Sub...
          ifcase. apply P_Absurd... ifcase; crush.
          ifcase...
          assert (IsEmpty (tAnd tNat tFalse)) by (apply Empty_neq_tBase; crush).
          repeat ifcase... repeat ifcase...
        }
        {
          inversion Heq.
        }
      }
      { (* opSub1 *)
        assert (Subtype (op_type opStrLen) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (tArrow tStr tNat) (tArrow t2 t)) as
            Hopsub by (eapply Subtype_trans; eauto).
        (* the result is a supertype of the op result *)
        assert (Subtype tNat t) as Hcdom
            by (eapply Subtype_tArrow_cdom; eauto).
        (* the arg type is a subtype of the domain *)
        assert (Subtype t2 tStr) as Hdom
            by (eapply Subtype_tArrow_dom; eauto).
        clear Hopsub.
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert (exists s, v = vConst (cStr s)) as Hstr
            by (eapply TypeOf_tStr; eapply TypeOf_Sub_type; eauto).
        destruct Hstr as [s Hs].
        subst.
        match goal with
        | [ H : Some (vConst (cNat _)) = Some _ |- _]
          => inversion H; subst
        end.
        assert (Subtype tStr t2) as Ht2low by
              (eapply TypeOfVal_lower_bound; eauto).
        assert (TypeOfVal (vOp opStrLen) t1) as Hval1 by crush.
        assert (TypeOfVal (vStr s) t2) as Hval2 by crush.
        assert (((vNat (String.length s)) <> (vBool false)
                 /\ TypeOfVal (vStr s) tpos)
                \/ ((vNat (String.length s)) = (vBool false)
                    /\ TypeOfVal (vStr s) tneg))
          as Hres.
        {
          eapply pred_inv_props; try eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
        {
          assert (~ IsEmpty tpos) as Hnmt
              by (eapply TypeOfVal_NonEmpty; eauto).
          eapply T_Subsume. apply T_Const. simpl. apply Subres_refl.
          crush. crush.
          apply SR_Sub...
          ifcase. apply P_Absurd... ifcase; crush.
          ifcase...
          assert (IsEmpty (tAnd tNat tFalse)) by (apply Empty_neq_tBase; crush).
          repeat ifcase... repeat ifcase...
        }
        {
          inversion Heq.
        }
      }
      { (* opNot *)
        assert (Subtype (op_type opNot) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (predicate tFalse) (tArrow t2 t)) as Hopsub
            by (eapply Subtype_trans; eassumption).
        (* the result is a supertype of the op result *)
        assert (Subtype tBool t) as Hcdom.
        {
          eapply tArrow_R_cdom_sub. eassumption.
          apply codomain_predicate.
        }
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert ((v' = (vConst (cBool true))) \/ (v' = (vConst (cBool false))))
          as Hvoptions.
        {
          destruct v;
          try match goal with
              | [ H : TypeOf _ (eVal (vConst ?c)) _ |- _] => destruct c
              end;
          try match goal with
              | [ H : (if ?b then Some _ else Some _) = Some _ |- _]
                => destruct b
              end;
          try match goal with
              | [ H : Some (vConst (cBool _)) = Some _ |- _]
                => inversion H; crush
              end.
        }
        assert (TypeOfVal (vOp opNot) t1) as Hval1 by crush.
        assert (TypeOfVal v t2) as Hval2 by crush.
        assert ((v' <> (vBool false) /\ TypeOfVal v tpos)
                \/ (v' = (vBool false) /\ TypeOfVal v tneg))
          as Hres.
        {
          eapply pred_inv_props. eassumption. eassumption.
          eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hvoptions; subst.
        { (* v' = vConst (cBool true) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert (~ IsEmpty tpos) as Hpos
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl.
            crush. crush.
            apply SR_Sub...
            assert (Subtype tTrue tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            assert (IsEmpty (tAnd tTrue tFalse)) as Hmt
                by (apply Empty_neq_tBase; crush).
            ifcase... apply P_Absurd... ifcase; crush.
            repeat ifcase...
          }
          {
            inversion Heq.
          }
        }
        { (* v' = vConst (cBool false) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert False as impossible by (apply Hneq; reflexivity).
            contradiction.
          }
          {
            assert (~ IsEmpty tneg) as Hneg
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush.
            apply SR_Sub...
            assert (Subtype tFalse tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            destruct (empty_dec tneg)...
            repeat ifcase...
          }
        }
      }
      { (* opIsNat *)
        assert (Subtype (op_type opIsNat) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (predicate tNat) (tArrow t2 t)) as Hopsub
            by (eapply Subtype_trans; eassumption).
        (* the result is a supertype of the op result *)
        assert (Subtype tBool t) as Hcdom.
        {
          eapply tArrow_R_cdom_sub. eassumption.
          apply codomain_predicate.
        }
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert ((v' = (vConst (cBool true))) \/ (v' = (vConst (cBool false))))
          as Hvoptions.
        {
          destruct v;
          try match goal with
              | [ H : TypeOf _ (eVal (vConst ?c)) _ |- _] => destruct c
              end;
          try match goal with
              | [ H : (if ?b then Some _ else Some _) = Some _ |- _]
                => destruct b
              end;
          try match goal with
              | [ H : Some (vConst (cBool _)) = Some _ |- _]
                => inversion H; crush
              end.
        }
        assert (TypeOfVal (vOp opIsNat) t1) as Hval1 by crush.
        assert (TypeOfVal v t2) as Hval2 by crush.
        assert ((v' <> (vBool false) /\ TypeOfVal v tpos)
                \/ (v' = (vBool false) /\ TypeOfVal v tneg))
          as Hres.
        {
          eapply pred_inv_props. eassumption. eassumption.
          eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hvoptions; subst.
        { (* v' = vConst (cBool true) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert (~ IsEmpty tpos) as Hpos
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tTrue tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            assert (IsEmpty (tAnd tTrue tFalse)) as Hmt
                by (apply Empty_neq_tBase; crush).
            ifcase... apply P_Absurd... ifcase; crush.
            repeat ifcase...
          }
          {
            inversion Heq.
          }
        }
        { (* v' = vConst (cBool false) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert False as impossible by (apply Hneq; reflexivity).
            contradiction.
          }
          {
            assert (~ IsEmpty tneg) as Hneg
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tFalse tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            destruct (empty_dec tneg)...
            repeat ifcase...
          }
        }
      }
      { (* opIsStr *)
        assert (Subtype (op_type opIsStr) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (predicate tStr) (tArrow t2 t)) as Hopsub
            by (eapply Subtype_trans; eassumption).
        (* the result is a supertype of the op result *)
        assert (Subtype tBool t) as Hcdom.
        {
          eapply tArrow_R_cdom_sub. eassumption.
          apply codomain_predicate.
        }
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert ((v' = (vConst (cBool true))) \/ (v' = (vConst (cBool false))))
          as Hvoptions.
        {
          destruct v;
          try match goal with
              | [ H : TypeOf _ (eVal (vConst ?c)) _ |- _] => destruct c
              end;
          try match goal with
              | [ H : (if ?b then Some _ else Some _) = Some _ |- _]
                => destruct b
              end;
          try match goal with
              | [ H : Some (vConst (cBool _)) = Some _ |- _]
                => inversion H; crush
              end.
        }
        assert (TypeOfVal (vOp opIsStr) t1) as Hval1 by crush.
        assert (TypeOfVal v t2) as Hval2 by crush.
        assert ((v' <> (vBool false) /\ TypeOfVal v tpos)
                \/ (v' = (vBool false) /\ TypeOfVal v tneg))
          as Hres.
        {
          eapply pred_inv_props. eassumption. eassumption.
          eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hvoptions; subst.
        { (* v' = vConst (cBool true) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert (~ IsEmpty tpos) as Hpos
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tTrue tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            assert (IsEmpty (tAnd tTrue tFalse)) as Hmt
                by (apply Empty_neq_tBase; crush).
            ifcase... apply P_Absurd... ifcase; crush.
            repeat ifcase...
          }
          {
            inversion Heq.
          }
        }
        { (* v' = vConst (cBool false) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert False as impossible by (apply Hneq; reflexivity).
            contradiction.
          }
          {
            assert (~ IsEmpty tneg) as Hneg
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tFalse tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            destruct (empty_dec tneg)...
            repeat ifcase...
          }
        }
      }
      { (* opIsProc *)
        assert (Subtype (op_type opIsProc) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (predicate (tArrow tEmpty tAny)) (tArrow t2 t))
          as Hopsub by (eapply Subtype_trans; eassumption).
        (* the result is a supertype of the op result *)
        assert (Subtype tBool t) as Hcdom.
        {
          eapply tArrow_R_cdom_sub. eassumption.
          apply codomain_predicate.
        }
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert ((v' = (vConst (cBool true))) \/ (v' = (vConst (cBool false))))
          as Hvoptions.
        {
          destruct v;
          try match goal with
              | [ H : TypeOf _ (eVal (vConst ?c)) _ |- _] => destruct c
              end;
          try match goal with
              | [ H : (if ?b then Some _ else Some _) = Some _ |- _]
                => destruct b
              end;
          try match goal with
              | [ H : Some (vConst (cBool _)) = Some _ |- _]
                => inversion H; crush
              end.
        }
        assert (TypeOfVal (vOp opIsProc) t1) as Hval1 by crush.
        assert (TypeOfVal v t2) as Hval2 by crush.
        assert ((v' <> (vBool false) /\ TypeOfVal v tpos)
                \/ (v' = (vBool false) /\ TypeOfVal v tneg))
          as Hres.
        {
          eapply pred_inv_props. eassumption. eassumption.
          eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hvoptions; subst.
        { (* v' = vConst (cBool true) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert (~ IsEmpty tpos) as Hpos
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tTrue tBool) as Hsubb by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            assert (IsEmpty (tAnd tTrue tFalse)) as Hmt
                by (apply Empty_neq_tBase; crush).
            ifcase... apply P_Absurd... ifcase; crush.
            repeat ifcase...
          }
          {
            inversion Heq.
          }
        }
        { (* v' = vConst (cBool false) *)
          destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
          {
            assert False as impossible by (apply Hneq; reflexivity).
            contradiction.
          }
          {
            assert (~ IsEmpty tneg) as Hneg
                by (eapply TypeOfVal_NonEmpty; eauto).
            eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
            crush. apply SR_Sub...
            assert (Subtype tFalse tBool) as Hsubbby by (unfold Subtype; crush).
            eapply Subtype_trans; eauto.
            destruct (empty_dec tpos)...
            destruct (empty_dec tneg)...
            repeat ifcase...
          }
        }
      }
      { (* opIsZero *)
        assert (Subtype (op_type opIsZero) t1) as Hopt
            by (eapply TypeOf_Op_Subtype; eauto).
        simpl in *.
        assert (Subtype (tArrow tNat tBool) (tArrow t2 t)) as
            Hopsub by (eapply Subtype_trans; eauto).
        (* the result is a supertype of the op result *)
        assert (Subtype tBool t) as Hcdom
            by (eapply Subtype_tArrow_cdom; eauto).
        (* the arg type is a subtype of the domain *)
        assert (Subtype t2 tNat) as Hdom
            by (eapply Subtype_tArrow_dom; eauto).
        clear Hopsub.
        (* if the arg is a subtype of tNat, it must be a nat *)
        assert (exists n, v = vConst (cNat n)) as Hnat
            by (eapply TypeOf_tNat; eapply TypeOf_Sub_type; eauto).
        destruct Hnat as [n Hn].
        subst.
        assert (exists b, v' = (vConst (cBool b))) as Hbool
            by (destruct n; match goal with
                            | [ H : Some (vConst (cBool ?b)) = Some _ |- _]
                              => exists b; inversion H; crush
                            end).
        destruct Hbool as [b Hb]; subst.
        assert (Subtype tNat t2) as Ht2low by
              (eapply TypeOfVal_lower_bound; eauto).
        assert (TypeOfVal (vOp opIsZero) t1) as Hval1 by crush.
        assert (TypeOfVal (vNat n) t2) as Hval2 by crush.
        assert (((vConst (cBool b)) <> (vBool false)
                 /\ TypeOfVal (vNat n) tpos)
                \/ ((vConst (cBool b)) = (vBool false)
                    /\ TypeOfVal (vNat n) tneg))
          as Hres.
        {
          eapply pred_inv_props; try eassumption.
          eapply S_Cons. eassumption. apply S_Null.
        }
        destruct Hres as [[Hneq Htpos] | [Heq Htneg]].
        {
          assert (~ IsEmpty tpos) as Hnmt
              by (eapply TypeOfVal_NonEmpty; eauto).
          eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
          ifcase... ifcase... ifcase... 
          apply SR_Sub...
          assert (Subtype tTrue tBool) as Hsubb by (unfold Subtype; crush).
          eapply Subtype_trans; eauto.
          ifcase. apply P_Absurd... ifcase; crush.
          ifcase...
          assert (IsEmpty (tAnd tTrue tFalse)) by (apply Empty_neq_tBase; crush).
          repeat ifcase... repeat ifcase...
        }
        {
          inversion Heq; subst.
          assert (~ IsEmpty tneg) as Hnmt
              by (eapply TypeOfVal_NonEmpty; eauto).
          eapply T_Subsume. apply T_Const. simpl. apply Subres_refl...
          crush.
          apply SR_Sub...
          assert (Subtype tFalse tBool) as Hsubb by (unfold Subtype; crush).
          eapply Subtype_trans; eauto.
          ifcase. apply P_Absurd... ifcase; crush.
          ifcase...
          assert (IsEmpty (tAnd tTrue tFalse)) by (apply Empty_neq_tBase; crush).
          repeat ifcase... repeat ifcase...
        }
      }
    }
    { (* vAbs *)
      clear IHHtype1. clear IHHtype2.
      assert (TypeOf [] (eVal (vAbs x i body))
                     (Res (tArrow t2 t) Trivial Trivial oTop))
        as Hfun by (eapply T_Subsume; try eassumption; apply SR_Sub; crush).
      clear Htype1.
      assert (TypeOf [] (eVal v) (Res t2 Trivial Trivial oTop))
        as Harg by assumption. clear Htype2.
      assert (TypeOf [Is x t2] body (Res t Trivial Trivial oTop))
        as Hbody by (eapply TypeOf_tArrow_body; eauto).
      assert (((IsEmpty tpos -> IsEmpty (tAnd t (tNot tFalse)))
               /\
               (IsEmpty tneg -> IsEmpty (tAnd t tFalse))))
        as Hinv by (eapply pred_inv_supertype; eassumption).
      destruct Hinv as [Hinvp Hinvn].
      assert (exists t' p' q' o',
                 TypeOf [] (substitute body x v) (Res t' p' q' o')
                 /\ Subtype t' t
                 /\ Proves [(Is x t2) ; (isa o' (tAnd t' (tNot tFalse))) ; p']
                           (isa oTop tpos)
                 /\ Proves [(Is x t2) ; (isa o' (tAnd t' tFalse)) ; q']
                           (isa oTop tneg)
                 /\ ((oTop = (oVar x) /\ o' = oTop)
                     \/ (oTop <> (oVar x) /\ Subobj [] o' oTop)))
        as Hsub.
      {
        apply Substitution.
        crush.
        eapply T_Subsume. eassumption. apply SR_Sub; crush.
        { (* then proposition *)
          destruct (empty_dec tpos).
          { (* IsEmpty tpos *)
            assert (IsEmpty (tAnd t (tNot tFalse))) by auto.
            ifcase; crush.
          }
          { (* ~ IsEmpty tpos *)
            crush.
          }
        }
        { (* else proposition *)
          destruct (empty_dec tneg).
          { (* IsEmpty tneg *)
            assert (IsEmpty (tAnd t tFalse)) by auto.
            ifcase; crush.
          }
          { (* ~ IsEmpty tpos *)
            crush.
          }
        }
        repeat ifcase...
        crush.
      }
      destruct Hsub as [t' [p' [q' [o' [Htype [Hsub [Hp [Hq Ho]]]]]]]].
      assert (Subobj [] o' oTop) as Ho' by (destruct Ho; crush). clear Ho.
      eapply T_Subsume.
      eassumption.
      assert ((Proves [isa o' (tAnd t' (tNot tFalse)); p'] (isa oTop tpos))
              /\ Proves [isa o' (tAnd t' tFalse); q'] (isa oTop tneg))
        as Hproves.
      {
        assert (TypeOfVal v t2) by crush.
        eapply Proves_lemma1.
        eapply TypeOfVal_NonEmpty; try eassumption.
        eassumption. eassumption.
        eassumption. assumption.
      }
      destruct Hproves as [Hp' Hq'].
      eapply SR_Sub.
      eapply TypeOf_WellFormedRes. eassumption.
      assumption. assumption.
      assumption. assumption.
      crush. repeat ifcase...
    }
    assumption.
  }
  { (* T_If *)
    (* BOOKMARK *)
  }
  { (* T_Let *)
    
  }
  { (* T_ExFalso *)
    
  }
  


(* ARCHIVE // OLD *)
