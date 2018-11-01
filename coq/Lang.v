
Require Import CpdtTactics.
Require Import Bool.
Require Import Nat.
Require Import String.
Require Import Ensembles.
Require Import Classical_sets.
Require Import List.
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
| vAbs : var -> interface -> var -> exp -> val.
  
  
Hint Constructors exp.

Notation "(vNat n )"  := (vConst (cNat n)).
Notation "(vStr s )"  := (vConst (cStr s)).
Notation "(vBool b )" := (vConst (cBool b)).
Notation "(vOp o )"   := (vConst (cOp o)).
         
Inductive obj : Set :=
  oTop  : obj
| oBot  : obj
| oVar : var -> obj.
Hint Constructors obj.

Inductive prop : Set :=
  Trivial : prop
| Absurd  : prop
| And     : prop -> prop -> prop
| Or      : prop -> prop -> prop
| Is      : var -> ty -> prop
| Eq      : var -> var -> prop.
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
  | oBot => []
  end.
Hint Unfold fvsO.


Fixpoint fvsP (p:prop) : list var :=
  match p with
  | Trivial => []
  | Absurd => []
  | And p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Or p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Is x t => [x]
  | Eq x y => [x ; y]
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
  | opAdd1   , (vNat n)       => Some (vNat (n + 1))
  | opAdd1   , _              => None
  | opSub1   , (vNat n)       => Some (vNat (n - 1))
  | opSub1   , _              => None
  | opStrLen , (vStr s)       => Some (vNat (String.length s))
  | opStrLen , _              => None
  | opNot    , (vBool false)  => Some (vBool true)
  | opNot    , _              => Some (vBool false)
  | opIsNat  , (vNat _)       => Some (vBool true)
  | opIsNat  , _              => Some (vBool false)
  | opIsStr  , (vStr _)       => Some (vBool true)
  | opIsStr  , _              => Some (vBool false)
  | opIsProc , (vOp _)        => Some (vBool true)
  | opIsProc , (vAbs _ _ _ _) => Some (vBool true)
  | opIsProc , _              => Some (vBool false)
  | opIsZero , (vNat 0)       => Some (vBool true)
  | opIsZero , (vNat _)       => Some (vBool false)
  | opIsZero , _              => None
  end.
Hint Unfold apply_op.

Fixpoint substitute (e:exp) (x:var) (v:val) : exp :=
  match e with
  | eVar y => if var_dec x y then (eVal v) else e
  | (eVal (vConst c)) => e
  | (eVal (vAbs f i y e')) =>
    if var_dec x f then e
    else if var_dec x y then e
         else eVal (vAbs f i y (substitute e' x v))
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
| S_App_Abs : forall f i x body v e',
    e' = substitute (substitute body x v) f (vAbs f i x body) ->
    Step (eApp (eVal (vAbs f i x body)) (eVal v)) e'
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


Lemma Subtype_refl : forall t, Subtype t t.
Proof.
  crush.
Qed.

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
| SO_Bot : forall Γ o,
    incl (fvsO o) (fvs Γ) ->
    Subobj Γ oBot o
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
  inversion H0; crush.
  inversion H; crush.
Qed.


(* (SubstPath z x y z' *)
(* z[x ↦ y] = z' but where the substitution is optional *)
Inductive SubstVar : var -> var -> var -> var -> Prop :=
| SV_Refl : forall z x y,
    SubstVar z x y z
| SV_Swap : forall x y,
    SubstVar x x y y.
Hint Constructors SubstVar.

(* (SubstProp p1 x y p2)  *)
(* p1[x ↦ y] = p2 but where the substitution is optional *)
Inductive SubstProp : prop -> var -> var -> prop -> Prop :=
| SProp_Refl : forall p x y,
    SubstProp p x y p
| SProp_And : forall p1 p2 p1' p2' x y,
    SubstProp p1 x y p1' ->
    SubstProp p2 x y p2' ->
    SubstProp (And p1 p2) x y (And p1' p2')
| SProp_Or : forall p1 p2 p1' p2' x y,
    SubstProp p1 x y p1' ->
    SubstProp p2 x y p2' ->
    SubstProp (Or p1 p2) x y (Or p1' p2')
| SProp_Is : forall z z' x y t1,
    SubstVar z x y z' ->
    SubstProp (Is z t1) x y (Is z' t1)
| SProp_Eq : forall z1 z1' z2 z2' x y,
    SubstVar z1 x y z1' ->
    SubstVar z2 x y z2' ->
    SubstProp (Eq z1 z2) x y (Eq z1' z2').

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
    Proves Γ (Or p1 p2)
| P_Refl : forall Γ x t,
    Proves Γ (Is x t) ->
    Proves Γ (Eq x x)
| P_Subst : forall Γ x y p q,
    Proves Γ (Eq x y) ->
    Proves Γ p ->
    SubstProp p x y q ->
    Proves Γ q.
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
  {
    eapply P_Refl...
  }
  {
    eapply P_Subst.
    apply IHHproves1...
    apply IHHproves2...
    assumption.
  }
Qed.

Lemma SubstProp_fvs : forall p x y q,
    SubstProp p x y q ->
    incl (fvsP q) ([y] ++ (fvsP p)).
Proof.
  intros p x y q Hsubst.
  induction Hsubst.
  {
    apply incl_appr; crush.
  }
  {
    simpl.
    apply incl_app.
    eapply incl_tran. eassumption.
    simpl. rewrite app_comm_cons.
    apply incl_appl. crush.
    eapply incl_tran. eassumption.
    simpl.
    intros z Hz.
    inversion Hz; subst. left; auto.
    right.
    apply in_app_iff. right. assumption.
  }
  {
    simpl.
    apply incl_app.
    eapply incl_tran. eassumption.
    simpl. rewrite app_comm_cons.
    apply incl_appl. crush.
    eapply incl_tran. eassumption.
    simpl.
    intros z Hz.
    inversion Hz; subst. left; auto.
    right.
    apply in_app_iff. right. assumption.        
  }
  {
    inversion H; crush. 
  }
  {
    inversion H; inversion H0; crush.
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
  {
    apply SubstProp_fvs in H.
    eapply incl_tran. eassumption. crush.
  }
Qed.    
  

Definition isa (o:obj) (t:ty) : prop :=
  match o with
  | oVar x => Is x t
  | oTop => if empty_dec t then Absurd else Trivial
  | oBot => Absurd    
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
    apply P_Absurd; destruct o2... ifcase...
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
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) p2 ->
    Proves ((isa o1 (tAnd t1 tFalse))::q1::Γ) q2 ->
    WellFormedRes Γ (Res t2 p2 q2 o2) ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2)
| SR_Absurd : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    WellFormedRes Γ (Res t1 p1 q1 o1) ->
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) Absurd ->
    Proves ((isa o1 (tAnd t1 tFalse))::q1::Γ) Absurd ->
    WellFormedRes Γ (Res t2 p2 q2 o2) ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2)
| SR_False : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    WellFormedRes Γ (Res t1 p1 q1 o1) ->
    Subtype (tAnd t1 tFalse) t2 ->
    Subobj Γ o1 o2 ->
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) Absurd ->
    Proves ((isa o1 (tAnd t1 tFalse))::q1::Γ) q2 ->
    WellFormedRes Γ (Res t2 p2 q2 o2) ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2)
| SR_NonFalse : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    WellFormedRes Γ (Res t1 p1 q1 o1) ->
    Subtype (tAnd t1 (tNot tFalse)) t2 ->
    Subobj Γ o1 o2 ->
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) p2 ->
    Proves ((isa o1 (tAnd t1 tFalse))::q1::Γ) Absurd ->
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
  apply SO_Bot.
  intros x Hx.
  apply H in Hx.
  assert (incl (fvs Γ) (fvs Γ')) as Hincl' by (apply fvs_incl; auto).
  crush.
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
  induction H12; intros R3 H23.  
  { (* SR_Sub *)
    assert (Forall (Proves (isa o1 (tAnd t1 (tNot tFalse)) :: p1 :: Γ))
                   (isa o2 (tAnd t2 (tNot tFalse)) :: p2 :: Γ))
      as Hp1.
    {
      constructor.
      eapply Prove_sub_isa.
      eapply Subobj_Weakening. eassumption.
      repeat apply incl_tl...
      apply Subtype_tAnd_L. eassumption.
      apply P_Atom...
      constructor...
      apply Proves_incl...
    }
    assert (Forall (Proves (isa o1 (tAnd t1 tFalse) :: q1 :: Γ))
                   (isa o2 (tAnd t2 tFalse) :: q2 :: Γ))
      as Hp2.
    {
      constructor.
      eapply Prove_sub_isa.
      eapply Subobj_Weakening. eassumption.
      repeat apply incl_tl...
      apply Subtype_tAnd_L. eassumption.
      apply P_Atom...
      constructor...
      apply Proves_incl...        
    }
    remember (Res t2 p2 q2 o2) as R2.
    induction H23;
      match goal with
      | [ H : Res _ _ _ _ = Res _ _ _ _ |- _ ] =>
        inversion H; subst
      end.
    {
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
    }
    {
      apply SR_Absurd...
      eapply P_Env_Cut. eassumption. assumption.
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      eapply SR_False...
      eapply Subtype_tAnd_LL. eassumption. assumption.
      eapply Subobj_trans. eassumption. assumption.      
      eapply P_Env_Cut. eassumption. assumption.
      eapply P_Env_Cut. eassumption. assumption.      
    }
    {
      apply SR_NonFalse...
      eapply Subtype_tAnd_LL. eassumption. assumption.
      eapply Subobj_trans. eassumption. assumption.      
      eapply P_Env_Cut. eassumption. assumption.
      eapply P_Env_Cut. eassumption. assumption.
    }
  }
  { (* SR_Absurd *)
    remember (Res t2 p2 q2 o2) as R2.
    induction H23; eapply SR_Absurd; crush.
  }
  { (* SR_False *)
    assert (Subtype (tAnd t1 tFalse) (tAnd t2 tFalse)) as Hsub
        by (apply Subtype_tAnd_LFalse; auto).
    assert (Forall (Proves (isa o1 (tAnd t1 tFalse) :: q1 :: Γ))
                   (isa o2 (tAnd t2 tFalse) :: q2 :: Γ))
      as Hp2.
    {
      constructor.
      eapply Prove_sub_isa.
      eapply Subobj_Weakening. eassumption.
      repeat apply incl_tl... eassumption.
      apply P_Atom... 
      constructor...
      apply Proves_incl...        
    }
    remember (Res t2 p2 q2 o2) as R2.
    induction H23;
      match goal with
      | [ H : Res _ _ _ _ = Res _ _ _ _ |- _ ] =>
        inversion H; subst
      end.
    {
      apply SR_False...
      eapply Subtype_trans. eassumption. apply Subtype_L_tAnd. assumption.
      eapply Subobj_trans. eassumption. assumption.
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      apply SR_Absurd...
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      eapply SR_False...
      apply (@Subtype_tAnds_False_trans t1 t2 t3); auto.
      eapply Subobj_trans. eassumption. assumption.      
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      eapply SR_Absurd...
      eapply P_Env_Cut. eassumption. assumption.
    }
  }
  { (* SR_NonFalse *)
    assert (Subtype (tAnd t1 (tNot tFalse)) (tAnd t2 (tNot tFalse)))
      as Hsub by (apply Subtype_tAnd_LNotFalse; auto).
    assert (Forall (Proves (isa o1 (tAnd t1 (tNot tFalse)) :: p1 :: Γ))
                   (isa o2 (tAnd t2 (tNot tFalse)) :: p2 :: Γ))
      as Hp2.
    {
      constructor.
      eapply Prove_sub_isa.
      eapply Subobj_Weakening. eassumption.
      repeat apply incl_tl... eassumption.
      apply P_Atom... 
      constructor...
      apply Proves_incl...        
    }
    remember (Res t2 p2 q2 o2) as R2.
    induction H23;
      match goal with
      | [ H : Res _ _ _ _ = Res _ _ _ _ |- _ ] =>
        inversion H; subst
      end.
    {
      apply SR_NonFalse...
      eapply (@Subtype_trans (tAnd t1 (tNot tFalse)) t2 t3).
      eassumption. assumption.
      eapply Subobj_trans. eassumption. assumption.
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      apply SR_Absurd...
      eapply P_Env_Cut. eassumption. assumption.
    }
    {
      apply SR_Absurd...
      eapply P_Env_Cut. eassumption. assumption.      
    }
    {
      eapply SR_NonFalse...
      apply (@Subtype_trans (tAnd t1 (tNot tFalse))
                            (tAnd t2 (tNot tFalse))
                            t3); auto.
      eapply Subobj_trans. eassumption. assumption.      
      eapply P_Env_Cut. eassumption. assumption.
    }
  }
Qed.  

(*
Lemma Subres_implies_subtype : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    ~ Proves (isa o1 (tAnd t1 (tNot tFalse)) :: p1 :: Γ) Absurd
    \/ ~ Proves (isa o1 (tAnd t1 tFalse) :: q1 :: Γ) Absurd ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2) ->
    Subtype t1 t2.
Proof with crush.
  intros Γ t1 p1 q1 o1 t2 p2 q2 o2 Hp Hsubres.
  inversion Hsubres...
  apply Subtype_L_tAnd.
Qed.
*)

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


Definition objOr (o1 o2:obj) : obj :=
  match o1 , o2 with
  | o1 , oBot => o1
  | oBot , o2 => o2
  | _, _ => if obj_dec o1 o2
            then o1
            else oTop
  end.
Hint Unfold objOr.

Definition tresOr (r1 r2:tres) : tres :=
  match r1, r2 with
  | (Res t1 p1 q1 o1), (Res t2 p2 q2 o2) =>
    (Res (tOr t1 t2) (Or p1 p2) (Or q1 q2) (objOr o1 o2))
  end.
Hint Unfold tresOr.

Definition alias (x : var) (R:tres) : prop :=
  match R with
  | (Res _ _ _ oBot) => Absurd
  | (Res _ _ _ (oVar y)) => Eq x y
  | (Res t p q oTop) =>
    let p' := And p (Is x (tAnd t (tNot tFalse))) in
    let q' := And q (Is x (tAnd t tFalse)) in
    And (Is x t) (Or p' q')
  end.
Hint Unfold alias.


Axiom pred_inv : ty -> ty -> (ty * ty).
(* Metafunction to determine what types a function
   is a predicate for. In another module we formally
   define and prove properties about such an algorithm.
   For this module, we just keep this abstract.  *)


Inductive TypeOf : gamma -> exp -> tres -> Prop :=
| T_Var : forall Γ x y t R,
    Proves Γ (Eq x y) ->
    Proves Γ (Is y t) ->
    Subres Γ
           (Res t
                (Is y (tAnd t (tNot tFalse)))
                (Is y (tAnd t tFalse))
                (oVar y))
           R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVar x) R 
| T_Const : forall Γ c R,
    Subres Γ (const_tres c) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVal (vConst c)) R
| T_Abs : forall Γ f i i' x e t R,
    x <> f ->
    ~ In x (fvs Γ) ->
    ~ In f (fvs Γ) ->
    t = (tAnd (interface_ty i) (neg_interface_ty i')) ->
    ~ IsEmpty t ->
    (forall t1 t2,
        InInterface t1 t2 i ->
        TypeOf ((Is x t1)::(Is f t)::Γ)
               e
               (Res t2 Trivial Trivial oTop)) ->
    Subres Γ (Res t Trivial Absurd oTop) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eVal (vAbs f i x e)) R
| T_App : forall Γ e1 e2 t1 t2 o2 t tpos tneg R,
    TypeOf Γ e1 (Res t1 Trivial Trivial oTop) ->
    TypeOf Γ e2 (Res t2 Trivial Trivial o2) ->
    Subtype t1 (tArrow t2 t) ->
    pred_inv t1 t2 = (tpos , tneg) ->
    Subres Γ (Res t (isa o2 tpos) (isa o2 tneg) oTop) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eApp e1 e2) R
| T_If : forall Γ e1 e2 e3 t1 R2 R3 p1 q1 o1 R,
    TypeOf Γ e1 (Res t1 p1 q1 o1) ->
    TypeOf ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) e2 R2 ->
    TypeOf ((isa o1 (tAnd t1 tFalse))::q1::Γ) e3 R3 ->
    Subres Γ (tresOr R2 R3) R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eIf e1 e2 e3) R
| T_Let : forall Γ x e1 e2 R1 R2 R,
    ~ In x (fvs Γ) ->
    TypeOf Γ e1 R1 ->
    TypeOf ((alias x R1)::Γ) e2 R2 ->
    Subres Γ R2 R ->
    WellFormedRes Γ R ->
    TypeOf Γ (eLet x e1 e2) R
| T_ExFalso : forall Γ e t p q o,
    Proves Γ Absurd ->
    WellFormedRes Γ (Res t p q o) ->
    TypeOf Γ e (Res t p q o).
Hint Constructors TypeOf.

Inductive TypeOfVal : val -> ty -> Prop :=
| TOV : forall v t,
    TypeOf [] (eVal v) (Res t Trivial Trivial oTop) ->
    TypeOfVal v t.


(* See Inv.v for details/proofs/etc about function inversion. *)
Axiom pred_inv_props : forall funty argty tpos tneg,
    pred_inv funty argty = (tpos, tneg) ->
    forall v1 v2 v3,
      TypeOfVal v1 funty ->
      TypeOfVal v2 argty ->
      Steps (eApp (eVal v1) (eVal v2)) (eVal v3) ->
      (v3 <> (vBool false) /\ TypeOfVal v2 tpos)
      \/
      (v3 = (vBool false) /\ TypeOfVal v2 tneg).

Axiom pred_inv_tNat_tNat :
  pred_inv (tArrow tNat tNat) tNat = (tNat, tEmpty).
Axiom pred_inv_tStr_tNat :
  pred_inv (tArrow tStr tNat) tStr = (tStr, tEmpty).
Axiom pred_inv_tNat_tBool :
  pred_inv (tArrow tNat tBool) tNat = (tNat, tNat).
Axiom pred_inv_tFalse_predicate :
  pred_inv (predicate tFalse) tAny = (tFalse, (tNot tFalse)).
Axiom pred_inv_tNat_predicate :
  pred_inv (predicate tNat) tAny = (tNat, (tNot tNat)).
Axiom pred_inv_tStr_predicate :
  pred_inv (predicate tStr) tAny = (tStr, (tNot tStr)).
Axiom pred_inv_tProc_predicate :
  pred_inv (predicate (tArrow tEmpty tAny)) tAny
  = ((tArrow tEmpty tAny), (tNot (tArrow tEmpty tAny))).

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
    \/ (exists f i x e, v = (vAbs f i x e)).
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
    TypeOf [] (eVal (vOpo)) (Res t1 Trivial Trivial oTop) ->
    pred_inv t1 t2 = (tpos, tneg) ->
    WellFormedRes [] R ->
    Subres [] (Res t (isa o2 tpos) (isa o2 tneg) oTop) R ->
    Subtype (op_type o) (tArrow t2 t) ->
    (exists e' : exp, Step (eApp (eVal (vOpo)) (eVal v2)) e').
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
    assert (incl (fvsP (Eq x y)) (fvs [])) as Hcrazy.
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
    left. exists (vAbs f i x e). reflexivity.
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
      assert ((exists o : op, v1 = (vOpo))
              \/ (exists f i x e, v1 = vAbs f i x e))
        as Hv1opts.
      {
        eapply TypeOf_arrow_val. eassumption. eassumption.
      }
      destruct Hv1opts as [[o Ho] | [f [i [x [e Habs]]]]]; subst.
      { 
        eapply Progress_App_op; eauto.
        eapply Subtype_trans.
        eapply TypeOf_Op_Subtype. eassumption. assumption.
      }
      { (* (vAbs f i x e) *)
        exists (substitute (substitute e x v2) f (vAbs f i x e)).
        constructor. reflexivity.
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
      subst.
      right. exists e3. apply S_If_False.
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
  {
    intuition.
    {
      match goal with
      | [H : (exists _, _ = eVal _) |- _]
        =>  destruct H as [v1 Hv1]
      end.
      subst.
      right. exists (substitute e2 x v1).
      apply S_Let...
    }
    {
      match goal with
      | [H : (exists _, Step _ _) |- _]
        =>  destruct H as [e1' Hstep1]
      end.
      right. exists (eLet x e1' e2). apply S_Let_Cong...
    }
  }
  {
    remember Proves_sound. crush.
  }
Qed.
  



Lemma Typeof_type_subsume : forall Γ e t p q o t',
    ~ Proves Γ Absurd ->
    TypeOf Γ e (Res t p q o) ->
    Subtype t t' ->
    TypeOf Γ e (Res t' p q o).
Proof with crush.
  intros Γ e t p q o t' Hsound Htype Hsub.
  remember (Res t p q o) as R.
  inversion Htype; subst.
  { (* eVar *)
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_Var... eassumption. eassumption.
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
    applyH. assumption.
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
    eapply T_If...
    eassumption. eassumption. eassumption.
    eapply Subres_trans... eassumption.
    apply SR_Sub...
  }
  {
    assert (WellFormedRes Γ (Res t' p q o)) as Hwfr
        by match goal with
           | [ H : WellFormedRes _ _ |- _]
             => inversion H; crush
           end.
    eapply T_Let...
    eassumption. eassumption. 
    eapply Subres_trans... eassumption.
    apply SR_Sub...
  }
  {
    contradiction.
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

Lemma Preservation : forall e e' R,
    TypeOf [] e R ->
    SimpleRes R ->
    Step e e' ->
    exists R', TypeOf [] e' R'
               /\ SimpleRes R'
               /\ Subres [] R' R.
Proof with crush.
  intros e e' R Htype.  
  generalize dependent e'.
  remember [] as Γ.
  induction Htype;
    intros e' Hsimp Hstep;
    try solve[inversion Hstep].
  { (* T_App *)
    subst.
    assert (o2 = oTop) as Ho2 by (eapply TypeOf_oTop; eassumption).
    inversion Hstep; subst.
    { (* (e1 e2) --> (e1' e2) *)
      assert (exists R' : tres,
                 TypeOf [] e1' R'
                 /\ SimpleRes R'
                 /\ Subres [] R' (Res t1 Trivial Trivial oTop))
        as IH1 by crush.
      destruct IH1 as [[t1' p1' q1' o1'] [Htype1' [Hsimp1' HSR1']]].
      subst.
      exists (Res t (isa oTop tpos) (isa oTop tneg) oTop).
      split. eapply T_App. eapply T_Subsume. eassumption. eassumption.
      eassumption. eassumption. eassumption. apply Subres_refl.
      apply SimpleRes_WellFormedRes...
      repeat ifcase; crush. repeat ifcase; crush.
      constructor; crush. repeat ifcase; crush.
      split... repeat ifcase; crush.
    }
    { (* (v e2) --> (v e2') *)
      assert (exists R' : tres,
                 TypeOf [] e2' R'
                 /\ SimpleRes R'
                 /\ Subres [] R' (Res t2 Trivial Trivial oTop))
        as IH2 by crush.
      destruct IH2 as [[t2' p2' q2' o2'] [Htype2' [Hsimp2' HSR2']]].
      exists (Res t (isa oTop tpos) (isa oTop tneg) oTop).
      split. eapply T_App. eassumption.
      eapply T_Subsume. eassumption. eassumption.
      eassumption. eassumption. apply Subres_refl.
      apply SimpleRes_WellFormedRes...
      repeat ifcase; crush. repeat ifcase; crush.
      constructor; crush. repeat ifcase; crush.
      split... repeat ifcase; crush.
    }
    { (* (o v) --> v'   where Some v' = apply_op o v *)
      (* BOOKMARK *)
    }
    { (* ? *)
    }
  }
  { (* T_If *)
    
  }
  { (* T_Let *)
    
  }
  { (* T_ExFalso *)
    
  }
  


(* ARCHIVE // OLD *)
