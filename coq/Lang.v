
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
| S_If_Let_Cong : forall x e1 e1' e2,
    Step e1 e1' ->
    Step (eLet x e1 e2) (eLet x e1' e2)
| S_If_Let : forall x v e,
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


Axiom Pred : ty -> ty -> ty -> ty -> Prop.
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
    Pred t1 t2 tpos tneg ->
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
Axiom Pred_def : forall funty argty tpos tneg,
    Pred funty argty tpos tneg ->
    forall v1 v2 v3,
      TypeOfVal v1 funty ->
      TypeOfVal v2 argty ->
      Steps (eApp (eVal v1) (eVal v2)) (eVal v3) ->
      (v3 <> (vBool false) /\ TypeOfVal v2 tpos)
      \/
      (v3 = (vBool false) /\ TypeOfVal v2 tneg).

Lemma Pred_pos_arg : forall t1 t2 tpos tneg,
    Pred t1 t2 tpos tneg ->
    Subtype tpos t2.
Proof.
Admitted.

Lemma Pred_neg_arg : forall t1 t2 tpos tneg,
    Pred t1 t2 tpos tneg ->
    Subtype tneg t2.
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

Lemma TypeOf_Op_Subtype : forall Γ o t1 t2 t,
    TypeOf Γ (eVal (vOp o)) (Res t1 Trivial Trivial oTop) ->
    Subtype t1 (tArrow t2 t) ->
    Subtype (op_type o) (tArrow t2 t).
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

Lemma TypeOf_tStr : forall Γ v p q o,
    TypeOf Γ (eVal v) (Res tNat p q o) ->
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
  
Lemma Progress : forall Γ e R,
    Γ = [] ->
    TypeOf Γ e R ->
    (exists v, e = (eVal v))
    \/
    (exists e', Step e e' /\ (exists  R', TypeOf Γ e' R' /\ Subres Γ R' R)).
Proof.
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
      destruct Hv1opts as [[o Ho] | f [i [x [e H]]]]; subst.
      {
        assert (Subtype (op_type o) (tArrow t2 t)) as Harrow.
        {
          eapply TypeOf_Op_Subtype. eassumption. eassumption.
        }
        destruct o; simpl in *.
        assert (Subtype t2 tNat) as Ht2.
        {
          eapply Subtype_tArrow_dom. eassumption.
        }
        assert (Subtype tNat t) as Ht.
        {
          eapply Subtype_tArrow_cdom. eassumption.
        }
        assert (TypeOf [] (eVal v2) (Res tNat Trivial Trivial o2)) as Hv2Nat.
        {
          eapply TypeOf_Sub_type; eassumption.
        }
        apply TypeOf_tNat in Hv2Nat.
        destruct Hv2Nat as [n Hn]. subst.
        exists (eVal (vNat (n + 1))). split.
        apply S_App_Op. simpl. reflexivity.
        exists (Res t Trivial Absurd oTop). split.
        apply T_Const. simpl.
        apply SR_Sub; auto.
        assert (IsEmpty (tAnd tNat tFalse)) as Hempty.
        {
          apply Empty_neq_tBase. crush.
        }
        unfold isa. ifcase.
        apply P_Atom. left; auto.
        contradiction.
        constructor. simpl. crush.
        assert (Subtype tneg tNat) as Hneg.
        {
          assert (Subtype tneg t2) as Htneg2
              by (eapply Pred_neg_arg; eassumption).
          eapply Subtype_trans; eauto.
        }
        
        (* BOOKMARK *)
      }      
      {
        
      }
      {
        
      }      

      (*
        Lemma TypeOf_Op_Subtype : forall Γ o t1 t2 t,
        TypeOf Γ (eVal (vOp o)) (Res t1 Trivial Trivial oTop) ->
        Subtype t1 (tArrow t2 t) ->
        Subtype (op_type o) (tArrow t2 t).
        Proof.
        Admitted.
       *)
      
      assert (TypeOf [] (eVal v1) (Res (tArrow t2 t) Trivial Trivial oTop))
        as Htype1'.
      {
        eapply TypeOf_Const_Subtype. eassumption. eassumption.
      }
      clear Htype1.

      
    }
    {
      
    }
    {
      
    }
    {
      
    }
    
    
  }
  {
  }
  {
  }
  {
  }
  
  
Lemma Preservation : forall Γ e e' R R',
    Γ = [] ->
    TypeOf Γ e R ->
    Step e e' ->
    TypeOf Γ e' R' /\ Subres Γ R' R.


(* ARCHIVE // OLD *)


Ltac same_rVal :=
  match goal with
  | [H : rVal _ = rVal _ |- _] => inversion H; subst
  end.

Inductive Sat : rho -> prop -> Prop :=
| M_Trivial : forall r,
    Sat r Trivial
| M_And : forall p q r,
    Sat r p ->
    Sat r q ->
    Sat r (And p q)
| M_Or_L : forall p q r,
    Sat r p ->
    Sat r (Or p q)
| M_Or_R : forall p q r,
    Sat r q ->
    Sat r (Or p q)
| M_Is : forall π t r v,
    path_lookup r π = rVal v ->
    TypeOfVal v t ->
    Sat r (Is π t)
| M_Eq : forall π1 π2 v r,
    path_lookup r π1 = rVal v ->
    path_lookup r π2 = rVal v ->
    Sat r (Eq π1 π2)

with
TypeOfVal : val -> ty -> Prop :=
| TOV_Const : forall c t,
    Subtype (const_type c) t ->
    TypeOfVal (vConst c) t
| TOV_Pair : forall v1 v2 t1 t2 t,
    TypeOfVal v1 t1 ->
    TypeOfVal v2 t2 ->
    Subtype (tProd t1 t2) t ->
    TypeOfVal (vPair v1 v2) t
| TOV_Clos : forall r f i i' x e t funt Γ,
    f <> x ->
    ~ In f (fvs Γ) ->
    ~ In x (fvs Γ) ->
    t = (tAnd (interface_ty i) (neg_interface_ty i')) ->
    ~ IsEmpty t ->
    Forall (Sat r) Γ ->
    (forall t1 t2,
        InInterface t1 t2 i ->
        TypeOf ((Is (pVar x) t1)::(Is (pVar f) t)::Γ)
               e
               (Res t2 Trivial Trivial oTop)) ->
    Subtype t funt ->
    TypeOfVal (vClos r f i x e) funt.      
Hint Constructors Sat TypeOfVal.


Inductive ApplyVal : val -> val -> result -> Prop :=
| Apply_Op : forall o v res,
    apply_op o v = res ->
    ApplyVal (vOp o) v res
| Apply_Error : forall r f i x e v,
    (exists n, ValOf n (rhoCons x v (rhoCons f (vClos r f i x e) r))
                     e
                     rError) ->
    ApplyVal (vClos r f i x e) v rError
| Apply_Stuck : forall r f i x e v,
    (exists n, ValOf n (rhoCons x v (rhoCons f (vClos r f i x e) r))
                     e
                     rStuck) ->
    ApplyVal (vClos r f i x e) v rStuck
| Apply_Val : forall r f i x e v,
    (exists n v, ValOf n (rhoCons x v (rhoCons f (vClos r f i x e) r))
                       e
                       (rVal v)) ->
    ApplyVal (vClos r f i x e) v rStuck
| Apply_Timeout : forall r f i x e v,
    (forall n, ValOf n (rhoCons x v (rhoCons f (vClos r f i x e) r))
                     e
                     rTimeout) ->
    ApplyVal (vClos r f i x e) v rTimeout.
Hint Constructors ApplyVal.

Inductive IsProc : val -> Prop :=
| IP_Op : forall o, IsProc (vOp o)
| IP_Clos : forall r f i x e, IsProc (vClos r f i x e).
Hint Constructors IsProc.

Inductive ValMaps : val -> ty -> ty -> Prop :=
| Maps : forall v t1 t2,
    IsProc v ->
    (forall v1,
        TypeOfVal v1 t1 ->
        ApplyVal v v1 rTimeout
        \/ ApplyVal v v1 rError
        \/ (exists v2, ApplyVal v v1 (rVal v2)
                       /\ TypeOfVal v2 t2)) ->
    ValMaps v t1 t2.
Hint Constructors ValMaps.

Axiom interp_tArrow_exists : forall (t1 t2:ty) (v:val),
    v ∈ (tInterp (tArrow t1 t2)) ->
    ValMaps v t1 t2.
Axiom interp_tArrow_full : forall (v:val) (t1 t2:ty),
    ValMaps v t1 t2 ->
    v ∈ (tInterp (tArrow t1 t2)).

Axiom Pred_def : forall funty argty tpos tneg,
    Pred funty argty tpos tneg ->
    forall v1 v2 v3,
      TypeOfVal v1 funty ->
      TypeOfVal v2 argty ->
      ApplyVal v1 v2 (rVal v3) ->
      (v3 <> (vBool false) /\ TypeOfVal v2 tpos)
      \/
      (v3 = (vBool false) /\ TypeOfVal v2 tneg).



Lemma SubstPath_lookup_eq : forall r π1 π1' π π' v,
    SubstPath π1 π π' π1' ->
    path_lookup r π = rVal v ->
    path_lookup r π' = rVal v ->
    path_lookup r π1 = path_lookup r π1'.
Proof.
  intros r π1 π1' π π' v Hsub.
  generalize dependent r.
  induction Hsub; crush.
Qed.  
  
Lemma Sat_transport : forall r p π π' q,
    SubstProp p π π' q ->
    Sat r p ->
    Sat r (Eq π π') ->
    Sat r q.
Proof.
  intros r p π π' q Hsubst.
  generalize dependent r.
  induction Hsubst.
  {
    (* SProp_Refl *)
    crush.
  }
  {
    (* SProp_And *)
    intros r Hand Heq.
    inversion Hand; crush.
  }
  {
    (* SProp_Or *)
    intros r Hor Heq.
    inversion Hor; crush.
  }
  {
    (* SProp_Is *)
    intros r His Heq.
    inversion Heq; subst.
    inversion His; subst.
    assert (path_lookup r π1 = path_lookup r π1') as Heq1
        by (eapply SubstPath_lookup_eq; eassumption).
    assert (path_lookup r π1' = rVal v0) as Heq0 by crush.
    econstructor; eauto.
  }
  {
    (* SProp_Eq *)
    intros r Heq Heq'.
    inversion Heq; subst.
    inversion Heq'; subst.
    assert (path_lookup r π1 = path_lookup r π1') as Heq1
        by (eapply SubstPath_lookup_eq; eassumption).
    assert (path_lookup r π1' = rVal v) as Heq1' by crush.
    assert (path_lookup r π2 = path_lookup r π2') as Heq2
        by (eapply SubstPath_lookup_eq; eassumption).
    assert (path_lookup r π2' = rVal v) as Heq2' by crush.
    econstructor; eauto.
  }
Qed.  

Lemma TOV_Sub : forall v t t',
    TypeOfVal v t ->
    Subtype t t' ->
    TypeOfVal v t'.
Proof.
Admitted.

Lemma Subtype_tAnd_R : forall t t1 t2,
    Subtype t t1 ->
    Subtype t t2 ->
    Subtype t (tAnd t1 t2).
Proof.
  intros.
  unfold Subtype in *.
  crush.
Qed.

Lemma Subtype_tAnd_L : forall t1 t2 t,
    Subtype t1 t ->
    Subtype t2 t ->
    Subtype (tAnd t1 t2) t.
Proof.
Admitted.

Lemma Subtype_tProd_And : forall t1 t2 t1' t2' t t',
    Subtype (tProd t1 t2) t ->
    Subtype (tProd t1' t2') t' ->
    Subtype (tProd (tAnd t1 t1') (tAnd t2 t2')) (tAnd t t').
Proof.
Admitted.
(* TODO this should be a fairly straightforward proof *)

Lemma non_IsEmpty_interface_combine_neg : forall i i' i'',
    ~ IsEmpty (tAnd (interface_ty i) (neg_interface_ty i')) ->
    ~ IsEmpty (tAnd (interface_ty i) (neg_interface_ty i'')) ->
    ~ IsEmpty (tAnd (interface_ty i) (neg_interface_ty (i' ++ i''))).
Proof.
Admitted.
(* Justification: if you look at the emptiness algorithm, a
   single negative arrow must refute the combination of the
   positive ones, thus if none of the negative arrows in i'
   and i'' made i a contradiction before, they cannot
   together since they are just the sum of their parts. *)

Lemma TypeOf_env_weakening : forall Γ Γ' e R,
    Forall (Proves Γ') Γ ->
    TypeOf Γ e R ->
    TypeOf Γ' e R.
Proof.
Admitted.
(* TODO should be straightforward *)

Lemma neg_interface_ty_app : forall i i',
    neg_interface_ty (i ++ i') =
    tAnd (neg_interface_ty i) (neg_interface_ty i').
Proof.
Admitted. (* Obvious *)

Lemma no_fvs_app : forall v Γ Γ',
    ~ In v (fvs Γ) ->
    ~ In v (fvs Γ') ->
    ~ In v (fvs (Γ ++ Γ')).
Proof.
Admitted.

Lemma Sat_app : forall r Γ Γ',
    Forall (Sat r) Γ ->
    Forall (Sat r) Γ' ->
    Forall (Sat r) (Γ ++ Γ').
Proof.
Admitted.  

Lemma Proves_I_am_lazy : forall v0 t v i i' i'0 Γ Γ0,
    Forall
      (Proves
         (Is (pVar v0) t
             :: Is (pVar v)
             (tAnd (interface_ty i) (neg_interface_ty (i' ++ i'0)))
             :: Γ ++ Γ0))
      (Is (pVar v0) t
          :: Is (pVar v) (tAnd (interface_ty i) (neg_interface_ty i'0)) :: Γ0).
Proof.
Admitted.

Lemma IsEmpty_no_vals : forall v t,
    IsEmpty t ->
  ~ TypeOfVal v t.
Proof.
Admitted.  

Lemma TOV_And : forall v t1 t2,
    TypeOfVal v t1 ->
    TypeOfVal v t2 ->
    TypeOfVal v (tAnd t1 t2).
Proof.
  intros v.
  induction v.
  {
    intros t1 t2 H1 H2.
    constructor.
    inversion H1. inversion H2. subst.
    apply Subtype_tAnd_R; auto.
  }
  {
    intros t1 t2 H1 H2.
    inversion H1. inversion H2. subst.
    assert (TypeOfVal v1 (tAnd t0 t4)) as H1And by crush.
    assert (TypeOfVal v2 (tAnd t3 t5)) as H2And by crush.
    apply (TOV_Pair H1And H2And).
    apply Subtype_tProd_And; auto.
  }
  {
    intros t1 t2 H1 H2.
    inversion H1.
    inversion H2.
    subst.
    assert (v <> v0) as Hneq by assumption.
    assert (~ In v (fvs (Γ ++ Γ0))) as Hnov
        by (apply no_fvs_app; auto).
    assert (~ In v0 (fvs (Γ ++ Γ0))) as Hnov0
        by (apply no_fvs_app; auto).
    eapply TOV_Clos.
    assumption.
    exact Hnov.
    exact Hnov0.
    reflexivity.
    apply (non_IsEmpty_interface_combine_neg i i' i'0); assumption.
    apply Sat_app; assumption.
    intros t t' HIn.
    assert
      (TypeOf
         (Is (pVar v0) t
             :: Is (pVar v) (tAnd (interface_ty i) (neg_interface_ty i'0))
             :: Γ0) e (Res t' Trivial Trivial oTop)) as Hfun by auto.
    eapply (TypeOf_env_weakening _ Hfun).
    rewrite neg_interface_ty_app.
    unfold Subtype in *.
    unfold Included in *.
    intros x Hx. repeat rewrite interp_tAnd in *.
    split. applyH.
    inversion Hx; subst.
    split. auto. inversion H0; subst. auto.
    applyH.
    inversion Hx; subst.
    split. auto. inversion H0; subst. auto.
    Unshelve.
    apply Proves_I_am_lazy.
  }
Qed.

Inductive WellFormedRho : rho -> Prop :=
| WFR_Nil : WellFormedRho rhoNull
| WFR_Cons : forall x v r,
    WellFormedRho r ->
    TypeOfVal v tAny ->
    WellFormedRho (rhoCons x v r).
Hint Constructors WellFormedRho.

Lemma well_formed_path_lookup : forall r π v,
    WellFormedRho r ->
    path_lookup r π = rVal v ->
    exists t, TypeOfVal v t.
Proof.
Admitted.

Lemma Subtype_Prod : forall t1 t2 t3 t4,
    Subtype t1 t3 ->
    Subtype t2 t4 ->
    Subtype (tProd t1 t2) (tProd t3 t4).
Proof.
Admitted.

Lemma Subtype_Refl : forall t,
    Subtype t t.
Proof.
Admitted.
Hint Resolve Subtype_Refl.
  
Lemma Subtype_Top : forall t,
    Subtype t tAny.
Proof.
Admitted.
Hint Resolve Subtype_Top.


(* i.e. lemma 1 from ICFP 2010 *)
Lemma Proves_implies_Sat : forall Γ p r,
    Proves Γ p ->
    WellFormedRho r ->
    Forall (Sat r) Γ ->
    Sat r p.
Proof with auto.
  intros Γ p r Hproves.
  generalize dependent r.
  induction Hproves; intros r Hwfv Hsat.
  { (* P_Atom *)
    eapply Forall_forall; eassumption.
  }
  { (* P_Trivial *)
    crush.
  }
  { (* P_Combine *)
    assert (Sat r (Is π t1)) as H1 by auto.
    assert (Sat r (Is π t2)) as H2 by auto.
    inversion H1. inversion H2. subst.
    assert (v = v0) as Heq by crush. subst.
    eapply M_Is. eassumption.
    apply TOV_And; crush.
  }
  { (* P_Empty *)
    assert (Sat r (Is π tEmpty)) as H by auto.
    inversion H. subst. remember IsEmpty_no_vals as nomt.
    applyHinH. contradiction. unfold IsEmpty. crush.
  }
  { (* P_Sub *)
    assert (Sat r (Is π t1)) as Ht1 by auto.
    inversion Ht1; subst.
    econstructor. eassumption.
    eapply TOV_Sub. eassumption. assumption.
  }
  { (* P_Fst *)
    assert (Sat r (Is (pFst π) t)) as H by auto.
    inversion H; subst.
    assert (exists v', path_lookup r π = rVal (vPair v v')) as H'.
    {
      simpl in *. destruct (path_lookup r π); crush.
      destruct v0;
        try match goal with
            | [ H : rStuck = rVal _ |- _] => inversion H; crush
            end.
      same_rVal.
      eexists. eauto.
    }
    destruct H' as [v' Hv'].
    assert (path_lookup r (pSnd π) = rVal v') as Hlookup' by crush.
    assert (exists t', TypeOfVal v' t') as Ht'
        by (eapply well_formed_path_lookup; eassumption).
    destruct Ht' as [t' Ht'].
    eapply (M_Is π r Hv').
    econstructor. eassumption. eassumption.
    apply Subtype_Prod...
  }
  { (* P_Snd *)    
    assert (Sat r (Is (pSnd π) t)) as H by auto.
    inversion H; subst.
    assert (exists v', path_lookup r π = rVal (vPair v' v)) as H'.
    {
      simpl in *. destruct (path_lookup r π); crush.
      destruct v0;
        try match goal with
            | [ H : rStuck = rVal _ |- _] => inversion H; crush
            end.
      same_rVal.
      eexists. eauto.
    }
    destruct H' as [v' Hv'].
    assert (path_lookup r (pFst π) = rVal v') as Hlookup' by crush.
    assert (exists t', TypeOfVal v' t') as Ht'
        by (eapply well_formed_path_lookup; eassumption).
    destruct Ht' as [t' Ht'].
    eapply (M_Is π r Hv').
    econstructor. eassumption. eassumption.
    apply Subtype_Prod...
  }
  { (* P_Absurd *)
    assert (Sat r Absurd) as Hnope by auto.
    inversion Hnope.
  }
  { (* P_AndE_L *)
    assert (Sat r (And p1 p2)) as Hsat' by auto.
    inversion Hsat'; auto.
  }
  { (* P_AndE_R *)
    assert (Sat r (And p1 p2)) as Hsat' by auto.
    inversion Hsat'; auto.
  }
  { (* P_AndI *)
    crush.
  }
  { (* P_OrE *)
    assert (Sat r (Or p1 p2)) as Hsat' by auto.
    inversion Hsat'; subst; intuition.
  }
  { (* P_OrI_L *)
    apply M_Or_L. auto.
  }
  { (* P_OrI_R *)
    apply M_Or_R. auto.
  }
  { (* P_Refl *)
    assert (Sat r (Is π t)) as Hsat' by auto.
    inversion Hsat'; subst.
    eapply M_Eq; eauto.
  }
  { (* P_Subst *)
    assert (Sat r (Eq π π')) as Heq by auto.
    assert (Sat r p) as Hp by auto.
    eapply Sat_transport; eauto.    
  }
Qed.

Lemma Proves_implies_Sat' : forall Γ p r,
    Forall (Sat r) Γ ->
    WellFormedRho r ->
    Proves Γ p ->
    Sat r p.
Proof.
  intros.
  eapply Proves_implies_Sat; eauto.
Qed.

Inductive ObjSatVal : rho -> obj -> val -> Prop :=
| OSV_Top : forall r v,
    ObjSatVal r oTop v
| OSV_Path : forall r v π,
    path_lookup r π = (rVal v) ->
    ObjSatVal r (oPath π) v.
Hint Constructors ObjSatVal.

Inductive SatProps : rho -> val -> prop -> prop -> Prop :=
| SP_False : forall r p q,
    Sat r q ->
    SatProps r (vBool false) p q
| SP_NonFalse : forall r p q v,
    v <> (vBool false) ->
    Sat r p ->
    SatProps r v p q.
Hint Constructors SatProps.

Inductive SoundTypeRes : rho -> val -> tres -> Prop :=
| STR : forall r v t p q o,
    ObjSatVal r o v ->
    SatProps r v p q ->
    TypeOfVal v t ->
    SoundTypeRes r v (Res t p q o).
Hint Constructors SoundTypeRes.

Lemma Subobj_sound : forall r o1 o2 v,
    ObjSatVal r o1 v ->
    Subobj o1 o2 ->
    ObjSatVal r o2 v.
Proof.
  intros r o1 o2 v H1 Hsub.
  inversion H1; inversion Hsub; crush.
Qed.

Lemma In_IsEmpty : forall v t (P:Prop),
    IsEmpty t ->
    v ∈ (tInterp t) ->
    P.
Proof.
  intros v t P H1 H2.
  inversion H1; crush.
  match goal with
  | [H : _ = Empty_set val |- _] => rewrite H in *
  end.
  match goal with
  | [H : v ∈ Empty_set val |- _] => inversion H
  end.
Qed.  

Lemma In_empty : forall v P,
    v ∈ (Empty_set val) ->
    P.
Proof.
  intros v p H. inversion H.
Qed.  

Hint Extern 1 =>
match goal with
| [H : ?v ∈ (Empty_set val) |- ?P] =>
  apply (In_empty P H)
| [H : IsEmpty ?t, H' : ?v ∈ (tInterp ?t) |- ?P] =>
  apply (In_IsEmpty v t P)
end.

Lemma Setminus_eq : forall X A B,
    (Setminus X A B) = (Intersection X A (Complement X B)).
Proof.
  intros X A B.
  apply Extensionality_Ensembles.
  split.
  constructor.
  inversion H; crush.
  inversion H; crush.
  constructor; crush.
  inversion H; crush.
  inversion H; crush.
Qed.  

Lemma Complement_singleton : forall v v',
    v <> v' ->
    v ∈ (Complement val (Singleton val v')).
Proof.    
  intros v v' Hneq.
  intros H. inversion H; crush.
Qed.
  
Hint Extern 1 (_ ∈ _) =>
match goal with
| [ |- _ ∈ (Full_set val)]
    => constructor
| [ |- _ ∈ (tInterp tTrue)]
  => rewrite interp_tTrue
| [ |- _ ∈ (tInterp tFalse)]
  => rewrite interp_tFalse
| [ |- _ ∈ (tInterp (tAnd _ _))]
  => rewrite interp_tAnd
| [ |- _ ∈ (Setminus val _ _)]
  => rewrite Setminus_eq
| [ |- _ ∈ (Intersection val _ _)]
  => constructor
| [ |- _ ∈ (Complement val (Singleton val _))]
  => apply Complement_singleton
end. 

Lemma neq_false_Not_False : forall v,
    v <> (vBool false) ->
    TypeOfVal v (tNot tFalse).
Proof.
Admitted.

Lemma Sat_false_val : forall r v t1 p1 q1 o1,
    SoundTypeRes r v (Res t1 p1 q1 o1) ->
    v = (vBool false) ->
    Sat r (isa o1 (tAnd t1 tFalse)).
Proof with auto.
  intros r v t1 p1 q1 o1 Hstr Heq.
  inversion Hstr; subst.
  cbv.
  ifcase.
  { (* is empty (tAnd t1 (tBase btFalse)) *)
    assert (TypeOfVal (vBool false) (tAnd t1 (tBase btFalse)))
      as Hand by (apply TOV_And; auto).
    assert (IsEmpty (tAnd t1 (tBase btFalse))) as Hmtand by auto.
    assert False as impossible.
    eapply IsEmpty_no_vals; eassumption.
    contradiction.
  }
  { (* is not empty (tAnd t1 (tBase btFalse)) *)
    destruct o1.
    { (* o1 = oTop *)
      apply M_Trivial.
    }
    { (* o1 = oBot *)
      assert (ObjSatVal r oBot (vBoolfalse)) as Hobj by assumption.
      inversion Hobj.
    }
    { (* o1 = (oPath _) *)
      assert (ObjSatVal r (oPath p) (vBoolfalse)) as Hobj
          by assumption.
      inversion Hobj; subst.
      eapply (M_Is p r); crush.
      apply TOV_And; auto.
    }
  }
Qed.


Lemma Sat_nonfalse_val : forall r v t1 p1 q1 o1,
    SoundTypeRes r v (Res t1 p1 q1 o1) ->
    v <> (vBool false) ->
    Sat r (isa o1 (tAnd t1 (tNot tFalse))).
Proof.
  intros r v t1 p1 q1 o1 Hstr Hneq.
  inversion Hstr; subst.
  cbv.
  ifcase.
  { (* is empty (tAnd t1 (tNot (tBase btFalse))) *)
    assert (TypeOfVal v t1) as Ht1 by auto.
    assert (TypeOfVal v (tNot tFalse)) as Hnotfalse
    by (apply neq_false_Not_False; crush).
    assert (TypeOfVal v (tAnd t1 (tNot tFalse))) as Hand
        by (apply TOV_And; crush).
    assert (IsEmpty (tAnd t1 (tNot tFalse))) as Hmtand by auto.
    assert False as impossible by
          (eapply IsEmpty_no_vals; eassumption).
    contradiction.
  }
  { (* is not empty (tAnd t1 (tNot (tBase btFalse))) *)
    destruct o1.
    { (* o1 = oTop *)
      apply M_Trivial.
    }
    { (* o1 = oBot *)
      assert (ObjSatVal r oBot v) as Hobj by assumption.
      inversion Hobj.
    }
    { (* o1 = (oPath _) *)
      assert (ObjSatVal r (oPath p) v) as Hobj
          by assumption.
      inversion Hobj; subst.
      eapply (M_Is p r).
      eassumption.
      apply TOV_And. eassumption.
      apply neq_false_Not_False. auto.
    }
  }
Qed.
 
Hint Extern 1 (Sat _ _) => 
match goal with
| [H : Proves ?Γ ?p |- Sat ?r ?p]
  => apply (Proves_implies_Sat H)
| [H : (Forall (Sat ?r) ?Γ) |- Sat ?r ?p]
  => apply (Proves_implies_Sat' H)
end. 

Lemma Subres_sound : forall Γ r v R1 R2,
    Forall (Sat r) Γ ->
    WellFormedRho r ->
    SoundTypeRes r v R1 ->
    Subres Γ R1 R2 ->
    SoundTypeRes r v R2.
Proof.
  intros Γ r v R R' Hsat Hwfr Hstr Hsr.
  induction Hsr.
  {
    inversion Hstr; subst.
    constructor.
    eapply Subobj_sound; eassumption.    
    destruct (val_dec v (vBool false)) as [Heq | Hneq].
    { (* v = false *)
      subst.
      apply SP_False.
      assert (Sat r (isa o1 (tAnd t1 tFalse))) as Hv
          by (eapply Sat_false_val; eauto).
      eapply Proves_implies_Sat. eassumption.
      crush. crush.
    }
    { (* v <> false *)
      apply SP_NonFalse; auto.
      assert (Sat r (isa o1 (tAnd t1 (tNot tFalse)))) as Hv
          by (eapply Sat_nonfalse_val; eauto).
      crush.
    }
    eapply TOV_Sub. eassumption. assumption.
  }
  {
    destruct (val_dec v (vBool false)) as [Heq | Hneq].
    { (* v = false *)
      assert (Sat r Absurd) as impossible.
      {
        assert (Sat r (isa o1 (tAnd t1 tFalse)))
          as Hisa by (eapply Sat_false_val; eauto).
        crush.
      }
      inversion impossible.
    }
    { (* v <> false *)
      assert (Sat r Absurd) as impossible.
      {
        assert (Sat r (isa o1 (tAnd t1 (tNot tFalse))))
          as Hisa by (eapply Sat_nonfalse_val; eauto).
        assert (Forall (Sat r) (isa o1 (tAnd t1 (tNot tFalse)) :: Γ))
          as Hsat' by auto.
        crush.
      }
      inversion impossible.
    }
  }
  {
    inversion Hstr; subst.
    constructor.
    {
      eapply Subobj_sound. eassumption.
      apply SO_Refl.
    }
    {
      destruct (val_dec v (vBool false)) as [Heq | Hneq].
      { (* v = false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.
      }
      { (* v <> false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.
        assert (Sat r Absurd) as impossible.
        {
          assert (Sat r (isa o1 (tAnd t1 (tNot tFalse))))
            as Hisa by (eapply Sat_nonfalse_val; eauto).
          crush.
        }
        inversion impossible.
      }
    }
    {
      inversion Hstr; subst.
      apply TOV_And; crush.
      destruct (val_dec v (vBool false)) as [Heq | Hneq]; crush.
      { (* v <> false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.
        assert (Sat r Absurd) as impossible.
        {
          assert (Sat r (isa o1 (tAnd t1 (tNot tFalse))))
            as Hisa by (eapply Sat_nonfalse_val; eauto).
          crush.
        }
        inversion impossible.
      }
    }    
  }
  {
    inversion Hstr; subst.
    constructor.
    {
      eapply Subobj_sound. eassumption.
      apply SO_Refl.
    }
    {
      destruct (val_dec v (vBool false)) as [Heq | Hneq].
      { (* v = false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.
        assert (Sat r Absurd) as impossible.
        {
          assert (Sat r (isa o1 (tAnd t1 tFalse)))
            as Hisa by (eapply Sat_false_val; eauto).
          crush.
        }
        inversion impossible.
      }
      { (* v <> false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.        
      }
    }
    {
      inversion Hstr; subst.
      apply TOV_And; crush.
      destruct (val_dec v (vBool false)) as [Heq | Hneq].
      { (* v = false *)
        match goal with
        | [H : SatProps _ _ _ _ |- _] => inversion H
        end; crush.
        assert (Sat r Absurd) as impossible.
        {
          assert (Sat r (isa o1 (tAnd t1 tFalse)))
            as Hisa by (eapply Sat_false_val; eauto).
          crush.
        }
        inversion impossible.
      }
      { (* v <> false *)
        apply neq_false_Not_False; auto.
      }
    }    
  }
Qed.

Ltac notIsProc :=
  match goal with
  | [H : IsProc _ |- _] => inversion H
  end.

Lemma tArrow_top : forall t1 t2 t3,
    Subtype (tArrow t1 t2) (tArrow tEmpty t3).
Proof.
Admitted.
Hint Resolve tArrow_top.

Lemma op_is_tArrow : forall o,
    TypeOfVal (vOp o) (tArrow tEmpty tAny).
Proof.
  intros o.
  constructor.
  destruct o; crush; try (unfold predicate);
    try (apply Subtype_tAnd_L); crush.
Qed.

Lemma IsEmpty_And_tAny : forall t,
    IsEmpty (tAnd t tAny) ->
    IsEmpty t.
Proof.
Admitted.

Lemma interface_non_empty : forall i,
    ~ IsEmpty (interface_ty i).
Proof.
Admitted.

Lemma Subtype_And_R1_Refl : forall t t',
    Subtype t (tAnd t t').
Proof.
Admitted.
Hint Resolve Subtype_And_R1_Refl.

Lemma Subtype_And_R2_Refl : forall t t',
    Subtype t (tAnd t' t).
Proof.
Admitted.
Hint Resolve Subtype_And_R2_Refl.


Lemma lemma3 : forall Γ e R r n,
      TypeOf Γ e R ->
      Forall (Sat r) Γ ->
      WellFormedRho r ->
      (exists v, ValOf n r e (rVal v) /\ SoundTypeRes r v R) 
      \/ (ValOf n r e rError)
      \/ (ValOf n r e rTimeout).
Proof with crush.
  (* BOOKMARK *)
  intros Γ e R r n Htype Hsat Hwfv.
  induction Hvalof.
  { (* V_Timeout *)
    crush.
  }
  { (* V_Var *)
    inversion Htype; subst.
    remember (var_lookup r x) as Hlook.
    destruct Hlook.
    { (* rVal v = var_lookup r x *)
      left. eexists. split. reflexivity.
      assert (Sat r (Is π t)) as Hsatis
          by (eapply Proves_implies_Sat; eassumption).
      inversion Hsatis; subst.
      assert (Sat r (Eq (pVar x) π)) as Hsateq
          by (eapply Proves_implies_Sat; eassumption).
      inversion Hsateq; subst.
      assert (SoundTypeRes r v (Res t
                                    (Is π (tAnd t (tNot tFalse)))
                                    (Is π (tAnd t tFalse))
                                    (oPath π)))
        as Hstr.
      {
        constructor. constructor. crush.
        destruct (val_dec v (vBool false)) as [Heq | Hneq]; subst.
        { (* v = false *)
          constructor. eapply M_Is; crush.
      }
        { (* v <> false *)
          apply SP_NonFalse. assumption.
          eapply M_Is. eassumption.
          crush.
          apply TOV_And; crush.
          apply neq_false_Not_False.
          crush.
        }
        crush.
      }
      eapply Subres_sound; eauto.
    }
    { (* rFail f = var_lookup r x *)
      assert (Sat r (Is π t)) as Hsatis
          by (eapply Proves_implies_Sat; eassumption).
      inversion Hsatis; subst.
      assert (Sat r (Eq (pVar x) π)) as Hsateq
          by (eapply Proves_implies_Sat; eassumption).
      inversion Hsateq; crush.
    }
  }
  { (* V_Const *)
    inversion Htype; subst.
    destruct c.
    { (* vNat *)
      simpl in *.
      left. exists (vNat n0).
      split; auto.
      assert (SoundTypeRes r (vNat n0) (Res tNat Trivial Absurd oTop))
        as Hstr.
      {
        constructor; crush.
        apply SP_NonFalse; crush.
      }
      eapply Subres_sound; eauto.
    }
    { (* vStr *)
      simpl in *.
      left. exists (vStr s).
      split; auto.
      assert (SoundTypeRes r (vStr s) (Res tStr Trivial Absurd oTop))
        as Hstr.
      {
        constructor; crush.
        apply SP_NonFalse; crush.
      }
      eapply Subres_sound; eauto.
    }
    { (* vBool *)
      destruct b.
      { (* b = true *)
        simpl in *.
        left. exists (vBool true).
        split; auto.
        assert (SoundTypeRes r (vBool true) (Res tTrue Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* b = false *)
        simpl in *.
        left. exists (vBool false).
        split; auto.
        assert (SoundTypeRes r (vBool false)
                             (Res tFalse Absurd Trivial oTop))
          as Hstr by crush.
        eapply Subres_sound; eauto.
      }      
    }
    { (* vOp *)
      destruct o.
      { (* opAdd1 *)
        simpl in *.
        left. exists (vOp opAdd1).
        split; auto.
        assert (SoundTypeRes r (vOp opAdd1)
                             (Res (tArrow tNat tNat) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opSub1 *)
        simpl in *.
        left. exists (vOp opSub1).
        split; auto.
        assert (SoundTypeRes r (vOp opSub1)
                             (Res (tArrow tNat tNat) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opStrLen *)
        simpl in *.
        left. exists (vOp opStrLen).
        split; auto.
        assert (SoundTypeRes r (vOp opStrLen)
                             (Res (tArrow tStr tNat) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opNot *)
        simpl in *.
        left. exists (vOp opNot).
        split; auto.
        assert (SoundTypeRes r (vOp opNot)
                             (Res (predicate tFalse) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opIsNat *)
        simpl in *.
        left. exists (vOp opIsNat).
        split; auto.
        assert (SoundTypeRes r (vOp opIsNat)
                             (Res (predicate tNat) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush. 
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opIsStr *)
        simpl in *.
        left. exists (vOp opIsStr).
        split; auto.
        assert (SoundTypeRes r (vOp opIsStr)
                             (Res (predicate tStr) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opIsPair *)
        simpl in *.
        left. exists (vOp opIsPair).
        split; auto.
        assert (SoundTypeRes r (vOp opIsPair)
                             (Res (predicate (tProd tAny tAny))
                                  Trivial
                                  Absurd
                                  oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opIsProc *)
        simpl in *.
        left. exists (vOp opIsProc).
        split; auto.
        assert (SoundTypeRes r (vOp opIsProc)
                             (Res (predicate (tArrow tEmpty tAny))
                                  Trivial
                                  Absurd
                                  oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opIsZero *)
        simpl in *.
        left. exists (vOp opIsZero).
        split; auto.
        assert (SoundTypeRes r (vOp opIsZero)
                             (Res (tArrow tNat tBool) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
      { (* opError *)
        simpl in *.
        left. exists (vOp opError).
        split; auto.
        assert (SoundTypeRes r (vOp opError)
                             (Res (tArrow tStr tEmpty) Trivial Absurd oTop))
          as Hstr.
        {
          constructor; crush.
          apply SP_NonFalse; crush.
        }
        eapply Subres_sound; eauto.
      }
    }
  }
  { (* V_Abs *)
    inversion Htype; subst.
    (* BOOKMARK *)
    left. exists (vClos r f i x e); split; auto.
    assert (SoundTypeRes r (vClos r f i x e)
                         (Res (int_to_ty i)
                              Trivial
                              Absurd
                              oTop))
      as Hstr.
    {
      constructor; crush.
      constructor; crush.
      eapply closure_interface_lemma; eauto.
    }
      (* BOOKMARK *)
      eapply Subres_sound; eauto.
  }
  { (* V_App_Fail1 *)
  }
  { (* V_App_Fail2 *)
  }
  {
    (* V_App_Fail3 *)
  }
  {
    (* V_App_Op *)
  }
  {
    (* V_App_Clos *)
  }
  {
    (* V_Pair_Fail1 *)
  }
  {
    (* V_Pair_Fail2 *)
  }
  {
    (* V_Pair *)
  }
  {
    (* V_Fst_Fail1 *)
  }
  {
    (* V_Fst_Fail2 *)
  }
  {
    (* V_Fst *)
  }
  {
    (* V_Snd_Fail1 *)
  }
  {
    (* V_Snd_Fail2 *)
  }
  {
    (* V_Snd *)
  }
  {
    (* V_If_Fail1 *)
  }
  {
    (* V_If_NonFalse *)
  }
  {
    (* V_If_False *)
  }
  {
    (* V_Let_Fail *)
  }
  {
    (* V_Let *)
  }
Admitted.

  
