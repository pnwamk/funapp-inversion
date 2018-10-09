
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
| opIsPair
| opIsProc
| opIsZero
| opError.
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
| tProd  : ty -> ty -> ty
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
| eConst : const -> exp
| eAbs   : var -> interface -> var -> exp -> exp
| eApp   : exp -> exp -> exp
| ePair  : exp -> exp -> exp
| eFst   : exp -> exp
| eSnd   : exp -> exp
| eIf    : exp -> exp -> exp -> exp
| eLet   : var -> exp -> exp -> exp.
Hint Constructors exp.

Notation "(eNat n )"  := (eConst (cNat n)).
Notation "(eStr s )"  := (eConst (cStr s)).
Notation "(eBool b )" := (eConst (cBool b)).
Notation "(eOp o )"   := (eConst (cOp o)).


Inductive val : Set :=
  vConst : const -> val
| vPair  : val -> val -> val
| vClos  : rho -> var -> interface -> var -> exp -> val
with
rho : Set :=
  rhoNull  : rho
| rhoCons  : var -> val -> rho -> rho.
Hint Constructors val rho.

Notation "(vNat n )"  := (vConst (cNat n)).
Notation "(vStr s )"  := (vConst (cStr s)).
Notation "(vBool b )" := (vConst (cBool b)).
Notation "(vOp o )"   := (vConst (cOp o)).

Inductive path : Set :=
  pVar : var -> path
| pFst : path -> path
| pSnd : path -> path.
Hint Constructors path.

Inductive obj : Set :=
  oTop  : obj
| oBot  : obj
| oPath : path -> obj.
Hint Constructors obj.

Notation "(oFst p )"  := (oPath (pFst p)).
Notation "(oSnd p )"  := (oPath (pSnd p)).
Notation "(oVar x )"  := (oPath (pVar x)).


Inductive prop : Set :=
  Trivial : prop
| Absurd  : prop
| And     : prop -> prop -> prop
| Or      : prop -> prop -> prop
| Is      : path -> ty -> prop
| Eq      : path -> path -> prop.
Hint Constructors prop.

Definition gamma := list prop.
Hint Unfold gamma.

Inductive tres : Set :=
  Res : ty -> prop -> prop -> obj -> tres.
Hint Constructors tres.

Inductive failure : Set := fError | fStuck | fTimeout.
Hint Constructors failure.

Inductive result : Set :=
  rVal  : val -> result
| rFail : failure -> result.
Hint Constructors result.

Notation rError   := (rFail fError).
Notation rStuck   := (rFail fStuck).
Notation rTimeout := (rFail fTimeout).

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

Definition exp_dec : forall (x y : exp),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve exp_dec.

Fixpoint val_dec (x y : val) : { x = y } + { x <> y }
with
rho_dec (x y : rho) : { x = y } + { x <> y }.
Proof.
  decide equality.
  decide equality.
Defined.
Hint Resolve val_dec rho_dec.

Definition path_dec : forall (x y : path),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve path_dec.

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

Definition failure_dec : forall (x y : failure),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve failure_dec.

Definition result_dec : forall (x y : result),
    {x = y} + {x <> y}.
Proof. decide equality. Defined.
Hint Resolve result_dec.

(**********************************************************)
(* Dynamic Semantics                                      *)
(**********************************************************)

Definition apply_op (o:op) (v:val) : result :=
  match o , v with
  | opAdd1   , (vNat n)          => rVal (vNat (n + 1))
  | opAdd1   , _                 => rStuck
  | opSub1   , (vNat n)          => rVal (vNat (n - 1))
  | opSub1   , _                 => rStuck
  | opStrLen , (vStr s)          => rVal (vNat (String.length s))
  | opStrLen , _                 => rStuck
  | opNot    , (vBool false)     => rVal (vBool true)
  | opNot    , _                 => rVal (vBool false)
  | opIsNat  , (vNat _)          => rVal (vBool true)
  | opIsNat  , _                 => rVal (vBool false)
  | opIsStr  , (vStr _)          => rVal (vBool true)
  | opIsStr  , _                 => rVal (vBool false)
  | opIsPair , (vPair _ _)       => rVal (vBool true)
  | opIsPair , _                 => rVal (vBool false)
  | opIsProc , (vOp _)           => rVal (vBool true)
  | opIsProc , (vClos _ _ _ _ _) => rVal (vBool true)
  | opIsProc , _                 => rVal (vBool false)
  | opIsZero , (vNat 0)          => rVal (vBool true)
  | opIsZero , (vNat _)          => rVal (vBool false)
  | opIsZero , _                 => rStuck
  | opError  , (vStr s)          => rError
  | opError  , _                 => rStuck
  end.
Hint Unfold apply_op.

Fixpoint var_lookup (r:rho) (x:var) : result :=
  match r with
  | rhoNull       => rStuck
  | rhoCons y v r' => if var_dec x y
                      then rVal v
                      else var_lookup r' x
  end.
Hint Unfold var_lookup.

Fixpoint path_lookup (r:rho) (π:path) : result :=
  match π with
  | (pVar x) => var_lookup r x
  | (pFst π') =>
    match (path_lookup r π') with
    | (rVal (vPair v _)) => rVal v
    | _ => rStuck
    end
  | (pSnd π') =>
    match (path_lookup r π') with
    | (rVal (vPair _ v)) => rVal v
    | _ => rStuck
    end
  end.
Hint Unfold path_lookup.

Inductive NonOp : const -> Prop :=
| NO_Nat : forall n, NonOp (cNat n)
| NO_Str : forall s, NonOp (cStr s)
| NO_Bool : forall b, NonOp (cBool b).
Hint Constructors NonOp.

Inductive NonPair : val -> Prop :=
| NP_Const : forall c, NonPair (vConst c)
| NP_Clos : forall r f i x e, NonPair (vClos r f i x e).
Hint Constructors NonPair.


Inductive ValOf : nat -> rho -> exp -> result -> Prop :=
| V_Timeout : forall r e,
    ValOf O r e rTimeout
| V_Var : forall n r x,
    ValOf (S n) r (eVar x) (var_lookup r x)
| V_Const : forall n r c,
    ValOf (S n) r (eConst c) (rVal (vConst c))
| V_Abs : forall n r f i x e,
    ValOf (S n) r (eAbs f i x e) (rVal (vClos r f i x e))
| V_App_Fail1 : forall n r e1 e2 f,
    ValOf n r e1 (rFail f) ->
    ValOf (S n) r (eApp e1 e2) (rFail f)
| V_App_Fail2 : forall n r e1 e2 c,
    ValOf n r e1 (rVal (vConst c)) ->
    NonOp c ->
    ValOf (S n) r (eApp e1 e2) rStuck
| V_App_Fail3 : forall n r e1 e2 v1 f,
    ValOf n r e1 (rVal v1) ->
    ValOf n r e2 (rFail f) ->
    ValOf (S n) r (eApp e1 e2) (rFail f)
| V_App_Op : forall n r e1 e2 o1 v2,
    ValOf n r e1 (rVal (vOp o1)) ->
    ValOf n r e2 (rVal v2) ->
    ValOf (S n) r (eApp e1 e2) (apply_op o1 v2)
| V_App_Clos : forall n r e1 e2 r' f i x e' v2 r'' res,
    ValOf n r e1 (rVal (vClos r' f i x e')) ->
    ValOf n r e2 (rVal v2) ->
    r'' = (rhoCons x v2 (rhoCons f (vClos r' f i x e') r')) ->
    ValOf n r'' e' res ->
    ValOf (S n) r (eApp e1 e2) res
| V_Pair_Fail1 : forall n r e1 e2 f,
    ValOf n r e1 (rFail f) ->
    ValOf (S n) r (ePair e1 e2) (rFail f)
| V_Pair_Fail2 : forall n r e1 e2 v1 f,
    ValOf n r e1 (rVal v1) ->
    ValOf n r e2 (rFail f) ->
    ValOf (S n) r (ePair e1 e2) (rFail f)
| V_Pair : forall n r e1 e2 v1 v2,
    ValOf n r e1 (rVal v1) ->
    ValOf n r e2 (rVal v2) ->
    ValOf (S n) r (ePair e1 e2) (rVal (vPair v1 v2))
| V_Fst_Fail1 : forall n r e f,
    ValOf n r e (rFail f) ->
    ValOf (S n) r (eFst e) (rFail f)
| V_Fst_Fail2 : forall n r e v,
    ValOf n r e (rVal v) ->
    NonPair v ->
    ValOf (S n) r (eFst e) rStuck
| V_Fst : forall n r e v1 v2,
    ValOf n r e (rVal (vPair v1 v2)) ->
    ValOf (S n) r (eFst e) (rVal v1)
| V_Snd_Fail1 : forall n r e f,
    ValOf n r e (rFail f) ->
    ValOf (S n) r (eSnd e) (rFail f)
| V_Snd_Fail2 : forall n r e v,
    ValOf n r e (rVal v) ->
    NonPair v ->
    ValOf (S n) r (eSnd e) rStuck
| V_Snd : forall n r e v1 v2,
    ValOf n r e (rVal (vPair v1 v2)) ->
    ValOf (S n) r e (rVal v2)
| V_If_Fail1 : forall n r e1 e2 e3 f,
    ValOf n r e1 (rFail f) ->
    ValOf (S n) r (eIf e1 e2 e3) (rFail f)
| V_If_NonFalse : forall n r e1 e2 e3 v1 res,
    ValOf n r e1 (rVal v1) ->
    v1 <> (vBool false) ->
    ValOf n r e2 res ->
    ValOf (S n) r (eIf e1 e2 e3) res
| V_If_False : forall n r e1 e2 e3 res,
    ValOf n r e1 (rVal (vBool false)) ->
    ValOf n r e3 res ->
    ValOf (S n) r (eIf e1 e2 e3) res
| V_Let_Fail : forall n r x e1 e2 f,
    ValOf n r e1 (rFail f) ->
    ValOf (S n) r (eLet x e1 e2) (rFail f)
| V_Let : forall n r x e1 e2 v1 res,
    ValOf n r e1 (rVal v1) ->
    ValOf n (rhoCons x v1 r) e2 res ->
    ValOf (S n) r (eLet x e1 e2) res.
Hint Constructors ValOf.

Fixpoint eval (fuel:nat) (r:rho) (expr:exp) : result :=
  match fuel with
  | O => rTimeout
  | S n =>
    match expr with
    | eVar x => var_lookup r x
    | eConst c => rVal (vConst c)
    | eAbs f i x e => rVal (vClos r f i x e)
    | eApp e1 e2 =>
      match (eval n r e1) , (eval n r e2) with
      | rFail f, _ => rFail f
      | _, rFail f => rFail f
      | rVal v1, rVal v2 =>
        match v1 with
        | vConst (cOp o) => apply_op o v2
        | vClos r f i x e =>
          let r' := rhoCons x v2 (rhoCons f v1 r) in
          eval n r' e
        | _ => rStuck
        end
      end
    | ePair e1 e2 =>
      match (eval n r e1) , (eval n r e2) with
      | rFail f, _ => rFail f
      | _, rFail f => rFail f
      | rVal v1, rVal v2 => rVal (vPair v1 v2)
      end
    | eFst e =>
      match (eval n r e) with
      | rFail f => rFail f
      | rVal (vPair v1 v2) => rVal v1
      | rVal _ => rStuck
      end
    | eSnd e =>
      match (eval n r e) with
      | rFail f => rFail f
      | rVal (vPair v1 v2) => rVal v2
      | rVal _ => rStuck
      end
    | eIf e1 e2 e3 =>
      match (eval n r e1) with
      | rFail f => rFail f
      | rVal (vBool false) => eval n r e3
      | rVal _ => eval n r e2
      end
    | eLet x e1 e2 =>
      match (eval n r e1) with
      | rFail f => rFail f
      | rVal v => eval n (rhoCons x v r) e2
      end
    end 
  end.

(* TODO? May be interesting, may not. *)
Lemma ValOf_iff_eval : forall n r e res,
    ValOf n r e res <-> eval n r e = res.
Proof.
  Admitted.

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
Axiom interp_tTrue : tInterp tTrue = (Singleton val (vConst (cBool true))).
Hint Rewrite interp_tTrue.
Axiom interp_tFalse : tInterp tFalse = (Singleton val (vConst (cBool false))).
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
Axiom interp_tProd_exists : forall (t1 t2:ty) (v:val),
    v ∈ (tInterp (tProd t1 t2)) ->
    exists (v1 v2:val), v = (vPair v1 v2)
                        /\ v1 ∈ (tInterp t1)
                        /\ v2 ∈ (tInterp t2).
Axiom interp_tProd_full : forall (v1 v2:val) (t1 t2:ty),
    v1 ∈ (tInterp t1) ->
    v2 ∈ (tInterp t2) ->
    (vPair v1 v2) ∈ (tInterp (tProd t1 t2)).
Hint Resolve interp_tProd_full.

Notation "A '⊆' B" :=
  (Included val A B) (at level 55, right associativity).

Definition Subtype (t1 t2:ty) : Prop := (tInterp t1) ⊆ (tInterp t2).
  
Definition IsEmpty (t: ty) := (tInterp t) = (Empty_set val).
Hint Unfold IsEmpty.

Axiom empty_dec : forall (t: ty), {IsEmpty t} + {~ IsEmpty t}.

Inductive Subobj : obj -> obj -> Prop :=
| SO_Refl : forall o,
    Subobj o o
| SO_Bot : forall o,
    Subobj oBot o
| SO_Top : forall o,
    Subobj o oTop.
Hint Constructors Subobj.

(* (SubstPath π1 π π' π2 *)
(* π1[π ↦ π'] = π2 but where the substitution is optional *)
Inductive SubstPath : path -> path -> path -> path -> Prop :=
| SPath_Refl : forall π1 π π',
    SubstPath π1 π π' π1
| SPath_Swap : forall π π',
    SubstPath π π π' π'
| SPath_Fst : forall π1 π π' π2,
    SubstPath π1 π π' π2 ->
    SubstPath (pFst π1) π π' (pFst π2)
| SPath_Snd : forall π1 π π' π2,
    SubstPath π1 π π' π2 ->
    SubstPath (pSnd π1) π π' (pSnd π2).


(* (SubstProp p1 π π' p2)  *)
(* p1[π ↦ π'] = p2 but where the substitution is optional *)
Inductive SubstProp : prop -> path -> path -> prop -> Prop :=
| SProp_Refl : forall p π π',
    SubstProp p π π' p
| SProp_And : forall p1 p2 p1' p2' π π',
    SubstProp p1 π π' p1' ->
    SubstProp p2 π π' p2' ->
    SubstProp (And p1 p2) π π' (And p1' p2')
| SProp_Or : forall p1 p2 p1' p2' π π',
    SubstProp p1 π π' p1' ->
    SubstProp p2 π π' p2' ->
    SubstProp (Or p1 p2) π π' (Or p1' p2')
| SProp_Is : forall π1 π1' π π' t1,
    SubstPath π1 π π' π1' ->
    SubstProp (Is π1 t1) π π' (Is π1' t1)
| SProp_Eq : forall π1 π1' π2 π2' π π',
    SubstPath π1 π π' π1' ->
    SubstPath π2 π π' π2' ->
    SubstProp (Eq π1 π2) π π' (Eq π1' π2').

Inductive Proves : gamma -> prop -> Prop :=
| P_Atom : forall Γ p,
    In p Γ ->
    Proves Γ p
| P_Trivial : forall Γ,
    Proves Γ Trivial
| P_Combine : forall Γ π t1 t2,
    Proves Γ (Is π t1) ->
    Proves Γ (Is π t2) ->
    Proves Γ (Is π (tAnd t1 t2))
| P_Empty : forall Γ π p,
    Proves Γ (Is π tEmpty) ->
    Proves Γ p
| P_Sub : forall Γ π t1 t2,
    Proves Γ (Is π t1) ->
    Subtype t1 t2 ->
    Proves Γ (Is π t2)
| P_Fst : forall Γ π t,
    Proves Γ (Is (pFst π) t) ->
    Proves Γ (Is π (tProd t tAny))
| P_Snd : forall Γ π t,
    Proves Γ (Is (pSnd π) t) ->
    Proves Γ (Is π (tProd tAny t))       
| P_Absurd : forall Γ p,
    Proves Γ Absurd ->
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
    Proves Γ (Or p1 p2)
| P_OrI_R : forall Γ p1 p2,
    Proves Γ p2 ->
    Proves Γ (Or p1 p2)
| P_Refl : forall Γ π t,
    Proves Γ (Is π t) ->
    Proves Γ (Eq π π)
| P_Subst : forall Γ π π' p q,
    Proves Γ (Eq π π') ->
    Proves Γ p ->
    SubstProp p π π' q ->
    Proves Γ q.
Hint Constructors Proves.

Lemma P_Subset : forall Γ Γ' p,
    Proves Γ p ->
    incl Γ Γ' ->
    Proves Γ' p.
Proof with auto.
  intros Γ Γ' p Hproves.
  generalize dependent Γ'. 
  induction Hproves; crush.
  eapply P_Empty... 
  eapply P_Sub... 
  eapply P_AndE_L... 
  eapply P_AndE_R... 
  eapply P_OrE...
  apply IHHproves2; crush.
  apply IHHproves3; crush.
  eapply P_Refl...
  eapply P_Subst.
  apply IHHproves1...
  apply IHHproves2...
  assumption.
Qed.

  
Definition isa (o:obj) (t:ty) : prop :=
  if empty_dec t
  then Absurd
  else match o with
       | oPath π => Is π t
       | oTop => Trivial
       | oBot => Absurd    
       end.
Hint Unfold isa.

Definition maybeFst (o:obj) : obj :=
  match o with
  | oTop => oTop
  | oBot => oBot
  | oPath π => oPath (pFst π)
  end.
Hint Unfold maybeFst.

Definition maybeSnd (o:obj) : obj :=
  match o with
  | oTop => oTop
  | oBot => oBot
  | oPath π => oPath (pSnd π)
  end.
Hint Unfold maybeSnd.

Inductive Subres : gamma -> tres -> tres -> Prop :=
| SR_Sub : forall Γ t1 p1 q1 o1 t2 p2 q2 o2,
    Subtype t1 t2 ->
    Subobj o1 o2 ->
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::Γ) p2 ->
    Proves ((isa o1 (tAnd t1 tFalse))::Γ) q2 ->
    Subres Γ (Res t1 p1 q1 o1) (Res t2 p2 q2 o2)
| SR_Absurd : forall Γ t1 p1 q1 o1,
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::Γ) Absurd ->
    Proves ((isa o1 (tAnd t1 tFalse))::Γ) Absurd ->
    Subres Γ (Res t1 p1 q1 o1) (Res tEmpty Absurd Absurd oBot)
| SR_False : forall Γ t1 p1 q1 o1,
    Proves ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) Absurd ->
    Subres Γ (Res t1 p1 q1 o1) (Res (tAnd t1 tFalse) Absurd q1 o1)
| SR_NonFalse : forall Γ t1 p1 q1 o1,
    Proves ((isa o1 (tAnd t1 tFalse))::q1::Γ) Absurd ->
    Subres Γ (Res t1 p1 q1 o1) (Res (tAnd t1 (tNot tFalse)) p1 Absurd o1).
Hint Constructors Subres.


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
  | opIsPair => predicate (tProd tAny tAny)
  | opIsProc => predicate (tArrow tEmpty tAny)
  | opIsZero => tArrow tNat tBool
  | opError  => tArrow tStr tEmpty
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

Fixpoint fvsPath (π:path) : list var :=
  match π with
  | pVar x => [x]
  | pFst π' => fvsPath π'
  | pSnd π' => fvsPath π'
  end.
Hint Unfold fvsPath.

Fixpoint fvsP (p:prop) : list var :=
  match p with
  | Trivial => []
  | Absurd => []
  | And p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Or p1 p2 => (fvsP p1) ++ (fvsP p2)
  | Is π t => fvsPath π
  | Eq π π' => (fvsPath π) ++ (fvsPath π')
  end.
Hint Unfold fvsP.

Fixpoint fvs (Γ:gamma) : list var :=
  match Γ with
  | [] => []
  | p::ps => (fvsP p) ++ (fvs ps)
  end.
Hint Unfold fvs.

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
  | (Res _ _ _ (oPath π)) => Eq (pVar x) π
  | (Res t p q oTop) =>
    let p' := And p (Is (pVar x) (tAnd t (tNot tFalse))) in
    let q' := And q (Is (pVar x) (tAnd t tFalse)) in
    And (Is (pVar x) t) (Or p' q')
  end.
Hint Unfold alias.

Axiom Pred : ty -> ty -> ty -> ty -> Prop.


Inductive TypeOf : gamma -> exp -> tres -> Prop :=
| T_Var : forall Γ x π t R,
    Proves Γ (Eq (pVar x) π) ->
    Proves Γ (Is π t) ->
    Subres Γ
           (Res t
                (Is π (tAnd t (tNot tFalse)))
                (Is π (tAnd t tFalse))
                (oPath π))
           R ->
    TypeOf Γ (eVar x) R 
| T_Const : forall Γ c R,
    Subres Γ (const_tres c) R ->
    TypeOf Γ (eConst c) R
| T_Abs : forall Γ f i i' x e t R,
    x <> f ->
    ~ In x (fvs Γ) ->
    ~ In f (fvs Γ) ->
    t = (tAnd (interface_ty i) (neg_interface_ty i')) ->
    ~ IsEmpty t ->
    (forall t1 t2,
        InInterface t1 t2 i ->
        TypeOf ((Is (pVar x) t1)::(Is (pVar f) t)::Γ)
               e
               (Res t2 Trivial Trivial oTop)) ->
    Subres Γ (Res t Trivial Absurd oTop) R ->
    TypeOf Γ (eAbs f i x e) R
| T_App : forall Γ e1 e2 t1 t2 o2 t tpos tneg R,
    TypeOf Γ e1 (Res t1 Trivial Trivial oTop) ->
    TypeOf Γ e2 (Res t2 Trivial Trivial o2) ->
    Subtype t1 (tArrow t2 t) ->
    Pred t1 t2 tpos tneg ->
    Subres Γ (Res t (isa o2 tpos) (isa o2 tneg) oTop) R ->
    TypeOf Γ (eApp e1 e2) R
| T_Pair : forall Γ e1 e2 t1 t2 R,
    TypeOf Γ e1 (Res t1 Trivial Trivial oTop) ->
    TypeOf Γ e2 (Res t2 Trivial Trivial oTop) ->
    Subres Γ (Res (tProd t1 t2) Trivial Absurd oTop) R ->
    TypeOf Γ (ePair e1 e2) R
| T_Fst : forall Γ e t t1 t2 o R,
    TypeOf Γ e (Res t Trivial Trivial oTop) ->
    Subtype t (tProd t1 t2) ->
    Subres Γ (Res t1 Trivial Trivial (maybeFst o)) R ->
    TypeOf Γ (eFst e) R
| T_Snd : forall Γ e t t1 t2 o R,
    TypeOf Γ e (Res t Trivial Trivial oTop) ->
    Subtype t (tProd t1 t2) ->
    Subres Γ (Res t2 Trivial Trivial (maybeSnd o)) R->
    TypeOf Γ (eSnd e) R
| T_If : forall Γ e1 e2 e3 t1 R2 R3 p1 q1 o1 R,
    TypeOf Γ e1 (Res t1 p1 q1 o1) ->
    TypeOf ((isa o1 (tAnd t1 (tNot tFalse)))::p1::Γ) e2 R2 ->
    TypeOf ((isa o1 (tAnd t1 tFalse))::q1::Γ) e3 R3 ->
    Subres Γ (tresOr R2 R3) R ->
    TypeOf Γ (eIf e1 e2 e3) R
| T_Let : forall Γ x e1 e2 R1 R2 R,
    ~ In x (fvs Γ) ->
    TypeOf Γ e1 R1 ->
    TypeOf ((alias x R1)::Γ) e2 R2 ->
    Subres Γ R2 R ->
    TypeOf Γ (eLet x e1 e2) R.
Hint Constructors TypeOf.


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


Lemma lemma3 : forall Γ e R r n res,
      TypeOf Γ e R ->
      Forall (Sat r) Γ ->
      WellFormedRho r ->
      ValOf n r e res ->
      (exists v, res = rVal v /\ SoundTypeRes r v R)
      \/ res = rError
      \/ res = rTimeout.
Proof with crush.
  intros Γ e R r n res Htype Hsat Hwfv Hvalof.
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

  
