From Coq Require Import ssreflect.
(* From HoTT Require Import HoTT. *)
From Trocq Require Import Trocq.

Set Universe Polymorphism.
Set Primitive Projections.
Set Asymmetric Patterns.


(** Redefining vectors (probably already somewhere...) *)

Inductive vect {A : Type} : nat -> Type :=
  | ε : vect 0
  | cons {n} : A -> vect n -> vect (S n).
Arguments vect : clear implicits.

Inductive vectε {A : Type} {P : A -> Type} : forall (n : nat), vect A n -> Type :=
  | εε : vectε 0 ε
  | consε {n a v} : P a -> vectε n v -> vectε (S n) (cons a v).
Arguments vectε : clear implicits.
Arguments vectε {_} _ {_} _.

Definition map_vect {A B} (f : A -> B) :=
  fix aux  {n} (v : vect A n) : vect B n :=
  match v with
  | ε => ε
  | cons _ a v => cons (f a) (aux v)
  end.

Definition dmap_vect {A B} (f : forall a : A, B a) :=
  fix aux {n} (v : vect A n) : vectε B v :=
  match v with
  | ε => εε
  | cons _ a v => consε (f a) (aux v)
  end.

Definition hd {A n} (v : vect A (S n)) : A :=
  match v with | cons _ a _ => a end.

Definition tl {A n} (v : vect A (S n)) : vect A n :=
  match v with | cons _ _ v => v end.

Definition dhd {A B n} {v : vect A (S n)} (vε : vectε B v) : B (hd v) :=
  match vε in @vectε _ _ n v return
        match n as n return vect A n -> Type with
        | 0%nat => fun _ => unit
        | S n => fun v => B (hd v) end v with
  | εε => tt
  | consε _ _ _ b _ => b
  end.

Definition dtl {A B n} {v : vect A (S n)} (vε : vectε B v) : vectε B (tl v) :=
  match vε in @vectε _ _ n v return
        match n as n return vect A n -> Type with
        | 0%nat => fun _ => unit
        | S n => fun v => vectε B (tl v) end v with
  | εε => tt
  | consε _ _ _ _ bs => bs
  end.


Lemma vect_ext {A n} (v : vect A n) :
  match n as n return vect A n -> Type with
  | 0%nat => fun v => v = ε
  | S n => fun v => v = cons (hd v) (tl v)
  end v.
Proof. now destruct v. Qed.

Lemma empty_ext {A} (v : vect A 0) : v = ε.
Proof. apply: vect_ext v. Qed.

Lemma cons_ext {A n} (v : vect A (S n)) : v = cons (hd v) (tl v).
Proof. apply: vect_ext v. Qed.





(** First order single-sorted finitary signatures *)

Record sig := { ops : Type ; ar : ops -> nat ; }.

(* (Generic) Terms on a signature *)
Unset Elimination Schemes.
Inductive tm {s : sig} {A : Type} :=
| var : A -> tm
| op (op : s.(ops)) (args : vect tm (s.(ar) op)) : tm.
Set Elimination Schemes.
Arguments tm : clear implicits.

(* Induction for terms (to deal with the nested occurence of vect) *)
Definition tm_rect (s : sig) (A : Type) (P : tm s A -> Type)
  (hvar : forall a, P (var a))
  (hop : forall opi args, vectε P args -> P (op opi args)) :
  forall (t : tm s A), P t.
Proof.
  fix aux 1.
  intros [].
  - apply: hvar.
  - apply: hop; apply: dmap_vect; apply: aux.
Defined.

(* Substitution on generic terms *)
Definition sub {A B s} (f : A -> tm s B) :=
  fix aux (t : tm s A) {struct t} : tm s B :=
  match t with
    | var a => f a
    | op x args => op x (map_vect aux args)
  end.

(* Associativity of substitution *)
Lemma sub_assoc {s A B C} {f : A -> tm s B} {g : B -> tm s C} {t}:
  sub g (sub f t) = sub (sub g o f) t.
Proof.
  induction t using tm_rect; first reflexivity.
  cbn; apply: ap.
  induction X; first reflexivity.
  by rewrite /= IHX p.
Qed.

(* Concrete signature for monoids *)
Inductive monoid_ops := unit_op | mul_op.

Definition monoid : sig := {|
  ops := monoid_ops ;
  ar mop := match mop with
            | unit_op => 0%nat
            | mul_op => 2%nat
            end
                    |}.

(* Instantiation of the generic terms on the signature of monoids (with variables in nat) *)
Definition tm_monoid := tm monoid nat.


(* Concrete description of monoid terms *)

Inductive tm_monoid' :=
  | Var : nat -> tm_monoid'
  | Unit : tm_monoid'
  | Mul : tm_monoid' -> tm_monoid' -> tm_monoid'.


(* Equivalence between the two descriptions *)

Definition f : tm_monoid -> tm_monoid'.
Proof.
  intros x; induction x using tm_rect.
  - now apply: Var.
  - destruct opi.
    + exact Unit.
    + apply: Mul; [exact (dhd X)| exact (dhd (dtl X))].
Defined.

Definition g : tm_monoid' -> tm_monoid.
Proof.
  intro x; induction x as [n | | x1 ih1 x2 ih2 ].
  - exact (var n).
  - exact (op (s:=monoid) unit_op ε).
  - exact (op (s:=monoid) mul_op (cons ih1 (cons ih2 ε))).
Defined.

Lemma gf_id : forall x : tm_monoid, g (f x) = x.
Proof.
  intros x; induction x using tm_rect.
  + reflexivity.
  + destruct opi; first by rewrite /= [args]empty_ext.
    by rewrite [args]cons_ext [tl args]cons_ext /= (dhd X) (dhd (dtl X)) [tl (tl args)]empty_ext.
Qed.

Lemma fg_id : forall x : tm_monoid', f (g x) = x.
Proof.
  intros x; induction x as [n| |x1 ih1 x2 ih2].
  1,2: reflexivity.
  by rewrite /= ih1 ih2.
Qed.

Definition Param44_tm_monoid : Param44.Rel tm_monoid' tm_monoid.
Proof.
apply Iso.toParam; unshelve econstructor.
- exact: g.
- exact: f.
- exact: fg_id.
- exact: gf_id.
Defined.

Trocq Use Param44_nat Param44_tm_monoid.



(**  Trying to transfer substitution *)
Module TransferSub.
Definition subst' : forall (σ : nat -> tm_monoid') (t : tm_monoid'), tm_monoid'.
Proof.
  trocq. exact sub.
Defined.

Print subst'.

Eval cbn in subst' (fun _ => Unit) (Mul (Unit) (Var 0)).

Goal  (fun x => subst' (fun _ => Unit) (Mul (x) (Var 0)))  = fun x => x.
Proof.
  rewrite /=. (* No simplification *)
  rewrite /subst' /= -/subst'. (* No simplification ; too much to unfold *)
  Restart.
  cbn. (* Ugly *)
  change ((fun x => Mul (subst' (fun _ => Unit) x) Unit) = idmap). (* ideal result *)
Abort.

End TransferSub.

Module ByHand.

Definition subst' (σ : nat -> tm_monoid') (t : tm_monoid') : tm_monoid' :=
   f (sub (g o σ) (g t)).

Eval cbn in subst' (fun _ => Unit) (Mul (Unit) (Var 0)).

Goal  (fun x => subst' (fun _ => Unit) (Mul (x) (Var 0)))  = fun x => x.
Proof.
  rewrite /=. (* No simplification *)
  rewrite /subst' /= -/subst'. (* ok, but does not refold entirely *)
  Restart.
  cbn. (* Ugly *)
  change ((fun x => Mul (subst' (fun _ => Unit) x) Unit) = idmap). (* ideal result *)
Abort.

End ByHand.

(* The two approaches are convertible *)
Check idpath : ByHand.subst' = TransferSub.subst'.

(**  Defining substitution on the concrete representation and relating to the generic substitution *)

Fixpoint subst' (σ : nat -> tm_monoid') (t : tm_monoid') : tm_monoid' :=
   match t with
   | Var n => σ n
   | Unit => Unit
   | Mul t1 t2 => Mul (subst' σ t1) (subst' σ t2)
   end.

Definition sub0 := @sub nat nat monoid.

Lemma Param_subst'_sub
  σ' σ (σR : R_arrow Param44_nat Param44_tm_monoid σ' σ)
  t' t (tR : Param44_tm_monoid t' t):
  Param44_tm_monoid (subst' σ' t') (sub0 σ t).
Proof.
  induction t' in t, tR |- * ; apply Param44.R_in_map in tR;  rewrite /= in tR; rewrite -tR.
  - apply: σR. by apply: map_in_R_nat.
  - reflexivity.
  - rewrite /=.
    unshelve epose proof (ih1 := IHt'1 (g t'1) _); first by rewrite /= /graph.
    apply Param44.R_in_map in ih1; cbn in ih1.
    unshelve epose proof (ih2 := IHt'2 (g t'2) _); first by rewrite /= /graph.
    apply Param44.R_in_map in ih2; cbn in ih2.
    by rewrite  -ih1 -ih2 /graph /=.
Qed.

Trocq Use Param_subst'_sub.
Trocq Use Param10_paths Param01_paths.

(**  Trying to transfer substitution associativity *)
Set Printing Universes.

Lemma subst'_assoc {f g : nat -> tm_monoid'} {t : tm_monoid'} :
  subst' g (subst' f t) = subst' (fun x => subst' g (f x)) t.
Proof.
  revert f g t; trocq; intros; apply sub_assoc.
Qed.
