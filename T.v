Inductive empty := .

Inductive typ : Type :=
| typ_arr : typ -> typ -> typ
| typ_nat : typ.

Notation "τ --> σ" := (typ_arr τ σ) (at level 8, right associativity).

(* Binders are represented in nested abstract syntax.

   In short, terms are parametrized by the type X of their free variables.
   Then, e.g. when we open a lambda, its body is a [tm (option X)]: [None] is
   the additional variable bound by the lambda, and [Some x] is an other free
   variable of type X.

   It can be seen as a well-typed De Bruijn representation.
*)

Notation "^ f" := (option_map f)  (at level 5, right associativity).
Notation "^ X" := (option X) : type_scope.

Inductive tm (X : Type) : Type :=
| tm_var : X -> tm X
| tm_app : tm X -> tm X -> tm X
| tm_lam : typ -> tm ^X -> tm X
| tm_zero : tm X
| tm_succ : tm X -> tm X
| tm_nrec : typ -> tm X -> tm ^^X -> tm X -> tm X.

Notation "# x" := (tm_var _ x) (at level 10).
Notation "t $ u" := (tm_app _ t u) (at level 10).
Notation "'λ' [ τ ] u" := (tm_lam _ τ u) (at level 10).
Notation Z := (tm_zero _).
Notation S := (tm_succ _).
Notation "'rec' [ τ ] ( e0 , e1 )" := (tm_nrec _ τ e0 e1) (at level 10).

Reserved Notation "% f" (at level 5, right associativity).

(* Renaming *)
Fixpoint tm_map {X Y : Type} (f : X -> Y) (t : tm X) : tm Y :=
  match t with
  | # x => # (f x)
  | u $ v => (%f u) $ (%f v)
  | λ [τ] u => λ [τ] (%^f u)
  | Z => Z
  | S u => S (%f u)
  | rec [τ] (e0, e1) e => rec [τ] (%f e0, %^^f e1) (%f e)
  end
where "% f" := (tm_map f).

Definition f_lift {X Y : Type} (f : X -> tm Y) : ^X -> tm ^Y :=
  fun o =>
    match o with
    | None => # None
    | Some t => %Some (f t)
    end.

(* Parallel substitution *)
Fixpoint tm_bind {X Y : Type} (t : tm X) (f : X -> tm Y) : tm Y :=
  match t with
  | # x => f x
  | u $ v => (tm_bind u f) $ (tm_bind v f)
  | λ [τ] u => λ [τ] (tm_bind u (f_lift f))
  | Z => Z
  | S u => S (tm_bind u f)
  | rec [τ] (e0, e1) e => rec [τ] (tm_bind e0 f, tm_bind e1 (f_lift (f_lift f))) (tm_bind e f)
  end.

Notation "'lift'" := %(@Some _) (at level 1).

(* Substitution of the "first" free variable *)
Definition tm_head_subst {X : Type} (t : tm ^X) (u : tm X) : tm X :=
  tm_bind t (fun x => match x with None => u | Some u => # u end).

Notation "t <- u" := (tm_head_subst t u) (at level 50).

(* Substitution of the two first free variables *)
Definition tm_head_subst2 {X : Type} (t : tm ^^X) (u : tm X) (v : tm X) : tm X :=
  tm_bind t (fun x => match x with None => u | Some None => v | Some (Some u) => # u end).

Notation "t <<- ( u , v )" := (tm_head_subst2 t u v) (at level 50).

(* Small-step operational semantics *)

(* This is a bit meh *)
Fixpoint is_value {X : Type} (t : tm X) : bool :=
  match t with
  | λ [_] _ | Z => true
  | S u => is_value u
  | _  => false
  end.

Definition value {X} (t : tm X) : Prop := is_true (is_value t).

Lemma value_succ {X : Type} : forall (t : tm X), value t <-> value (S t).
Proof.
  intros. split; unfold value, is_value, is_true in *; tauto.
Qed.

Ltac value := compute; reflexivity.
Ltac valueH H := compute in H; congruence.

Inductive step {X : Type} : tm X -> tm X -> Prop :=
| step_beta : forall (τ : typ) (v : tm X) (u : tm ^X),
    value v ->
    step ((λ [τ] u) $ v) (u <- v)
| step_app1 : forall (u1 u2 v : tm X),
    step u1 u2 ->
    step (u1 $ v) (u2 $ v)
| step_app2 : forall (u v1 v2 : tm X),
    value u ->
    step v1 v2 ->
    step (u $ v1) (u $ v2)
| step_succ : forall (u1 u2 : tm X),
    step u1 u2 ->
    step (S u1) (S u2)
| step_rec : forall τ (e0 : tm X) (e1 : tm ^^X) (e e' : tm X),
    step e e' ->
    step (rec [τ] (e0, e1) e) (rec [τ] (e0, e1) e')
| step_rec_zero : forall τ (e0 : tm X) (e1 : tm ^^X),
    step (rec [τ] (e0, e1) Z) e0
| step_rec_succ : forall τ (e0 : tm X) (e1 : tm ^^X) (e : tm X),
    value e ->
    step (rec [τ] (e0, e1) (S e)) (e1 <<- (rec [τ] (e0, e1) e, e)).

(* Type-system *)

(* A typing environment *)
Definition env X := X -> typ.

Definition env_empty : env empty := empty_rect _.

Definition env_cons {X : Type} (τ : typ) (Γ : env X) : env ^X :=
  fun x =>
    match x with
    | None => τ
    | Some y => Γ y
    end.

Notation "Γ & τ" := (env_cons τ Γ) (at level 1).

Reserved Notation "Γ |- t :~ τ" (at level 60).

Inductive typing {X : Type} (Γ : env X) : tm X -> typ -> Prop :=
| typing_var : forall x,
    Γ |- # x :~ Γ x
| typing_app : forall u v τ σ,
    Γ |- u :~ τ --> σ ->
    Γ |- v :~ τ ->
    Γ |- (u $ v) :~ σ
| typing_lam : forall u τ σ,
    (Γ & τ) |- u :~ σ ->
    Γ |- (λ [τ] u) :~ (τ --> σ)
| typing_zero :
    Γ |- Z :~ typ_nat
| typing_succ : forall u,
    Γ |- u :~ typ_nat ->
    Γ |- (S u) :~ typ_nat
| typing_rec : forall τ e0 e1 e,
    Γ |- e0 :~ τ ->
    (Γ & typ_nat & τ) |- e1 :~ τ ->
    Γ |- e :~ typ_nat ->
    Γ |- (rec [τ] (e0, e1) e) :~ τ
where "Γ |- t :~ τ" := (@typing _ Γ t τ).

(* Progress *)

Lemma typing_nat_value {X : Type} : forall (Γ : env X) e,
  value e ->
  Γ |- e :~ typ_nat ->
  e = Z \/ (exists e', value e' /\ e = S e').
Proof.
  intros ? ? Hv H.
  inversion H; subst; try (valueH Hv).
  - left. reflexivity.
  - right. eexists. split.
    { apply value_succ. eassumption. }
    { reflexivity. }
Qed.

Lemma progress : forall (t : tm empty) (τ : typ),
  env_empty |- t :~ τ ->
  value t \/ exists t', step t t'.
Proof.
  generalize env_empty. remember (empty : Type).
  induction 1; subst X; try tauto; try (left; value).
  { right.
    specialize (IHtyping1 eq_refl). specialize (IHtyping2 eq_refl).
    destruct u as [?|?|?|?|?| τ' e0 e1 e ].
    - inversion H. tauto.
    - destruct IHtyping1 as [ Hv | [t' Ht'] ]; [ valueH Hv |].
      eexists. apply step_app1. apply Ht'.
    - destruct IHtyping2 as [ ? | [t' Ht'] ].
      { eexists. apply step_beta. assumption. }
      { eexists. apply step_app2. value. eassumption. }
    - inversion H.
    - inversion H.
    - destruct IHtyping1 as [ Hv | [t' Ht'] ]; [ valueH Hv |].
      eexists. apply step_app1. eassumption. }
  { specialize (IHtyping eq_refl).
    destruct IHtyping as [ ? | [t' Ht'] ].
    - left. apply value_succ. assumption.
    - right. eexists. apply step_succ. eassumption. }
  { right.
    specialize (IHtyping1 eq_refl). specialize (IHtyping3 eq_refl). clear IHtyping2. (* humm *)
    destruct IHtyping3 as [ Hv | [t' Ht'] ].
    - { destruct (typing_nat_value _ _ Hv H1) as [ HeZ | [e' [Hve' HeS]] ].
        - rewrite HeZ in *. eexists. apply step_rec_zero.
        - rewrite HeS in *. eexists. apply step_rec_succ. assumption. }
    - eexists. apply step_rec. eassumption. }
Qed.

(* Substitution preserves typing *)

Lemma weakening :
  forall (X : Type) (Γ : env X) (t : tm X) (τ : typ),
  Γ |- t :~ τ ->
  forall Y (f : X -> Y) Γ', (forall x, Γ' (f x) = Γ x) ->
  Γ' |- %f t :~ τ.
Proof with auto.
  do 4 intro. intro H. induction H; simpl; intros ? ? ? W; try constructor...
  - rewrite <-W. constructor.
  - econstructor. apply IHtyping1... apply IHtyping2...
  - apply IHtyping. intros [|]; simpl...
  - apply IHtyping2. intros [[|]|]; simpl...
Qed.

Lemma weakening_one :
  forall (X : Type) (Γ : env X) (t : tm X) (τ σ : typ),
  Γ |- t :~ τ ->
  Γ & σ |- lift t :~ τ.
Proof.
  intros. apply weakening with Γ. assumption. reflexivity.
Qed.

Lemma substitution :
  forall (X : Type) (Γ : env X) (t : tm X) (τ : typ),
    Γ |- t :~ τ ->
    forall (Y : Type) (f : X -> tm Y) Γ',
      (forall x, Γ' |- f x :~ Γ x) ->
      Γ' |- (tm_bind t f) :~ τ.
Proof with auto.
  intros X Γ t τ H. induction H; intros ? ? ? Hf; simpl; try constructor...
  - apply typing_app with τ.
    + apply IHtyping1...
    + apply IHtyping2...
  - apply IHtyping. intros [|]; simpl; try constructor.
    apply weakening_one...
  - apply IHtyping2. intros [[|]|]; simpl; try constructor.
    do 2 apply weakening_one...
Qed.

(* Reduction preserves typing *)

Lemma preservation : forall (X : Type) (t t' : tm X) (Γ : env X) (τ : typ),
  Γ |- t :~ τ ->
  step t t' ->
  Γ |- t' :~ τ.
Proof with eauto.
  do 5 intro. intro H. revert t'. induction H; intros t' Hstep; try (solve [ inversion Hstep ]).
  { inversion Hstep; subst.
    - inversion H; subst. eapply substitution. apply H2.
      intros [|]. simpl. constructor. simpl. assumption.
    - econstructor...
    - econstructor... }
  { inversion Hstep; subst. constructor... }
  { inversion Hstep; subst.
    - constructor...
    - assumption.
    - eapply substitution. eassumption.
      inversion H1; subst.
      intros [[|]|]; simpl. constructor. assumption. constructor... }
Qed.