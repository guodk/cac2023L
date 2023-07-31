(* 本文件为MK公理化集合论的预备逻辑部分，包括
  1. 引入逻辑公理排中律
  2. 证明一些常见逻辑性质
  3. 定义一些常用Ltac和Notation *)

(* 引进记号 *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' ∃ x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' 'λ' x .. y ']' , t").

(* 初等逻辑模块 *)

Module Logic.

Axiom classic : ∀ P, P \/ ~P.

Proposition peirce : ∀ P, (~P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Proposition notandor : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition inp : ∀ {P Q: Prop}, (P -> Q) -> (~Q) -> (~P).
Proof.
  intros; intro; auto.
Qed.

Lemma not_and_or : ∀ P Q:Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros; elim (classic P); auto.
Qed.

Lemma not_imply_elim : ∀ P Q:Prop, ~ (P -> Q) -> P.
Proof.
  intros; apply NNPP; red.
  intro; apply H; intro; absurd P; trivial.
Qed.

Lemma not_imply_elim2 : ∀ P Q:Prop, ~ (P -> Q) -> ~ Q.
Proof.
  tauto.
Qed.

Lemma imply_to_and : ∀ P Q:Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros; split.
  apply not_imply_elim with Q; trivial.
  apply not_imply_elim2 with P; trivial.
Qed.

(* 一些简单的策略 *)

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

(* 批处理条件或目标中"与"和"或"策略 *)

Ltac deand :=
  match goal with
   | H: ?a /\ ?b |- _ => destruct H; deand
   | _ => idtac
  end.

Ltac deor :=
  match goal with
   | H: ?a \/ ?b |- _ => destruct H; deor
   | _ => idtac 
  end.

Ltac deandG :=
  match goal with
    |- ?a /\ ?b => split; deandG
    | _ => idtac
  end.

End Logic.

Export Logic.