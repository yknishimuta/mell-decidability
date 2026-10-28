From Coq Require Import List Arith.Cantor Arith.PeanoNat Lia.
From Mell.Core Require Import FiniteTree.

Import ListNotations.

Record Codec (A : Type) : Type := {
  encode : A -> nat;
  decode : nat -> option A;
  decode_encode : forall value, decode (encode value) = Some value
}.

Arguments encode {A} _ _.
Arguments decode {A} _ _.
Arguments decode_encode {A} _ _.

Definition nat_codec : Codec nat :=
  {| encode := fun n => n;
     decode := fun n => Some n;
     decode_encode := fun _ => eq_refl |}.

Definition pair_encode {A B} (codecA : Codec A) (codecB : Codec B)
    (value : A * B) : nat :=
  Cantor.to_nat (encode codecA (fst value), encode codecB (snd value)).

Definition pair_decode {A B} (codecA : Codec A) (codecB : Codec B)
    (code : nat) : option (A * B) :=
  let '(codeA, codeB) := Cantor.of_nat code in
  match decode codecA codeA, decode codecB codeB with
  | Some valueA, Some valueB => Some (valueA, valueB)
  | _, _ => None
  end.

Lemma pair_decode_encode : forall A B (codecA : Codec A) (codecB : Codec B)
    value,
    pair_decode codecA codecB (pair_encode codecA codecB value) = Some value.
Proof.
  intros A B codecA codecB [valueA valueB].
  unfold pair_decode, pair_encode.
  rewrite Cantor.cancel_of_to; simpl.
  rewrite !decode_encode; reflexivity.
Qed.

Definition pair_codec {A B} (codecA : Codec A) (codecB : Codec B) :
    Codec (A * B) :=
  {| encode := pair_encode codecA codecB;
     decode := pair_decode codecA codecB;
     decode_encode := pair_decode_encode A B codecA codecB |}.

Lemma cantor_snd_lt_succ : forall code,
    snd (Cantor.of_nat code) < S code.
Proof.
  intro code.
  destruct (Cantor.of_nat code) as [left right] eqn:Hcode; simpl.
  pose proof (Cantor.to_nat_non_decreasing left right) as Hbound.
  assert (Cantor.to_nat (left, right) = code) as Hcancel.
  { rewrite <- Hcode. apply Cantor.cancel_to_of. }
  lia.
Qed.

Fixpoint list_encode {A} (codec : Codec A) (values : list A) : nat :=
  match values with
  | nil => 0
  | value :: values' =>
      S (Cantor.to_nat (encode codec value, list_encode codec values'))
  end.

Fixpoint list_decode_fuel {A} (codec : Codec A) (fuel code : nat) :
    option (list A) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match code with
      | 0 => Some nil
      | S packed =>
          let '(head_code, tail_code) := Cantor.of_nat packed in
          match decode codec head_code,
                list_decode_fuel codec fuel' tail_code with
          | Some value, Some values => Some (value :: values)
          | _, _ => None
          end
      end
  end.

Definition list_decode {A} (codec : Codec A) (code : nat) : option (list A) :=
  list_decode_fuel codec (S code) code.

Lemma list_decode_fuel_encode : forall A (codec : Codec A) values fuel,
    list_encode codec values < fuel ->
    list_decode_fuel codec fuel (list_encode codec values) = Some values.
Proof.
  intros A codec values; induction values as [|value values IH].
  - intros fuel Hfuel. destruct fuel; [lia | reflexivity].
  - intros fuel Hfuel. destruct fuel as [|fuel]; [lia |].
    cbn [list_encode list_decode_fuel] in Hfuel |- *.
    rewrite Cantor.cancel_of_to, decode_encode.
    rewrite IH; [reflexivity |].
    pose proof (Cantor.to_nat_non_decreasing
      (encode codec value) (list_encode codec values)).
    lia.
Qed.

Lemma list_decode_encode : forall A (codec : Codec A) values,
    list_decode codec (list_encode codec values) = Some values.
Proof.
  intros A codec values.
  unfold list_decode.
  apply list_decode_fuel_encode; lia.
Qed.

Definition list_codec {A} (codec : Codec A) : Codec (list A) :=
  {| encode := list_encode codec;
     decode := list_decode codec;
     decode_encode := list_decode_encode A codec |}.

Fixpoint tree_encode (tree : FiniteTree nat nat) : nat :=
  match tree with
  | tree_leaf label => 2 * label
  | tree_node label children =>
      S (2 * Cantor.to_nat (label, forest_encode children))
  end
with forest_encode (forest : FiniteForest nat nat) : nat :=
  match forest with
  | forest_nil => 0
  | forest_cons tree forest' =>
      S (Cantor.to_nat (tree_encode tree, forest_encode forest'))
  end.

Fixpoint tree_decode_fuel (fuel code : nat) : option (FiniteTree nat nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Nat.even code then Some (tree_leaf (Nat.div2 code))
      else
        let '(label, children_code) := Cantor.of_nat (Nat.div2 code) in
        match forest_decode_fuel fuel' children_code with
        | Some children => Some (tree_node label children)
        | None => None
        end
  end
with forest_decode_fuel (fuel code : nat) : option (FiniteForest nat nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match code with
      | 0 => Some forest_nil
      | S packed =>
          let '(tree_code, forest_code) := Cantor.of_nat packed in
          match tree_decode_fuel fuel' tree_code,
                forest_decode_fuel fuel' forest_code with
          | Some tree, Some forest => Some (forest_cons tree forest)
          | _, _ => None
          end
      end
  end.

Fixpoint tree_depth (tree : FiniteTree nat nat) : nat :=
  match tree with
  | tree_leaf _ => 1
  | tree_node _ children => S (forest_depth children)
  end
with forest_depth (forest : FiniteForest nat nat) : nat :=
  match forest with
  | forest_nil => 0
  | forest_cons tree forest' =>
      S (Nat.max (tree_depth tree) (forest_depth forest'))
  end.

Lemma tree_forest_decode_fuel_encode :
  (forall tree fuel, tree_depth tree < fuel ->
    tree_decode_fuel fuel (tree_encode tree) = Some tree) /\
  (forall forest fuel, forest_depth forest < fuel ->
    forest_decode_fuel fuel (forest_encode forest) = Some forest).
Proof.
  apply FiniteTree_FiniteForest_ind.
  - intros label fuel Hfuel. destruct fuel; [lia |].
    cbn [tree_depth tree_encode tree_decode_fuel].
    rewrite Nat.even_mul, Nat.div2_double; reflexivity.
  - intros label children IH fuel Hfuel. destruct fuel; [lia |].
    cbn [tree_depth tree_encode tree_decode_fuel] in Hfuel |- *.
    replace (Nat.even (S (2 * Cantor.to_nat
      (label, forest_encode children)))) with false.
    2: { rewrite Nat.even_succ, Nat.odd_mul, Nat.odd_2; reflexivity. }
    rewrite Nat.div2_succ_double, Cantor.cancel_of_to.
    rewrite IH; [reflexivity | lia].
  - intros fuel Hfuel. destruct fuel; [lia | reflexivity].
  - intros tree IHtree forest IHforest fuel Hfuel.
    destruct fuel; [lia |].
    cbn [forest_depth] in Hfuel.
    unfold forest_encode at 1.
    unfold forest_decode_fuel at 1.
    rewrite Cantor.cancel_of_to.
    rewrite IHtree by lia.
    rewrite IHforest by lia.
    reflexivity.
Qed.

Lemma tree_forest_depth_encode_bound :
  (forall tree, tree_depth tree <= S (tree_encode tree)) /\
  (forall forest, forest_depth forest <= S (forest_encode forest)).
Proof.
  apply FiniteTree_FiniteForest_ind.
  - intros; cbn; lia.
  - intros label children IH; cbn.
    pose proof (Cantor.to_nat_non_decreasing label (forest_encode children)).
    lia.
  - cbn; lia.
  - intros tree IHtree forest IHforest; cbn.
    pose proof (Cantor.to_nat_non_decreasing
      (tree_encode tree) (forest_encode forest)).
    apply le_n_S, Nat.max_lub.
    + exact (Nat.le_trans _ _ _ IHtree (le_n_S _ _ (Nat.le_trans _ _ _
        (Nat.le_add_l _ _) H))).
    + exact (Nat.le_trans _ _ _ IHforest (le_n_S _ _ (Nat.le_trans _ _ _
        (Nat.le_add_r _ _) H))).
Qed.

Definition tree_decode (code : nat) : option (FiniteTree nat nat) :=
  tree_decode_fuel (S (S code)) code.

Definition forest_decode (code : nat) : option (FiniteForest nat nat) :=
  forest_decode_fuel (S (S code)) code.

Lemma tree_decode_encode : forall tree,
    tree_decode (tree_encode tree) = Some tree.
Proof.
  intro tree. unfold tree_decode.
  apply tree_forest_decode_fuel_encode.
  pose proof (proj1 tree_forest_depth_encode_bound tree); lia.
Qed.

Lemma forest_decode_encode : forall forest,
    forest_decode (forest_encode forest) = Some forest.
Proof.
  intro forest. unfold forest_decode.
  apply tree_forest_decode_fuel_encode.
  pose proof (proj2 tree_forest_depth_encode_bound forest); lia.
Qed.

Definition tree_codec : Codec (FiniteTree nat nat) :=
  {| encode := tree_encode;
     decode := tree_decode;
     decode_encode := tree_decode_encode |}.

Definition forest_codec : Codec (FiniteForest nat nat) :=
  {| encode := forest_encode;
     decode := forest_decode;
     decode_encode := forest_decode_encode |}.
