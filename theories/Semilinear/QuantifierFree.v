From Coq Require Import List Vector VectorSpec ZArith Znumtheory Bool Lia
  Ring Classical_Prop.
From MiniCooper Require Import Constant Theory.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Formula LinearEquations.

Import ListNotations.
Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Fixpoint mc_term_scoped (bound : nat) (term : MC.term) : Prop :=
  match term with
  | MC.TSummand _ variable tail =>
      (variable < bound)%nat /\ mc_term_scoped bound tail
  | MC.TConstant _ => True
  end.

Definition qf_well_scoped (bound : nat) (formula : MC.formula) : Prop :=
  MC.all (fun _ term => mc_term_scoped bound term) formula.

Definition nat_environment {d} (value : NVec d) : MC.environment :=
  fun variable => Z.of_nat (vector_entry value variable).

Inductive QFPrimitive : Type :=
| PrimEq : MC.term -> QFPrimitive
| PrimPos : Z -> Z -> MC.term -> QFPrimitive
| PrimDiv : Z -> MC.term -> QFPrimitive
| PrimRem : Z -> Z -> MC.term -> QFPrimitive.

Definition primitive_semantics (cenv env : MC.environment)
    (primitive : QFPrimitive) : Prop :=
  match primitive with
  | PrimEq term => MC.interpret_term cenv env term = 0
  | PrimPos scale offset term =>
      0 < scale * MC.interpret_term cenv env term + offset
  | PrimDiv divisor term =>
      (divisor | MC.interpret_term cenv env term)
  | PrimRem modulus residue term =>
      exists quotient,
        MC.interpret_term cenv env term = modulus * quotient + residue
  end.

Definition QFBranch := list QFPrimitive.
Definition QFDNF := list QFBranch.

Definition branch_semantics cenv env (branch : QFBranch) : Prop :=
  List.Forall (primitive_semantics cenv env) branch.

Definition dnf_semantics cenv env (dnf : QFDNF) : Prop :=
  exists branch, List.In branch dnf /\ branch_semantics cenv env branch.

Definition nonzero_residues (modulus : Z) : list Z :=
  List.filter (fun residue => negb (Z.eqb residue 0)) (MC.interval modulus).

Lemma in_nonzero_residues : forall modulus residue,
    0 < modulus ->
    (List.In residue (nonzero_residues modulus) <-> 0 < residue < modulus).
Proof.
  intros modulus residue Hmodulus. unfold nonzero_residues.
  rewrite filter_In, MC.In_interval. rewrite Bool.negb_true_iff, Z.eqb_neq.
  lia.
Qed.
Definition positive_atom_dnf (predicate : MC.predicate)
    (term : MC.term) : QFDNF :=
  match predicate with
  | MC.Eq => [[PrimEq term]]
  | MC.Lt => [[PrimPos 1 0 term]]
  | MC.Dv divisor => [[PrimDiv divisor term]]
  end.

Definition negative_atom_dnf (predicate : MC.predicate)
    (term : MC.term) : QFDNF :=
  match predicate with
  | MC.Eq => [[PrimPos 1 0 term]; [PrimPos (-1) 0 term]]
  | MC.Lt => [[PrimPos (-1) 1 term]]
  | MC.Dv divisor =>
      if Z.eq_dec divisor 0 then
        [[PrimPos 1 0 term]; [PrimPos (-1) 0 term]]
      else
        List.map (fun residue => [PrimRem (Z.abs divisor) residue term])
          (nonzero_residues (Z.abs divisor))
  end.

Definition dnf_and (left right : QFDNF) : QFDNF :=
  List.flat_map (fun left_branch =>
    List.map (fun right_branch => left_branch ++ right_branch) right) left.

Fixpoint positive_dnf (formula : MC.formula) : QFDNF :=
  match formula with
  | MC.FAtom predicate term => positive_atom_dnf predicate term
  | MC.FFalse => []
  | MC.FTrue => [[]]
  | MC.FAnd lhs rhs => dnf_and (positive_dnf lhs) (positive_dnf rhs)
  | MC.FOr lhs rhs => positive_dnf lhs ++ positive_dnf rhs
  | MC.FNot body => negative_dnf body
  | MC.FExists _ => []
  end
with negative_dnf (formula : MC.formula) : QFDNF :=
  match formula with
  | MC.FAtom predicate term => negative_atom_dnf predicate term
  | MC.FFalse => [[]]
  | MC.FTrue => []
  | MC.FAnd lhs rhs => negative_dnf lhs ++ negative_dnf rhs
  | MC.FOr lhs rhs => dnf_and (negative_dnf lhs) (negative_dnf rhs)
  | MC.FNot body => positive_dnf body
  | MC.FExists _ => []
  end.

Fixpoint nnf_dnf (formula : MC.formula) : QFDNF :=
  match formula with
  | MC.FAtom predicate term => positive_atom_dnf predicate term
  | MC.FFalse => []
  | MC.FTrue => [[]]
  | MC.FAnd lhs rhs => dnf_and (nnf_dnf lhs) (nnf_dnf rhs)
  | MC.FOr lhs rhs => nnf_dnf lhs ++ nnf_dnf rhs
  | MC.FNot (MC.FAtom predicate term) => negative_atom_dnf predicate term
  | MC.FNot _ | MC.FExists _ => []
  end.

Definition formula_dnf (formula : MC.formula) : QFDNF :=
  positive_dnf formula.

Lemma primitive_eq_correct : forall cenv env term,
    primitive_semantics cenv env (PrimEq term) <->
    MC.interpret_formula cenv env (MC.FAtom MC.Eq term).
Proof. intros; cbn. lia. Qed.

Lemma primitive_pos_correct : forall cenv env term,
    primitive_semantics cenv env (PrimPos 1 0 term) <->
    MC.interpret_formula cenv env (MC.FAtom MC.Lt term).
Proof.
  intros. cbn [primitive_semantics MC.interpret_formula
    MC.interpret_predicate]. rewrite Z.mul_1_l, Z.add_0_r. reflexivity.
Qed.

Lemma primitive_neg_eq_correct : forall cenv env term,
    dnf_semantics cenv env (negative_atom_dnf MC.Eq term) <->
    ~ MC.interpret_formula cenv env (MC.FAtom MC.Eq term).
Proof.
  intros cenv env term. unfold negative_atom_dnf, dnf_semantics.
  split.
  - intros [branch [[<-|[<-|[]]] Hbranch]];
      unfold branch_semantics in Hbranch; inversion Hbranch; subst;
      cbn [primitive_semantics MC.interpret_formula
        MC.interpret_predicate] in *; lia.
  - intro Hneq. cbn [MC.interpret_formula MC.interpret_predicate] in Hneq.
    destruct (Z_lt_ge_dec 0 (MC.interpret_term cenv env term)) as [Hpos|Hnonpos].
    + exists [PrimPos 1 0 term]. split; [cbn; auto|].
      constructor; [cbn [primitive_semantics]; lia|constructor].
    + exists [PrimPos (-1) 0 term]. split; [cbn; auto|].
      constructor; [cbn [primitive_semantics]; lia|constructor].
Qed.

Lemma primitive_neg_lt_correct : forall cenv env term,
    dnf_semantics cenv env (negative_atom_dnf MC.Lt term) <->
    ~ MC.interpret_formula cenv env (MC.FAtom MC.Lt term).
Proof.
  intros cenv env term. unfold negative_atom_dnf, dnf_semantics.
  split.
  - intros [branch [[<-|[]] Hbranch]].
    unfold branch_semantics in Hbranch. inversion Hbranch; subst.
    cbn [primitive_semantics MC.interpret_formula
      MC.interpret_predicate] in *. lia.
  - intro Hnot. cbn [MC.interpret_formula MC.interpret_predicate] in Hnot.
    exists [PrimPos (-1) 1 term]. split; [cbn; auto|].
    constructor; [cbn [primitive_semantics]; lia|constructor].
Qed.

Lemma zero_divides_iff_zero : forall value, (0 | value) <-> value = 0.
Proof.
  intro value. split.
  - intros [quotient Heq]. nia.
  - intros ->. exists 0. ring.
Qed.

Lemma nonzero_divisor_remainders : forall divisor value,
    divisor <> 0 ->
    (~ (divisor | value) <->
      exists residue,
        List.In residue (nonzero_residues (Z.abs divisor)) /\
        exists quotient,
          value = Z.abs divisor * quotient + residue).
Proof.
  intros divisor value Hdivisor.
  assert (Hmodulus : 0 < Z.abs divisor) by now apply Z.abs_pos.
  split.
  - intro Hnot.
    exists (value mod Z.abs divisor). split.
    + apply in_nonzero_residues; [exact Hmodulus|].
      pose proof (Z.mod_pos_bound value (Z.abs divisor) Hmodulus).
      split; [|lia].
      assert (value mod Z.abs divisor <> 0).
      { intro Hzero. apply Hnot. apply Z.divide_abs_l.
        apply (proj1 (Z.mod_divide value (Z.abs divisor) ltac:(lia))).
        exact Hzero. }
      lia.
    + exists (value / Z.abs divisor).
      apply Z.div_mod. lia.
  - intros [residue [Hin [quotient Heq]]] Hdivide.
    apply in_nonzero_residues in Hin; [|exact Hmodulus].
    assert (Habsdivide : (Z.abs divisor | value)).
    { now apply Z.divide_abs_l. }
    destruct Habsdivide as [multiple Hmultiple].
    assert (Hresidue_divide : (Z.abs divisor | residue)).
    { exists (multiple - quotient). lia. }
    apply (proj2 (Z.mod_divide residue (Z.abs divisor) ltac:(lia))) in
      Hresidue_divide.
    rewrite Z.mod_small in Hresidue_divide by lia. lia.
Qed.

Lemma primitive_neg_div_correct : forall cenv env divisor term,
    dnf_semantics cenv env (negative_atom_dnf (MC.Dv divisor) term) <->
    ~ MC.interpret_formula cenv env (MC.FAtom (MC.Dv divisor) term).
Proof.
  intros cenv env divisor term. unfold negative_atom_dnf.
  destruct (Z.eq_dec divisor 0) as [->|Hnonzero].
  - change (dnf_semantics cenv env (negative_atom_dnf MC.Eq term) <->
      ~ MC.interpret_formula cenv env (MC.FAtom (MC.Dv 0) term)).
    rewrite primitive_neg_eq_correct.
    cbn [MC.interpret_formula MC.interpret_predicate].
    rewrite zero_divides_iff_zero. lia.
  - cbn [MC.interpret_formula MC.interpret_predicate].
    rewrite nonzero_divisor_remainders by exact Hnonzero.
    unfold dnf_semantics, branch_semantics. split.
    + intros [branch [Hinbranch Hsemantics]].
      apply in_map_iff in Hinbranch.
      destruct Hinbranch as [residue [Hbranch Hin]]. subst branch.
      inversion Hsemantics as [|primitive tail Hhead Htail]; subst.
      inversion Htail; subst.
      exists residue. split; [exact Hin|exact Hhead].
    + intros [residue [Hin Hremainder]].
      exists [PrimRem (Z.abs divisor) residue term]. split.
      * apply in_map_iff. exists residue. auto.
      * constructor; [exact Hremainder|constructor].
Qed.

Lemma singleton_dnf_semantics : forall cenv env primitive,
    dnf_semantics cenv env [[primitive]] <->
    primitive_semantics cenv env primitive.
Proof.
  intros cenv env primitive. unfold dnf_semantics, branch_semantics.
  split.
  - intros [branch [[<-|[]] Hbranch]].
    inversion Hbranch; subst. exact H1.
  - intro Hprimitive. exists [primitive]. split; [cbn; auto|].
    constructor; [exact Hprimitive|constructor].
Qed.

Lemma positive_atom_dnf_correct : forall cenv env predicate term,
    dnf_semantics cenv env (positive_atom_dnf predicate term) <->
    MC.interpret_formula cenv env (MC.FAtom predicate term).
Proof.
  intros cenv env predicate term. destruct predicate;
    cbn [positive_atom_dnf]; rewrite singleton_dnf_semantics;
    cbn [primitive_semantics MC.interpret_formula MC.interpret_predicate];
    try lia; reflexivity.
Qed.

Lemma negative_atom_dnf_correct : forall cenv env predicate term,
    dnf_semantics cenv env (negative_atom_dnf predicate term) <->
    ~ MC.interpret_formula cenv env (MC.FAtom predicate term).
Proof.
  intros. destruct predicate.
  - apply primitive_neg_eq_correct.
  - apply primitive_neg_lt_correct.
  - apply primitive_neg_div_correct.
Qed.

Lemma branch_semantics_app : forall cenv env left right,
    branch_semantics cenv env (left ++ right) <->
    branch_semantics cenv env left /\ branch_semantics cenv env right.
Proof.
  intros. unfold branch_semantics. apply List.Forall_app.
Qed.

Lemma dnf_and_correct : forall cenv env left right,
    dnf_semantics cenv env (dnf_and left right) <->
    dnf_semantics cenv env left /\ dnf_semantics cenv env right.
Proof.
  intros cenv env left right. unfold dnf_semantics, dnf_and.
  split.
  - intros [combined [Hincombined Hcombined]].
    apply in_flat_map in Hincombined.
    destruct Hincombined as [left_branch [Hleft Hinmap]].
    apply in_map_iff in Hinmap.
    destruct Hinmap as [right_branch [Heq Hright]]. subst combined.
    apply branch_semantics_app in Hcombined as [Hleft_sem Hright_sem].
    split; [exists left_branch|exists right_branch]; auto.
  - intros [[left_branch [Hleft Hleft_sem]]
      [right_branch [Hright Hright_sem]]].
    exists (left_branch ++ right_branch). split.
    + apply in_flat_map. exists left_branch. split; [exact Hleft|].
      apply in_map_iff. exists right_branch. auto.
    + apply branch_semantics_app. auto.
Qed.

Lemma dnf_append_correct : forall cenv env left right,
    dnf_semantics cenv env (left ++ right) <->
    dnf_semantics cenv env left \/ dnf_semantics cenv env right.
Proof.
  intros cenv env left right. unfold dnf_semantics. split.
  - intros [branch [Hin Hbranch]]. apply in_app_iff in Hin.
    destruct Hin; [left|right]; exists branch; auto.
  - intros [[branch [Hin Hbranch]]|[branch [Hin Hbranch]]].
    + exists branch. split; [apply in_app_iff; now left|exact Hbranch].
    + exists branch. split; [apply in_app_iff; now right|exact Hbranch].
Qed.

Lemma nnf_dnf_correct : forall cenv env formula,
    MC.nnf formula ->
    (dnf_semantics cenv env (nnf_dnf formula) <->
      MC.interpret_formula cenv env formula).
Proof.
  intros cenv env formula Hnnf. induction Hnnf; cbn [nnf_dnf].
  - apply positive_atom_dnf_correct.
  - apply negative_atom_dnf_correct.
  - rewrite dnf_and_correct, IHHnnf1, IHHnnf2. reflexivity.
  - rewrite dnf_append_correct, IHHnnf1, IHHnnf2. reflexivity.
  - split.
    + intro Hignored. constructor.
    + intro Htrue. exists []. split; [cbn; auto|constructor].
  - unfold dnf_semantics. split.
    + intros [branch [Hin _]]. inversion Hin.
    + contradiction.
Qed.

Lemma signed_dnf_correct : forall cenv env formula,
    MC.qf formula ->
    (dnf_semantics cenv env (positive_dnf formula) <->
      MC.interpret_formula cenv env formula) /\
    (dnf_semantics cenv env (negative_dnf formula) <->
      ~ MC.interpret_formula cenv env formula).
Proof.
  intros cenv env formula Hqf. induction Hqf; cbn [positive_dnf negative_dnf].
  - split; [apply positive_atom_dnf_correct|apply negative_atom_dnf_correct].
  - split.
    + unfold dnf_semantics. split.
      * intros [branch [Hin _]]. inversion Hin.
      * contradiction.
    + split.
      * intro Hdnf. intro Hfalse. exact Hfalse.
      * intro Hnotfalse. exists []. split; [cbn; auto|constructor].
  - split.
    + split; [intro Hdnf; constructor|].
      intro Htrue. exists []. split; [cbn; auto|constructor].
    + unfold dnf_semantics. split.
      * intros [branch [Hin _]]. inversion Hin.
      * intro Hnot. exfalso. apply Hnot. constructor.
  - destruct IHHqf1 as [Hpos1 Hneg1].
    destruct IHHqf2 as [Hpos2 Hneg2]. split.
    + rewrite dnf_and_correct, Hpos1, Hpos2. reflexivity.
    + rewrite dnf_append_correct, Hneg1, Hneg2.
      split.
      * intros [Hnot1|Hnot2] [H1 H2]; [exact (Hnot1 H1)|exact (Hnot2 H2)].
      * intro Hnot.
        destruct (classic (MC.interpret_formula cenv env f1)) as [H1|Hnot1].
        -- right. intro H2. apply Hnot. split; assumption.
        -- left. exact Hnot1.
  - destruct IHHqf1 as [Hpos1 Hneg1].
    destruct IHHqf2 as [Hpos2 Hneg2]. split.
    + rewrite dnf_append_correct, Hpos1, Hpos2. reflexivity.
    + rewrite dnf_and_correct, Hneg1, Hneg2. split.
      * intros [Hnot1 Hnot2] [H1|H2]; [exact (Hnot1 H1)|exact (Hnot2 H2)].
      * intro Hnot. split.
        -- intro H1. apply Hnot. now left.
        -- intro H2. apply Hnot. now right.
  - destruct IHHqf as [Hpos Hneg]. split.
    + exact Hneg.
    + rewrite Hpos.
      split.
      * intro Hvalue. intro Hnot. exact (Hnot Hvalue).
      * intro Hnotnot.
        destruct (classic (MC.interpret_formula cenv env f)); auto.
        exfalso. apply Hnotnot. assumption.
Qed.

Lemma formula_dnf_correct : forall cenv env formula,
    MC.qf formula ->
    (dnf_semantics cenv env (formula_dnf formula) <->
      MC.interpret_formula cenv env formula).
Proof.
  intros cenv env formula Hqf. unfold formula_dnf.
  exact (proj1 (signed_dnf_correct cenv env formula Hqf)).
Qed.

Lemma qf_well_scoped_qf : forall d formula,
    qf_well_scoped d formula -> MC.qf formula.
Proof.
  intros d formula Hscope. eapply MC.all_covariant; [|exact Hscope].
  auto.
Qed.

Fixpoint raw_dot (dimension : nat) (coefficients : nat -> Z)
    (values : nat -> nat) : Z :=
  match dimension with
  | 0%nat => 0
  | S tail =>
      coefficients 0%nat * Z.of_nat (values 0%nat) +
      raw_dot tail (fun index => coefficients (S index))
        (fun index => values (S index))
  end.

Lemma raw_dot_ext : forall dimension left right values,
    (forall index, (index < dimension)%nat -> left index = right index) ->
    raw_dot dimension left values = raw_dot dimension right values.
Proof.
  induction dimension as [|dimension IH]; intros left right values Heq; cbn.
  - reflexivity.
  - rewrite (Heq 0%nat ltac:(lia)). f_equal. apply IH.
    intros index Hindex. apply Heq. lia.
Qed.

Lemma raw_dot_values_ext : forall dimension coefficients left right,
    (forall index, (index < dimension)%nat -> left index = right index) ->
    raw_dot dimension coefficients left = raw_dot dimension coefficients right.
Proof.
  induction dimension as [|dimension IH]; intros coefficients left right Heq;
    cbn; [reflexivity|].
  rewrite (Heq 0%nat ltac:(lia)). f_equal. apply IH.
  intros index Hindex. apply Heq. lia.
Qed.

Lemma raw_dot_add : forall dimension left right values,
    raw_dot dimension (fun index => left index + right index) values =
    raw_dot dimension left values + raw_dot dimension right values.
Proof.
  induction dimension as [|dimension IH]; intros; cbn; [ring|].
  rewrite IH. ring.
Qed.

Lemma raw_dot_scale : forall dimension scale coefficients values,
    raw_dot dimension (fun index => scale * coefficients index) values =
    scale * raw_dot dimension coefficients values.
Proof.
  induction dimension as [|dimension IH]; intros; cbn; [ring|].
  rewrite IH. ring.
Qed.

Definition delta_coefficient (position : nat) (coefficient : Z) : nat -> Z :=
  fun index => if Nat.eqb index position then coefficient else 0.

Lemma raw_dot_zero : forall dimension values,
    raw_dot dimension (fun _ => 0) values = 0.
Proof.
  induction dimension as [|dimension IH]; intros values; cbn; [reflexivity|].
  rewrite IH. ring.
Qed.

Lemma raw_dot_delta : forall dimension position coefficient values,
    (position < dimension)%nat ->
    raw_dot dimension (delta_coefficient position coefficient) values =
    coefficient * Z.of_nat (values position).
Proof.
  induction dimension as [|dimension IH]; intros position coefficient values Hlt;
    [lia|].
  destruct position as [|position]; cbn [raw_dot].
  - unfold delta_coefficient. cbn.
    rewrite raw_dot_zero, Z.add_0_r. reflexivity.
  - unfold delta_coefficient at 1. cbn.
    transitivity (raw_dot dimension (delta_coefficient position coefficient)
      (fun index => values (S index))).
    + apply raw_dot_ext. intros index Hindex.
      unfold delta_coefficient. cbn. reflexivity.
    + rewrite IH by lia. reflexivity.
Qed.

Fixpoint mc_term_coefficients (term : MC.term) (variable : nat) : Z :=
  match term with
  | MC.TSummand coefficient position tail =>
      (if Nat.eqb variable position then coefficient else 0) +
      mc_term_coefficients tail variable
  | MC.TConstant _ => 0
  end.

Fixpoint mc_term_constant (cenv : MC.environment) (term : MC.term) : Z :=
  match term with
  | MC.TSummand _ _ tail => mc_term_constant cenv tail
  | MC.TConstant constant => MiniCooper.Constant.interpret_constant cenv constant
  end.

Lemma mc_term_linearize : forall bound cenv values term,
    mc_term_scoped bound term ->
    MC.interpret_term cenv (fun variable => Z.of_nat (values variable)) term =
      raw_dot bound (mc_term_coefficients term) values +
      mc_term_constant cenv term.
Proof.
  induction term as [coefficient position tail IH|constant]; intros Hscope.
  - cbn in Hscope. destruct Hscope as [Hposition Htail].
    cbn [MC.interpret_term mc_term_constant].
    assert (Hdot : raw_dot bound
        (mc_term_coefficients (MC.TSummand coefficient position tail)) values =
      raw_dot bound (fun variable =>
        delta_coefficient position coefficient variable +
        mc_term_coefficients tail variable) values).
    { apply raw_dot_ext. intros variable Hvariable.
      cbn [mc_term_coefficients]. unfold delta_coefficient. reflexivity. }
    rewrite Hdot, raw_dot_add, raw_dot_delta by exact Hposition.
    rewrite IH by exact Htail. ring.
  - cbn [MC.interpret_term mc_term_coefficients mc_term_constant].
    rewrite raw_dot_zero. ring.
Qed.

Definition RawEquation := ((nat -> Z) * Z)%type.

Definition equation_holds (dimension : nat) (values : nat -> nat)
    (equation : RawEquation) : Prop :=
  raw_dot dimension (fst equation) values = snd equation.

Definition system_holds (dimension : nat) (values : nat -> nat)
    (system : list RawEquation) : Prop :=
  List.Forall (equation_holds dimension values) system.

Fixpoint row_of_coefficients (dimension : nat)
    (coefficients : nat -> Z) : ZVec dimension :=
  match dimension with
  | 0%nat => @Vector.nil Z
  | S tail => @Vector.cons Z (coefficients 0%nat) tail
      (row_of_coefficients tail (fun index => coefficients (S index)))
  end.

Fixpoint system_matrix (dimension : nat) (system : list RawEquation) :
    ZMatrix (List.length system) dimension :=
  match system with
  | [] => @Vector.nil (ZVec dimension)
  | equation :: tail =>
      @Vector.cons (ZVec dimension) (row_of_coefficients dimension (fst equation))
        (List.length tail) (system_matrix dimension tail)
  end.

Fixpoint system_constant (system : list RawEquation) :
    ZVec (List.length system) :=
  match system with
  | [] => @Vector.nil Z
  | equation :: tail =>
      @Vector.cons Z (snd equation) (List.length tail) (system_constant tail)
  end.

Lemma row_of_coefficients_correct : forall dimension coefficients value,
    zrow_apply (row_of_coefficients dimension coefficients) value =
    raw_dot dimension coefficients (fun index => vector_entry value index).
Proof.
  induction dimension as [|dimension IH]; intros coefficients value.
  - refine (Vector.case0 (fun value =>
      zrow_apply (row_of_coefficients 0 coefficients) value =
      raw_dot 0 coefficients (fun index => vector_entry value index)) _ value).
    reflexivity.
  - refine (Vector.caseS' value (fun value =>
      zrow_apply (row_of_coefficients (S dimension) coefficients) value =
      raw_dot (S dimension) coefficients
        (fun index => vector_entry value index)) _).
    intros head tail. cbn [row_of_coefficients zrow_apply raw_dot].
    rewrite IH. reflexivity.
Qed.

Lemma system_matrix_correct : forall dimension system value,
    LinearSolution (system_matrix dimension system) (system_constant system) value
    <-> system_holds dimension (fun index => vector_entry value index) system.
Proof.
  intros dimension system. induction system as [|equation tail IH]; intro value;
    cbn [LinearSolution matrix_apply system_holds system_matrix system_constant].
  - split; intro Hempty; [constructor|reflexivity].
  - unfold LinearSolution, system_holds. cbn [matrix_apply].
    split.
    + intro Hequality. apply Vector.cons_inj in Hequality as [Hhead Htail].
      constructor.
      * unfold equation_holds. rewrite <- row_of_coefficients_correct.
        exact Hhead.
      * apply (proj1 (IH value)). exact Htail.
    + intro Hsystem. inversion Hsystem as [|head tail' Hhead Htail]; subst.
      assert (Hhead' : zrow_apply
          (row_of_coefficients dimension (fst equation)) value = snd equation).
      { rewrite row_of_coefficients_correct. exact Hhead. }
      pose proof (proj2 (IH value) Htail) as Htail'.
      unfold matrix_apply. cbn.
      rewrite Hhead', Htail'. reflexivity.
Qed.

Definition primitive_diophantine (cenv env : MC.environment)
    (primitive : QFPrimitive) (first second : nat) : Prop :=
  match primitive with
  | PrimEq term => MC.interpret_term cenv env term = 0
  | PrimPos scale offset term =>
      scale * MC.interpret_term cenv env term + offset =
        1 + Z.of_nat first
  | PrimDiv divisor term =>
      MC.interpret_term cenv env term =
        divisor * (Z.of_nat first - Z.of_nat second)
  | PrimRem modulus residue term =>
      MC.interpret_term cenv env term =
        modulus * (Z.of_nat first - Z.of_nat second) + residue
  end.

Lemma signed_nat_difference : forall value : Z,
    exists positive negative : nat,
      value = Z.of_nat positive - Z.of_nat negative.
Proof.
  intro value. destruct (Z_le_gt_dec 0 value) as [Hnonnegative|Hnegative].
  - exists (Z.to_nat value), 0%nat. rewrite Z2Nat.id by lia. lia.
  - exists 0%nat, (Z.to_nat (- value)). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma primitive_diophantine_correct : forall cenv env primitive,
    primitive_semantics cenv env primitive <->
    exists first second, primitive_diophantine cenv env primitive first second.
Proof.
  intros cenv env primitive. destruct primitive as
    [term|scale offset term|divisor term|modulus residue term];
    cbn [primitive_semantics primitive_diophantine].
  - split; [intro H; exists 0%nat, 0%nat|intros [first [second H]]]; exact H.
  - split.
    + intro Hpositive.
      exists (Z.to_nat (scale * MC.interpret_term cenv env term + offset - 1)),
        0%nat.
      rewrite Z2Nat.id by lia. lia.
    + intros [first [second Heq]]. lia.
  - split.
    + intros [quotient Heq].
      destruct (signed_nat_difference quotient) as
        [positive [negative Hquotient]].
      exists positive, negative. lia.
    + intros [positive [negative Heq]].
      exists (Z.of_nat positive - Z.of_nat negative). nia.
  - split.
    + intros [quotient Heq].
      destruct (signed_nat_difference quotient) as
        [positive [negative Hquotient]].
      exists positive, negative. lia.
    + intros [positive [negative Heq]].
      exists (Z.of_nat positive - Z.of_nat negative). exact Heq.
Qed.

Definition primitive_term (primitive : QFPrimitive) : MC.term :=
  match primitive with
  | PrimEq term | PrimPos _ _ term | PrimDiv _ term | PrimRem _ _ term => term
  end.

Definition primitive_scoped (bound : nat) (primitive : QFPrimitive) : Prop :=
  mc_term_scoped bound (primitive_term primitive).

Definition branch_scoped (bound : nat) (branch : QFBranch) : Prop :=
  List.Forall (primitive_scoped bound) branch.

Definition dnf_scoped (bound : nat) (dnf : QFDNF) : Prop :=
  List.Forall (branch_scoped bound) dnf.

Lemma mc_term_coefficients_outside : forall bound term variable,
    mc_term_scoped bound term ->
    (bound <= variable)%nat ->
    mc_term_coefficients term variable = 0.
Proof.
  induction term as [coefficient position tail IH|constant];
    intros variable Hscope Houtside; cbn in *.
  - destruct Hscope as [Hposition Htail].
    destruct (variable =? position)%nat eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + rewrite IH by assumption. lia.
  - reflexivity.
Qed.

Lemma raw_dot_split : forall left right coefficients values,
    raw_dot (left + right) coefficients values =
      raw_dot left coefficients values +
      raw_dot right (fun index => coefficients (left + index)%nat)
        (fun index => values (left + index)%nat).
Proof.
  induction left as [|left IH]; intros right coefficients values; cbn.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma raw_dot_scoped_extend : forall bound extra term values,
    mc_term_scoped bound term ->
    raw_dot (bound + extra) (mc_term_coefficients term) values =
      raw_dot bound (mc_term_coefficients term) values.
Proof.
  intros bound extra term values Hscope. rewrite raw_dot_split.
  replace (raw_dot extra
      (fun index => mc_term_coefficients term (bound + index)%nat)
      (fun index => values (bound + index)%nat)) with 0.
  - lia.
  - transitivity (raw_dot extra (fun _ => 0) (fun index => values (bound + index)%nat)).
    + symmetry. apply raw_dot_zero.
    + apply raw_dot_ext. intros index Hindex. symmetry.
      apply mc_term_coefficients_outside with (bound := bound); [assumption|lia].
Qed.

Lemma vector_entry_append_left : forall d extra
    (left : NVec d) (right : NVec extra) index,
    (index < d)%nat ->
    vector_entry (Vector.append left right) index = vector_entry left index.
Proof.
  intros d extra left right index Hindex. unfold vector_entry.
  rewrite Vector.to_list_append, app_nth1; [reflexivity|].
  now rewrite length_to_list.
Qed.

Lemma vector_entry_append_right : forall d extra
    (left : NVec d) (right : NVec extra) index,
    (index < extra)%nat ->
    vector_entry (Vector.append left right) (d + index)%nat =
      vector_entry right index.
Proof.
  intros d extra left right index Hindex. unfold vector_entry.
  rewrite Vector.to_list_append, app_nth2 by (rewrite length_to_list; lia).
  rewrite length_to_list. replace (d + index - d)%nat with index by lia.
  reflexivity.
Qed.

Definition primitive_equation (d total offset : nat)
    (cenv : MC.environment) (primitive : QFPrimitive) : RawEquation :=
  let term := primitive_term primitive in
  let coefficients := mc_term_coefficients term in
  match primitive with
  | PrimEq _ => (coefficients, - mc_term_constant cenv term)
  | PrimPos scale constant _ =>
      ((fun index => scale * coefficients index +
          delta_coefficient (d + offset)%nat (-1) index),
        1 - constant - scale * mc_term_constant cenv term)
  | PrimDiv divisor _ =>
      ((fun index => coefficients index +
          delta_coefficient (d + offset)%nat (- divisor) index +
          delta_coefficient (d + S offset)%nat divisor index),
        - mc_term_constant cenv term)
  | PrimRem modulus residue _ =>
      ((fun index => coefficients index +
          delta_coefficient (d + offset)%nat (- modulus) index +
          delta_coefficient (d + S offset)%nat modulus index),
        residue - mc_term_constant cenv term)
  end.

Fixpoint branch_aux (branch : QFBranch) : nat :=
  match branch with
  | [] => 0%nat
  | _ :: tail => S (S (branch_aux tail))
  end.

Fixpoint compile_branch_from (d total offset : nat)
    (cenv : MC.environment) (branch : QFBranch) : list RawEquation :=
  match branch with
  | [] => []
  | primitive :: tail =>
      primitive_equation d total offset cenv primitive ::
      compile_branch_from d total (S (S offset)) cenv tail
  end.

Definition compile_branch d cenv (branch : QFBranch) : list RawEquation :=
  compile_branch_from d (branch_aux branch) 0 cenv branch.

Fixpoint branch_witnessed (cenv env : MC.environment) (offset : nat)
    (branch : QFBranch) (values : nat -> nat) : Prop :=
  match branch with
  | [] => True
  | primitive :: tail =>
      primitive_diophantine cenv env primitive (values offset)
        (values (S offset)) /\
      branch_witnessed cenv env (S (S offset)) tail values
  end.

Lemma primitive_equation_correct : forall d total offset cenv primitive
    (free : NVec d) (auxiliary : NVec total),
    primitive_scoped d primitive ->
    (S offset < total)%nat ->
    equation_holds (d + total)
      (fun index => vector_entry (Vector.append free auxiliary) index)
      (primitive_equation d total offset cenv primitive) <->
    primitive_diophantine cenv (nat_environment free) primitive
      (vector_entry auxiliary offset) (vector_entry auxiliary (S offset)).
Proof.
  intros d total offset cenv primitive free auxiliary Hscope Hoffset.
  destruct primitive as [term|scale constant term|divisor term|modulus residue term];
    unfold primitive_scoped, primitive_term in Hscope;
    unfold primitive_equation, equation_holds, primitive_diophantine;
    cbn [primitive_term fst snd].
  all: assert (Hterm : raw_dot (d + total) (mc_term_coefficients term)
        (fun index => vector_entry (Vector.append free auxiliary) index) =
      raw_dot d (mc_term_coefficients term)
        (fun index => vector_entry free index)).
  all: try (rewrite raw_dot_scoped_extend by exact Hscope;
    apply raw_dot_values_ext; intros index Hindex;
    apply vector_entry_append_left; exact Hindex).
  - pose proof (mc_term_linearize d cenv
      (fun index => vector_entry free index) term Hscope) as Hlinear.
    unfold nat_environment in *. rewrite Hterm. split; intro H; lia.
  - rewrite raw_dot_add, raw_dot_scale,
      raw_dot_delta by lia.
    rewrite vector_entry_append_right by lia.
    pose proof (mc_term_linearize d cenv
      (fun index => vector_entry free index) term Hscope) as Hlinear.
    unfold nat_environment in *. rewrite Hterm. split; intro; lia.
  - repeat rewrite raw_dot_add.
    rewrite !raw_dot_delta by lia.
    rewrite !vector_entry_append_right by lia.
    pose proof (mc_term_linearize d cenv
      (fun index => vector_entry free index) term Hscope) as Hlinear.
    unfold nat_environment in *. rewrite Hterm. split; intro; nia.
  - repeat rewrite raw_dot_add.
    rewrite !raw_dot_delta by lia.
    rewrite !vector_entry_append_right by lia.
    pose proof (mc_term_linearize d cenv
      (fun index => vector_entry free index) term Hscope) as Hlinear.
    unfold nat_environment in *. rewrite Hterm. split; intro; nia.
Qed.

Lemma compile_branch_from_correct : forall d total offset cenv branch
    (free : NVec d) (auxiliary : NVec total),
    branch_scoped d branch ->
    (offset + branch_aux branch <= total)%nat ->
    (system_holds (d + total)
      (fun index => vector_entry (Vector.append free auxiliary) index)
      (compile_branch_from d total offset cenv branch) <->
     branch_witnessed cenv (nat_environment free) offset branch
       (fun index => vector_entry auxiliary index)).
Proof.
  intros d total offset cenv branch. revert offset.
  induction branch as [|primitive tail IH];
    intros offset free auxiliary Hscope Hbound; cbn [compile_branch_from branch_aux
      system_holds branch_witnessed] in *.
  - split; intro; constructor.
  - inversion Hscope as [|primitive' tail' Hprimitive Htail]; subst.
    unfold system_holds at 1. rewrite List.Forall_cons_iff.
    rewrite primitive_equation_correct by (assumption || lia).
    pose proof (IH (S (S offset)) free auxiliary Htail ltac:(lia)) as Htailiff.
    unfold system_holds in Htailiff. tauto.
Qed.

Lemma branch_witnessed_offset_ext : forall cenv env branch left right
    left_offset right_offset,
    (forall index,
      left (left_offset + index)%nat = right (right_offset + index)%nat) ->
    (branch_witnessed cenv env left_offset branch left <->
      branch_witnessed cenv env right_offset branch right).
Proof.
  intros cenv env branch. induction branch as [|primitive tail IH];
    intros left right left_offset right_offset Heq;
    cbn [branch_witnessed]; [tauto|].
  pose proof (Heq 0%nat) as Hzero. pose proof (Heq 1%nat) as Hone.
  replace (left_offset + 0)%nat with left_offset in Hzero by lia.
  replace (right_offset + 0)%nat with right_offset in Hzero by lia.
  replace (left_offset + 1)%nat with (S left_offset) in Hone by lia.
  replace (right_offset + 1)%nat with (S right_offset) in Hone by lia.
  rewrite Hzero, Hone.
  apply and_iff_compat_l. apply IH. intro index.
  specialize (Heq (S (S index))). cbn in Heq.
  replace (left_offset + S (S index))%nat with
      (S (S left_offset) + index)%nat in Heq by lia.
  replace (right_offset + S (S index))%nat with
      (S (S right_offset) + index)%nat in Heq by lia.
  exact Heq.
Qed.

Lemma vector_entry_cons_cons_shift : forall n first second
    (tail : NVec n) index,
    vector_entry (@Vector.cons nat first _
      (@Vector.cons nat second _ tail)) (2 + index)%nat =
    vector_entry tail index.
Proof. reflexivity. Qed.

Lemma vector_entry_tail_tail_shift : forall n (values : NVec (S (S n))) index,
    vector_entry values (2 + index)%nat =
    vector_entry (Vector.tl (Vector.tl values)) index.
Proof.
  intros n values. refine (Vector.caseS' values (fun values => forall index,
    vector_entry values (2 + index)%nat =
    vector_entry (Vector.tl (Vector.tl values)) index) _).
  intros first rest. refine (Vector.caseS' rest (fun rest => forall index,
    vector_entry (@Vector.cons nat first _ rest) (2 + index)%nat =
    vector_entry (Vector.tl (Vector.tl (@Vector.cons nat first _ rest))) index) _).
  intros second tail index. reflexivity.
Qed.

Lemma branch_witnessed_exists : forall cenv env branch,
    branch_semantics cenv env branch <->
    exists auxiliary : NVec (branch_aux branch),
      branch_witnessed cenv env 0 branch
        (fun index => vector_entry auxiliary index).
Proof.
  intros cenv env branch. induction branch as [|primitive tail IH];
    cbn [branch_semantics branch_aux branch_witnessed].
  - split; intro H.
    + exists (@Vector.nil nat). constructor.
    + constructor.
  - unfold branch_semantics at 1. rewrite List.Forall_cons_iff,
      primitive_diophantine_correct, IH. split.
    + intros [[first [second Hprimitive]] [tail_values Htail]].
      exists (@Vector.cons nat first _
        (@Vector.cons nat second _ tail_values)). split; [exact Hprimitive|].
      pose proof (branch_witnessed_offset_ext cenv env tail
        (fun index => vector_entry
          (@Vector.cons nat first _ (@Vector.cons nat second _ tail_values)) index)
        (fun index => vector_entry tail_values index) 2 0
        ltac:(intro index; apply vector_entry_cons_cons_shift)) as Hshift.
      apply (proj2 Hshift). exact Htail.
    + intros [values Hvalues].
      destruct Hvalues as [Hprimitive Htail]. split.
      * exists (vector_entry values 0), (vector_entry values 1). exact Hprimitive.
      * exists (Vector.tl (Vector.tl values)).
        pose proof (branch_witnessed_offset_ext cenv env tail
          (fun index => vector_entry values index)
          (fun index => vector_entry (Vector.tl (Vector.tl values)) index) 2 0
          ltac:(intro index; apply vector_entry_tail_tail_shift)) as Hshift.
        apply (proj1 Hshift). exact Htail.
Qed.

Theorem branch_equations_correct : forall d cenv branch (free : NVec d),
    branch_scoped d branch ->
    (branch_semantics cenv (nat_environment free) branch <->
      exists auxiliary : NVec (branch_aux branch),
        LinearSolution
          (system_matrix (d + branch_aux branch) (compile_branch d cenv branch))
          (system_constant (compile_branch d cenv branch))
          (Vector.append free auxiliary)).
Proof.
  intros d cenv branch free Hscope. rewrite branch_witnessed_exists.
  unfold compile_branch. split; intros [auxiliary Hauxiliary]; exists auxiliary.
  - apply (proj2 (system_matrix_correct _ _ _)).
    apply (proj2 (compile_branch_from_correct d (branch_aux branch) 0 cenv
      branch free auxiliary Hscope ltac:(lia))). exact Hauxiliary.
  - apply (proj1 (compile_branch_from_correct d (branch_aux branch) 0 cenv
      branch free auxiliary Hscope ltac:(lia))).
    apply (proj1 (system_matrix_correct _ _ _)). exact Hauxiliary.
Qed.

Fixpoint nvec_prefix (d : nat) : forall extra, NVec (d + extra) -> NVec d :=
  match d with
  | 0%nat => fun _ _ => @Vector.nil nat
  | S tail => fun extra value =>
      @Vector.cons nat (Vector.hd value) tail
        (nvec_prefix tail extra (Vector.tl value))
  end.

Lemma nvec_prefix_append : forall d extra (left : NVec d) (right : NVec extra),
    nvec_prefix d extra (Vector.append left right) = left.
Proof.
  intros d extra left. induction left as [|head d tail IH]; intro right; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma nvec_prefix_zero : forall d extra,
    nvec_prefix d extra (nvec_zero (d + extra)) = nvec_zero d.
Proof.
  induction d as [|d IH]; intro extra; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma nvec_prefix_add : forall d extra (left right : NVec (d + extra)),
    nvec_prefix d extra (nvec_add left right) =
      nvec_add (nvec_prefix d extra left) (nvec_prefix d extra right).
Proof.
  intros d extra left. revert left. induction d as [|d IH]; intros left right.
  - reflexivity.
  - refine (Vector.caseS' left (fun left => forall right,
      nvec_prefix (S d) extra (nvec_add left right) =
      nvec_add (nvec_prefix (S d) extra left) (nvec_prefix (S d) extra right)) _ right).
    intros left_head left_tail right'.
    refine (Vector.caseS' right' (fun right' =>
      nvec_prefix (S d) extra
        (nvec_add (@Vector.cons nat left_head _ left_tail) right') =
      nvec_add (nvec_prefix (S d) extra
        (@Vector.cons nat left_head _ left_tail))
        (nvec_prefix (S d) extra right')) _).
    intros right_head right_tail. cbn. rewrite IH. reflexivity.
Qed.

Lemma nvec_prefix_scale : forall d extra coefficient
    (value : NVec (d + extra)),
    nvec_prefix d extra (nvec_scale coefficient value) =
      nvec_scale coefficient (nvec_prefix d extra value).
Proof.
  intros d extra coefficient value. revert value.
  induction d as [|d IH]; intro value; [reflexivity|].
  refine (Vector.caseS' value (fun value =>
    nvec_prefix (S d) extra (nvec_scale coefficient value) =
      nvec_scale coefficient (nvec_prefix (S d) extra value)) _).
  intros head tail. cbn. apply f_equal. apply IH.
Qed.

Definition project_component d extra (component : LinearComponent (d + extra)) :
    LinearComponent d :=
  (nvec_prefix d extra (fst component),
    List.map (nvec_prefix d extra) (snd component)).

Definition project_semicode d extra (code : SemiCode (d + extra)) : SemiCode d :=
  List.map (project_component d extra) code.

Lemma weighted_sum_project : forall d extra coefficients
    (periods : list (NVec (d + extra))) contribution,
    weighted_sum coefficients periods = Some contribution ->
    weighted_sum coefficients (List.map (nvec_prefix d extra) periods) =
      Some (nvec_prefix d extra contribution).
Proof.
  intros d extra coefficients. induction coefficients as [|coefficient coefficients IH];
    intros periods contribution Hsum; destruct periods as [|period periods];
    cbn in *; try discriminate.
  - inversion Hsum. rewrite nvec_prefix_zero. reflexivity.
  - destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
      [|discriminate]. inversion Hsum; subst contribution.
    rewrite (IH periods tail Htail), nvec_prefix_add, nvec_prefix_scale. reflexivity.
Qed.

Lemma weighted_sum_project_lift : forall d extra coefficients
    (periods : list (NVec (d + extra))) projected,
    weighted_sum coefficients (List.map (nvec_prefix d extra) periods) =
      Some projected ->
    exists contribution,
      weighted_sum coefficients periods = Some contribution /\
      nvec_prefix d extra contribution = projected.
Proof.
  intros d extra coefficients. induction coefficients as [|coefficient coefficients IH];
    intros periods projected Hsum; destruct periods as [|period periods];
    cbn in *; try discriminate.
  - inversion Hsum; subst projected. exists (nvec_zero (d + extra)). split.
    + reflexivity.
    + apply nvec_prefix_zero.
  - destruct (weighted_sum coefficients (List.map (nvec_prefix d extra) periods))
      as [projected_tail|] eqn:Hprojected_tail; [|discriminate].
    inversion Hsum; subst projected.
    destruct (IH periods projected_tail Hprojected_tail) as
      [tail [Htail Hprefix]].
    exists (nvec_add (nvec_scale coefficient period) tail). split.
    + cbn. rewrite Htail. reflexivity.
    + rewrite nvec_prefix_add, nvec_prefix_scale, Hprefix. reflexivity.
Qed.

Lemma project_component_correct : forall d extra
    (component : LinearComponent (d + extra)) value,
    linear_denote (project_component d extra component) value <->
    exists full_value,
      linear_denote component full_value /\
      nvec_prefix d extra full_value = value.
Proof.
  intros d extra [base periods] value. unfold project_component, linear_denote.
  cbn [fst snd]. split.
  - intros [coefficients [projected [Hsum Hvalue]]].
    destruct (weighted_sum_project_lift d extra coefficients periods projected Hsum)
      as [contribution [Hfull Hprefix]].
    exists (nvec_add base contribution). split.
    + exists coefficients, contribution. auto.
    + rewrite nvec_prefix_add, Hprefix. symmetry. exact Hvalue.
  - intros [full_value [[coefficients [contribution [Hsum Hfull]]] Hprefix]].
    exists coefficients, (nvec_prefix d extra contribution). split.
    + now apply weighted_sum_project.
    + rewrite Hfull, nvec_prefix_add in Hprefix. symmetry. exact Hprefix.
Qed.

Theorem project_semicode_correct : forall d extra
    (code : SemiCode (d + extra)) value,
    denote (project_semicode d extra code) value <->
    exists full_value,
      denote code full_value /\
      nvec_prefix d extra full_value = value.
Proof.
  intros d extra code value. unfold project_semicode, denote. split.
  - intros [component [Hin Hlinear]]. apply in_map_iff in Hin.
    destruct Hin as [full_component [Heq Hin]]. subst component.
    apply project_component_correct in Hlinear.
    destruct Hlinear as [full_value [Hlinear Hprefix]].
    exists full_value. split; [exists full_component; auto|exact Hprefix].
  - intros [full_value [[component [Hin Hlinear]] Hprefix]].
    exists (project_component d extra component). split.
    + apply in_map_iff. exists component. auto.
    + apply project_component_correct. exists full_value. auto.
Qed.

Lemma nvec_prefix_has_suffix : forall d extra (value : NVec (d + extra)),
    exists suffix : NVec extra,
      value = Vector.append (nvec_prefix d extra value) suffix.
Proof.
  intros d extra value. destruct (Vector.splitat d value) as [prefix suffix] eqn:Hsplit.
  exists suffix. apply Vector.append_splitat in Hsplit. subst value.
  rewrite nvec_prefix_append. reflexivity.
Qed.

Theorem branch_semicode : forall d cenv branch,
    branch_scoped d branch ->
    exists code : SemiCode d,
      forall value : NVec d,
        branch_semantics cenv (nat_environment value) branch <->
        denote code value.
Proof.
  intros d cenv branch Hscope.
  destruct (linear_equations_semicode
    (List.length (compile_branch d cenv branch))
    (d + branch_aux branch)
    (system_matrix (d + branch_aux branch) (compile_branch d cenv branch))
    (system_constant (compile_branch d cenv branch))) as [full_code Hfull].
  exists (project_semicode d (branch_aux branch) full_code). intro value.
  rewrite branch_equations_correct by exact Hscope.
  rewrite project_semicode_correct. split.
  - intros [auxiliary Hsolution]. exists (Vector.append value auxiliary). split.
    + apply (proj1 (Hfull _)). exact Hsolution.
    + apply nvec_prefix_append.
  - intros [full_value [Hdenote Hprefix]].
    destruct (nvec_prefix_has_suffix d (branch_aux branch) full_value) as
      [auxiliary Happend].
    rewrite Hprefix in Happend.
    exists auxiliary. apply (proj2 (Hfull _)). rewrite <- Happend.
    exact Hdenote.
Qed.

Lemma positive_atom_dnf_scoped : forall d predicate term,
    mc_term_scoped d term -> dnf_scoped d (positive_atom_dnf predicate term).
Proof.
  intros d predicate term Hscope. destruct predicate; cbn;
    repeat constructor; exact Hscope.
Qed.

Lemma negative_atom_dnf_scoped : forall d predicate term,
    mc_term_scoped d term -> dnf_scoped d (negative_atom_dnf predicate term).
Proof.
  intros d predicate term Hscope. destruct predicate; cbn.
  - repeat constructor; exact Hscope.
  - repeat constructor; exact Hscope.
  - destruct (Z.eq_dec z 0); cbn.
    + repeat constructor; exact Hscope.
    + remember (nonzero_residues (Z.abs z)) as residues.
      clear Heqresidues n. induction residues as [|residue residues IH]; cbn.
      * constructor.
      * constructor; [repeat constructor; exact Hscope|exact IH].
Qed.

Lemma dnf_scoped_append : forall d left right,
    dnf_scoped d left -> dnf_scoped d right -> dnf_scoped d (left ++ right).
Proof. intros; apply Forall_app; auto. Qed.

Lemma dnf_scoped_and : forall d left right,
    dnf_scoped d left -> dnf_scoped d right -> dnf_scoped d (dnf_and left right).
Proof.
  intros d left right Hleft Hright. unfold dnf_scoped in Hleft, Hright |- *.
  unfold dnf_and.
  apply List.Forall_forall. intros combined Hin. apply in_flat_map in Hin.
  destruct Hin as [left_branch [Hinleft Hinmap]].
  apply in_map_iff in Hinmap.
  destruct Hinmap as [right_branch [Heq Hinright]]. subst combined.
  pose proof (proj1 (List.Forall_forall (branch_scoped d) left)
    Hleft left_branch Hinleft)
    as Hleft_branch.
  pose proof (proj1 (List.Forall_forall (branch_scoped d) right)
    Hright right_branch Hinright)
    as Hright_branch.
  unfold branch_scoped in *. now apply Forall_app.
Qed.

Lemma signed_dnf_scoped : forall d formula,
    qf_well_scoped d formula ->
    dnf_scoped d (positive_dnf formula) /\
    dnf_scoped d (negative_dnf formula).
Proof.
  intros d formula Hscope. unfold qf_well_scoped in Hscope.
  induction Hscope; cbn [positive_dnf negative_dnf].
  - split; [apply positive_atom_dnf_scoped|apply negative_atom_dnf_scoped];
      exact H.
  - split.
    + constructor.
    + constructor; constructor.
  - split.
    + constructor; constructor.
    + constructor.
  - destruct IHHscope1 as [Hpos1 Hneg1].
    destruct IHHscope2 as [Hpos2 Hneg2]. split.
    + now apply dnf_scoped_and.
    + now apply dnf_scoped_append.
  - destruct IHHscope1 as [Hpos1 Hneg1].
    destruct IHHscope2 as [Hpos2 Hneg2]. split.
    + now apply dnf_scoped_append.
    + now apply dnf_scoped_and.
  - destruct IHHscope as [Hpositive Hnegative]. auto.
Qed.

Lemma formula_dnf_scoped : forall d formula,
    qf_well_scoped d formula -> dnf_scoped d (formula_dnf formula).
Proof.
  intros d formula Hscope. unfold formula_dnf.
  exact (proj1 (signed_dnf_scoped d formula Hscope)).
Qed.

Lemma denote_app : forall d (left right : SemiCode d) value,
    denote (left ++ right) value <-> denote left value \/ denote right value.
Proof.
  intros d left right value. unfold denote. split.
  - intros [component [Hin Hlinear]]. apply in_app_iff in Hin.
    destruct Hin; [left|right]; exists component; auto.
  - intros [[component [Hin Hlinear]]|[component [Hin Hlinear]]].
    + exists component. split; [apply in_app_iff; now left|exact Hlinear].
    + exists component. split; [apply in_app_iff; now right|exact Hlinear].
Qed.

Lemma dnf_semicode : forall d cenv dnf,
    dnf_scoped d dnf ->
    exists code : SemiCode d,
      forall value : NVec d,
        dnf_semantics cenv (nat_environment value) dnf <-> denote code value.
Proof.
  intros d cenv dnf Hscope. induction Hscope as [|branch tail Hbranch Htail IH].
  - exists []. intro value. split.
    + intros [branch [Hin _]]. inversion Hin.
    + intro Hdenote. exfalso. exact (denote_empty d value Hdenote).
  - destruct (branch_semicode d cenv branch Hbranch) as [head_code Hhead].
    destruct IH as [tail_code Htail_code]. exists (head_code ++ tail_code).
    intro value. rewrite denote_app. unfold dnf_semantics at 1. split.
    + intros [selected [[Heq|Hin] Hselected]].
      * subst selected. left. apply (proj1 (Hhead value)). exact Hselected.
      * right. apply (proj1 (Htail_code value)). exists selected. auto.
    + intros [Hselected|Hselected].
      * exists branch. split; [now left|]. apply (proj2 (Hhead value)); assumption.
      * apply (proj2 (Htail_code value)) in Hselected.
        destruct Hselected as [selected [Hin Hsemantics]].
        exists selected. split; [now right|exact Hsemantics].
Qed.

Theorem qf_semicode : forall d (cenv : MC.environment) (formula : MC.formula),
    qf_well_scoped d formula ->
    exists code : SemiCode d,
      forall value : NVec d,
        MC.interpret_formula cenv (nat_environment value) formula <->
        denote code value.
Proof.
  intros d cenv formula Hscope.
  destruct (dnf_semicode d cenv (formula_dnf formula)
    (formula_dnf_scoped d formula Hscope)) as [code Hcode].
  exists code. intro value. rewrite <- Hcode.
  symmetry. apply formula_dnf_correct. now apply qf_well_scoped_qf with (d := d).
Qed.
