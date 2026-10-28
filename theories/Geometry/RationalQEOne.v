From Coq Require Import Bool Field Lia List QArith Qfield Qring.
From Mell.Geometry Require Import RationalDefinability.

Import ListNotations.
Open Scope Q_scope.

Record QSeparatedTerm : Type := {
  separated_coefficient : Q;
  separated_tail : QTerm
}.

Definition qterm_zero : QTerm := QTConst 0.
Definition qterm_plus (left right : QTerm) : QTerm := QTAdd left right.
Definition qterm_minus (left right : QTerm) : QTerm :=
  QTAdd left (QTOpp right).

Definition separated_add (left right : QSeparatedTerm) : QSeparatedTerm :=
  {| separated_coefficient := separated_coefficient left +
       separated_coefficient right;
     separated_tail := qterm_plus (separated_tail left) (separated_tail right) |}.

Definition separated_opp (value : QSeparatedTerm) : QSeparatedTerm :=
  {| separated_coefficient := - separated_coefficient value;
     separated_tail := QTOpp (separated_tail value) |}.

Definition separated_scale (coefficient : Q)
    (value : QSeparatedTerm) : QSeparatedTerm :=
  {| separated_coefficient := coefficient * separated_coefficient value;
     separated_tail := QTScale coefficient (separated_tail value) |}.

Fixpoint separate_term (term : QTerm) : QSeparatedTerm :=
  match term with
  | QTVar O => {| separated_coefficient := 1; separated_tail := qterm_zero |}
  | QTVar (S variable) =>
      {| separated_coefficient := 0; separated_tail := QTVar variable |}
  | QTConst constant =>
      {| separated_coefficient := 0; separated_tail := QTConst constant |}
  | QTAdd lhs rhs => separated_add (separate_term lhs) (separate_term rhs)
  | QTOpp value => separated_opp (separate_term value)
  | QTScale coefficient value =>
      separated_scale coefficient (separate_term value)
  end.

Definition separated_semantics (environment : QEnvironment) (bound : Q)
    (term : QSeparatedTerm) : Q :=
  separated_coefficient term * bound +
    qterm_semantics environment (separated_tail term).

Theorem separate_term_correct : forall term environment bound,
    qterm_semantics (qenvironment_extend environment bound) term ==
      separated_semantics environment bound (separate_term term).
Proof.
  intro term. induction term; intros environment bound; cbn.
  - destruct n; cbn; unfold separated_semantics, qterm_zero; cbn; ring.
  - unfold separated_semantics; cbn; ring.
  - unfold separated_semantics, separated_add in *; cbn in *.
    setoid_rewrite IHterm1. setoid_rewrite IHterm2. ring.
  - unfold separated_semantics, separated_opp in *; cbn in *.
    setoid_rewrite IHterm. ring.
  - unfold separated_semantics, separated_scale in *; cbn in *.
    setoid_rewrite IHterm. ring.
Qed.

Inductive QAffineAtom : Type :=
| QAEq : QTerm -> QTerm -> QAffineAtom
| QALe : QTerm -> QTerm -> QAffineAtom
| QALt : QTerm -> QTerm -> QAffineAtom.

Definition QAffineConjunction := list QAffineAtom.

Definition qaffine_atom_semantics (environment : QEnvironment)
    (atom : QAffineAtom) : Prop :=
  match atom with
  | QAEq lhs rhs => qterm_semantics environment lhs == qterm_semantics environment rhs
  | QALe lhs rhs => qterm_semantics environment lhs <= qterm_semantics environment rhs
  | QALt lhs rhs => qterm_semantics environment lhs < qterm_semantics environment rhs
  end.

Definition qconjunction_semantics (environment : QEnvironment)
    (body : QAffineConjunction) : Prop :=
  List.Forall (qaffine_atom_semantics environment) body.

Record QLinearConstraint : Type := {
  constraint_coefficient : Q;
  constraint_rhs : QTerm;
  constraint_strict : bool
}.

Definition qconstraint_semantics (environment : QEnvironment) (bound : Q)
    (constraint : QLinearConstraint) : Prop :=
  if constraint_strict constraint
  then constraint_coefficient constraint * bound <
       qterm_semantics environment (constraint_rhs constraint)
  else constraint_coefficient constraint * bound <=
       qterm_semantics environment (constraint_rhs constraint).

Definition normalize_difference (left right : QTerm) : QLinearConstraint :=
  let left' := separate_term left in
  let right' := separate_term right in
  {| constraint_coefficient :=
       separated_coefficient left' - separated_coefficient right';
     constraint_rhs := qterm_minus (separated_tail right') (separated_tail left');
     constraint_strict := false |}.

Definition normalize_atom (atom : QAffineAtom) : list QLinearConstraint :=
  match atom with
  | QAEq lhs rhs =>
      [normalize_difference lhs rhs; normalize_difference rhs lhs]
  | QALe lhs rhs => [normalize_difference lhs rhs]
  | QALt lhs rhs =>
      [{| constraint_coefficient :=
           constraint_coefficient (normalize_difference lhs rhs);
          constraint_rhs := constraint_rhs (normalize_difference lhs rhs);
          constraint_strict := true |}]
  end.

Lemma qlinear_move_lt : forall lc rc bound lt rt,
    lc * bound + lt < rc * bound + rt <->
    (lc - rc) * bound < rt - lt.
Proof.
  intros lc rc bound lt rt. split; intro H.
  - apply (proj1 (Qplus_lt_l ((lc - rc) * bound) (rt - lt)
      (rc * bound + lt))).
    setoid_replace ((lc - rc) * bound + (rc * bound + lt))
      with (lc * bound + lt) by ring.
    setoid_replace ((rt - lt) + (rc * bound + lt))
      with (rc * bound + rt) by ring. exact H.
  - pose proof (proj2 (Qplus_lt_l ((lc - rc) * bound) (rt - lt)
      (rc * bound + lt)) H) as Hsum.
    setoid_replace ((lc - rc) * bound + (rc * bound + lt))
      with (lc * bound + lt) in Hsum by ring.
    setoid_replace ((rt - lt) + (rc * bound + lt))
      with (rc * bound + rt) in Hsum by ring. exact Hsum.
Qed.

Lemma qlinear_move_le : forall lc rc bound lt rt,
    lc * bound + lt <= rc * bound + rt <->
    (lc - rc) * bound <= rt - lt.
Proof.
  intros lc rc bound lt rt. split; intro H.
  - apply (proj1 (Qplus_le_l ((lc - rc) * bound) (rt - lt)
      (rc * bound + lt))).
    setoid_replace ((lc - rc) * bound + (rc * bound + lt))
      with (lc * bound + lt) by ring.
    setoid_replace ((rt - lt) + (rc * bound + lt))
      with (rc * bound + rt) by ring. exact H.
  - pose proof (proj2 (Qplus_le_l ((lc - rc) * bound) (rt - lt)
      (rc * bound + lt)) H) as Hsum.
    setoid_replace ((lc - rc) * bound + (rc * bound + lt))
      with (lc * bound + lt) in Hsum by ring.
    setoid_replace ((rt - lt) + (rc * bound + lt))
      with (rc * bound + rt) in Hsum by ring. exact Hsum.
Qed.

Lemma normalize_difference_correct : forall (left right : QTerm)
    (environment : QEnvironment) (bound : Q) (strict : bool),
    (if strict
     then qterm_semantics (qenvironment_extend environment bound) left <
          qterm_semantics (qenvironment_extend environment bound) right
     else qterm_semantics (qenvironment_extend environment bound) left <=
          qterm_semantics (qenvironment_extend environment bound) right) <->
    qconstraint_semantics environment bound
      {| constraint_coefficient := constraint_coefficient
           (normalize_difference left right);
         constraint_rhs := constraint_rhs (normalize_difference left right);
         constraint_strict := strict |}.
Proof.
  intros left right environment bound strict.
  unfold normalize_difference, qconstraint_semantics.
  destruct (separate_term left) as [lc lt] eqn:Hleft.
  destruct (separate_term right) as [rc rt] eqn:Hright. cbn.
  pose proof (separate_term_correct left environment bound) as Hl.
  pose proof (separate_term_correct right environment bound) as Hr.
  rewrite Hleft in Hl. rewrite Hright in Hr. cbn in Hl, Hr.
  unfold qterm_minus, qterm_plus; cbn.
  destruct strict; cbn; setoid_rewrite Hl; setoid_rewrite Hr.
  - apply qlinear_move_lt.
  - apply qlinear_move_le.
Qed.

Lemma normalize_atom_correct : forall atom environment bound,
    qaffine_atom_semantics (qenvironment_extend environment bound) atom <->
    List.Forall (qconstraint_semantics environment bound) (normalize_atom atom).
Proof.
  intros [left right|left right|left right] environment bound; cbn.
  - split.
    + intro Heq. constructor.
      * apply (proj1 (normalize_difference_correct left right environment bound false)).
        setoid_rewrite Heq. apply Qle_refl.
      * constructor; [|constructor].
        apply (proj1 (normalize_difference_correct right left environment bound false)).
        setoid_rewrite Heq. apply Qle_refl.
    + intro Hall. inversion Hall as [|? ? Hlr Hrest]; subst.
      inversion Hrest as [|? ? Hrl Hnil]; subst.
      apply Qle_antisym.
      * apply (proj2 (normalize_difference_correct left right environment bound false)); exact Hlr.
      * apply (proj2 (normalize_difference_correct right left environment bound false)); exact Hrl.
  - split; intro H.
    + constructor.
      * apply (proj1 (normalize_difference_correct left right environment bound false)).
        exact H.
      * constructor.
    + inversion H as [|? ? Hhead Hnil]; subst.
      apply (proj2 (normalize_difference_correct left right environment bound false)).
      exact Hhead.
  - split; intro H.
    + constructor.
      * apply (proj1 (normalize_difference_correct left right environment bound true)).
        exact H.
      * constructor.
    + inversion H as [|? ? Hhead Hnil]; subst.
      apply (proj2 (normalize_difference_correct left right environment bound true)).
      exact Hhead.
Qed.

Fixpoint normalize_conjunction (body : QAffineConjunction) :
    list QLinearConstraint :=
  match body with
  | [] => []
  | atom :: tail => normalize_atom atom ++ normalize_conjunction tail
  end.

Lemma normalize_conjunction_correct : forall body environment bound,
    qconjunction_semantics (qenvironment_extend environment bound) body <->
    List.Forall (qconstraint_semantics environment bound)
      (normalize_conjunction body).
Proof.
  intros body. induction body as [|atom body IH]; intros environment bound;
    unfold qconjunction_semantics in *; cbn.
  - split; intro H; constructor.
  - rewrite Forall_cons_iff, Forall_app, <- normalize_atom_correct, <- IH.
    reflexivity.
Qed.

Record QEndpoint : Type := {
  endpoint_term : QTerm;
  endpoint_strict : bool
}.

Definition endpoint_value (environment : QEnvironment) (endpoint : QEndpoint) : Q :=
  qterm_semantics environment (endpoint_term endpoint).

Record QElimState : Type := {
  state_residual : list QEndpoint;
  state_lower : list QEndpoint;
  state_upper : list QEndpoint
}.

Definition empty_state : QElimState :=
  {| state_residual := []; state_lower := []; state_upper := [] |}.

Definition endpoint_of_constraint (constraint : QLinearConstraint) : QEndpoint :=
  {| endpoint_term := QTScale (/ constraint_coefficient constraint)
       (constraint_rhs constraint);
     endpoint_strict := constraint_strict constraint |}.

Definition residual_of_constraint (constraint : QLinearConstraint) : QEndpoint :=
  {| endpoint_term := constraint_rhs constraint;
     endpoint_strict := constraint_strict constraint |}.

Definition add_constraint (constraint : QLinearConstraint)
    (state : QElimState) : QElimState :=
  if Qlt_le_dec (constraint_coefficient constraint) 0 then
    {| state_residual := state_residual state;
       state_lower := endpoint_of_constraint constraint :: state_lower state;
       state_upper := state_upper state |}
  else if Qeq_dec (constraint_coefficient constraint) 0 then
    {| state_residual := residual_of_constraint constraint :: state_residual state;
       state_lower := state_lower state;
       state_upper := state_upper state |}
  else
    {| state_residual := state_residual state;
       state_lower := state_lower state;
       state_upper := endpoint_of_constraint constraint :: state_upper state |}.

Definition classify_constraints (constraints : list QLinearConstraint) : QElimState :=
  List.fold_right add_constraint empty_state constraints.

Definition residual_holds (environment : QEnvironment) (endpoint : QEndpoint) : Prop :=
  if endpoint_strict endpoint then 0 < endpoint_value environment endpoint
  else 0 <= endpoint_value environment endpoint.

Definition lower_holds (environment : QEnvironment) (bound : Q)
    (endpoint : QEndpoint) : Prop :=
  if endpoint_strict endpoint then endpoint_value environment endpoint < bound
  else endpoint_value environment endpoint <= bound.

Definition upper_holds (environment : QEnvironment) (bound : Q)
    (endpoint : QEndpoint) : Prop :=
  if endpoint_strict endpoint then bound < endpoint_value environment endpoint
  else bound <= endpoint_value environment endpoint.

Definition state_semantics (environment : QEnvironment) (bound : Q)
    (state : QElimState) : Prop :=
  List.Forall (residual_holds environment) (state_residual state) /\
  List.Forall (lower_holds environment bound) (state_lower state) /\
  List.Forall (upper_holds environment bound) (state_upper state).

Lemma qdiv_opp_opp : forall numerator denominator,
    ~ denominator == 0 -> numerator / denominator ==
      (- numerator) / (- denominator).
Proof. intros; field; assumption. Qed.

Lemma positive_coefficient_lt : forall coefficient bound rhs,
    0 < coefficient ->
    (coefficient * bound < rhs <-> bound < rhs / coefficient).
Proof.
  intros coefficient bound rhs Hpositive. split; intro H.
  - apply Qlt_shift_div_l; [exact Hpositive|].
    setoid_rewrite Qmult_comm. exact H.
  - pose proof (proj2 (Qmult_lt_l bound (rhs / coefficient)
      coefficient Hpositive) H) as Hscaled.
    setoid_rewrite Qmult_div_r in Hscaled; auto with qarith.
Qed.

Lemma positive_coefficient_le : forall coefficient bound rhs,
    0 < coefficient ->
    (coefficient * bound <= rhs <-> bound <= rhs / coefficient).
Proof.
  intros coefficient bound rhs Hpositive. split; intro H.
  - apply Qle_shift_div_l; [exact Hpositive|].
    setoid_rewrite Qmult_comm. exact H.
  - pose proof (proj2 (Qmult_le_l bound (rhs / coefficient)
      coefficient Hpositive) H) as Hscaled.
    setoid_rewrite Qmult_div_r in Hscaled; auto with qarith.
Qed.

Lemma negative_coefficient_lt : forall coefficient bound rhs,
    coefficient < 0 ->
    (coefficient * bound < rhs <-> rhs / coefficient < bound).
Proof.
  intros coefficient bound rhs Hnegative.
  assert (Hpositive : 0 < - coefficient).
  { pose proof (Qopp_lt_compat coefficient 0 Hnegative) as Hopp.
    cbn in Hopp. exact Hopp. }
  assert (Hnonzero : ~ coefficient == 0) by auto with qarith.
  split; intro H.
  - setoid_rewrite (qdiv_opp_opp rhs coefficient Hnonzero).
    apply Qlt_shift_div_r; [exact Hpositive|].
    pose proof (Qopp_lt_compat _ _ H) as Hopp.
    setoid_replace (- (coefficient * bound)) with ((- coefficient) * bound)
      in Hopp by ring.
    setoid_replace ((- coefficient) * bound) with (bound * (- coefficient))
      in Hopp by ring. exact Hopp.
  - setoid_rewrite (qdiv_opp_opp rhs coefficient Hnonzero) in H.
    pose proof (proj2 (Qmult_lt_l ((- rhs) / (- coefficient)) bound
      (- coefficient) Hpositive) H) as Hscaled.
    setoid_rewrite Qmult_div_r in Hscaled; [|auto with qarith].
    pose proof (Qopp_lt_compat _ _ Hscaled) as Hopp.
    setoid_replace (- ((- coefficient) * bound)) with (coefficient * bound)
      in Hopp by ring.
    setoid_replace (- (- rhs)) with rhs in Hopp by ring. exact Hopp.
Qed.

Lemma negative_coefficient_le : forall coefficient bound rhs,
    coefficient < 0 ->
    (coefficient * bound <= rhs <-> rhs / coefficient <= bound).
Proof.
  intros coefficient bound rhs Hnegative.
  assert (Hpositive : 0 < - coefficient).
  { pose proof (Qopp_lt_compat coefficient 0 Hnegative) as Hopp.
    cbn in Hopp. exact Hopp. }
  assert (Hnonzero : ~ coefficient == 0) by auto with qarith.
  split; intro H.
  - setoid_rewrite (qdiv_opp_opp rhs coefficient Hnonzero).
    apply Qle_shift_div_r; [exact Hpositive|].
    pose proof (Qopp_le_compat _ _ H) as Hopp.
    setoid_replace (- (coefficient * bound)) with ((- coefficient) * bound)
      in Hopp by ring.
    setoid_replace ((- coefficient) * bound) with (bound * (- coefficient))
      in Hopp by ring. exact Hopp.
  - setoid_rewrite (qdiv_opp_opp rhs coefficient Hnonzero) in H.
    pose proof (proj2 (Qmult_le_l ((- rhs) / (- coefficient)) bound
      (- coefficient) Hpositive) H) as Hscaled.
    setoid_rewrite Qmult_div_r in Hscaled; [|auto with qarith].
    pose proof (Qopp_le_compat _ _ Hscaled) as Hopp.
    setoid_replace (- ((- coefficient) * bound)) with (coefficient * bound)
      in Hopp by ring.
    setoid_replace (- (- rhs)) with rhs in Hopp by ring. exact Hopp.
Qed.

Lemma constraint_classification_correct : forall constraint environment bound state,
    qconstraint_semantics environment bound constraint /\
      state_semantics environment bound state <->
    state_semantics environment bound (add_constraint constraint state).
Proof.
  intros [coefficient rhs strict] environment bound [residual lower upper].
  unfold add_constraint, qconstraint_semantics, state_semantics,
    residual_holds, lower_holds, upper_holds, endpoint_of_constraint,
    residual_of_constraint, endpoint_value. cbn.
  destruct (Qlt_le_dec coefficient 0) as [Hnegative|Hnonnegative].
  - destruct strict; cbn.
    + split.
      * intros [Hc [Hr [Hl Hu]]]. split; [exact Hr|]. split; [|exact Hu].
        constructor.
        -- change ((/ coefficient) * qterm_semantics environment rhs < bound).
           setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
             with (qterm_semantics environment rhs / coefficient)
             by (unfold Qdiv; ring).
           apply (proj1 (negative_coefficient_lt _ _ _ Hnegative)); exact Hc.
        -- exact Hl.
      * intros [Hr [Hlower Hu]]. inversion Hlower as [|? ? Hc Hl]; subst.
        cbn in Hc.
        setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
          with (qterm_semantics environment rhs / coefficient) in Hc
          by (unfold Qdiv; ring).
        split; [apply (proj2 (negative_coefficient_lt _ _ _ Hnegative));
          exact Hc|]. repeat split; assumption.
    + split.
      * intros [Hc [Hr [Hl Hu]]]. split; [exact Hr|]. split; [|exact Hu].
        constructor.
        -- change ((/ coefficient) * qterm_semantics environment rhs <= bound).
           setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
             with (qterm_semantics environment rhs / coefficient)
             by (unfold Qdiv; ring).
           apply (proj1 (negative_coefficient_le _ _ _ Hnegative)); exact Hc.
        -- exact Hl.
      * intros [Hr [Hlower Hu]]. inversion Hlower as [|? ? Hc Hl]; subst.
        cbn in Hc.
        setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
          with (qterm_semantics environment rhs / coefficient) in Hc
          by (unfold Qdiv; ring).
        split; [apply (proj2 (negative_coefficient_le _ _ _ Hnegative));
          exact Hc|]. repeat split; assumption.
  - destruct (Qeq_dec coefficient 0) as [Hzero|Hnonzero].
    + destruct strict; cbn.
      * split.
        -- intros [Hc [Hr [Hl Hu]]]. setoid_rewrite Hzero in Hc.
           setoid_rewrite Qmult_0_l in Hc.
           split; [constructor; assumption|]. split; assumption.
        -- intros [Hres [Hl Hu]]. inversion Hres as [|? ? Hc Hr]; subst.
           split.
           ++ setoid_rewrite Hzero. setoid_rewrite Qmult_0_l. exact Hc.
           ++ repeat split; assumption.
      * split.
        -- intros [Hc [Hr [Hl Hu]]]. setoid_rewrite Hzero in Hc.
           setoid_rewrite Qmult_0_l in Hc.
           split; [constructor; assumption|]. split; assumption.
        -- intros [Hres [Hl Hu]]. inversion Hres as [|? ? Hc Hr]; subst.
           split.
           ++ setoid_rewrite Hzero. setoid_rewrite Qmult_0_l. exact Hc.
           ++ repeat split; assumption.
    + assert (Hpositive : 0 < coefficient).
      { destruct (Qle_lt_or_eq _ _ Hnonnegative); [assumption|].
        exfalso. apply Hnonzero. now symmetry. }
      destruct strict; cbn.
      * split.
        -- intros [Hc [Hr [Hl Hu]]]. split; [exact Hr|]. split; [exact Hl|].
           constructor.
           ++ change (bound < (/ coefficient) * qterm_semantics environment rhs).
              setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
                with (qterm_semantics environment rhs / coefficient)
                by (unfold Qdiv; ring).
              apply (proj1 (positive_coefficient_lt _ _ _ Hpositive)); exact Hc.
           ++ exact Hu.
        -- intros [Hr [Hl Hupper]]. inversion Hupper as [|? ? Hc Hu]; subst.
           cbn in Hc.
           setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
             with (qterm_semantics environment rhs / coefficient) in Hc
             by (unfold Qdiv; ring).
           split; [apply (proj2 (positive_coefficient_lt _ _ _ Hpositive));
             exact Hc|]. repeat split; assumption.
      * split.
        -- intros [Hc [Hr [Hl Hu]]]. split; [exact Hr|]. split; [exact Hl|].
           constructor.
           ++ change (bound <= (/ coefficient) * qterm_semantics environment rhs).
              setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
                with (qterm_semantics environment rhs / coefficient)
                by (unfold Qdiv; ring).
              apply (proj1 (positive_coefficient_le _ _ _ Hpositive)); exact Hc.
           ++ exact Hu.
        -- intros [Hr [Hl Hupper]]. inversion Hupper as [|? ? Hc Hu]; subst.
           cbn in Hc.
           setoid_replace ((/ coefficient) * qterm_semantics environment rhs)
             with (qterm_semantics environment rhs / coefficient) in Hc
             by (unfold Qdiv; ring).
           split; [apply (proj2 (positive_coefficient_le _ _ _ Hpositive));
             exact Hc|]. repeat split; assumption.
Qed.

Lemma classify_constraints_correct : forall constraints environment bound,
    List.Forall (qconstraint_semantics environment bound) constraints <->
    state_semantics environment bound (classify_constraints constraints).
Proof.
  intros constraints. induction constraints as [|constraint constraints IH];
    intros environment bound; cbn.
  - unfold state_semantics, empty_state. split; intro H.
    + repeat split; constructor.
    + constructor.
  - rewrite Forall_cons_iff, IH, constraint_classification_correct. reflexivity.
Qed.

Record QOutputAtom : Type := {
  output_left : QTerm;
  output_right : QTerm;
  output_strict : bool
}.

Definition qoutput_atom_semantics (environment : QEnvironment)
    (atom : QOutputAtom) : Prop :=
  if output_strict atom
  then qterm_semantics environment (output_left atom) <
       qterm_semantics environment (output_right atom)
  else qterm_semantics environment (output_left atom) <=
       qterm_semantics environment (output_right atom).

Definition QOutputConjunction := list QOutputAtom.
Definition QDNF := list QOutputConjunction.

Definition qoutput_conjunction_semantics environment (body : QOutputConjunction) :=
  List.Forall (qoutput_atom_semantics environment) body.

Definition qdnf_semantics environment (dnf : QDNF) : Prop :=
  exists body, List.In body dnf /\ qoutput_conjunction_semantics environment body.

Definition residual_atom (endpoint : QEndpoint) : QOutputAtom :=
  {| output_left := QTConst 0;
     output_right := endpoint_term endpoint;
     output_strict := endpoint_strict endpoint |}.

Definition pair_atom (lower upper : QEndpoint) : QOutputAtom :=
  {| output_left := endpoint_term lower;
     output_right := endpoint_term upper;
     output_strict := orb (endpoint_strict lower) (endpoint_strict upper) |}.

Definition pair_atoms (lowers uppers : list QEndpoint) : list QOutputAtom :=
  List.flat_map (fun lower => List.map (pair_atom lower) uppers) lowers.

Definition eliminate_state (state : QElimState) : QOutputConjunction :=
  List.map residual_atom (state_residual state) ++
  pair_atoms (state_lower state) (state_upper state).

Definition eliminate_one (body : QAffineConjunction) : QDNF :=
  [eliminate_state (classify_constraints (normalize_conjunction body))].

Definition endpoints_compatible environment (lower upper : QEndpoint) : Prop :=
  if orb (endpoint_strict lower) (endpoint_strict upper)
  then endpoint_value environment lower < endpoint_value environment upper
  else endpoint_value environment lower <= endpoint_value environment upper.

Lemma eliminate_state_semantics : forall state environment,
    qoutput_conjunction_semantics environment (eliminate_state state) <->
    List.Forall (residual_holds environment) (state_residual state) /\
    List.Forall (fun lower => List.Forall
      (endpoints_compatible environment lower) (state_upper state))
      (state_lower state).
Proof.
  intros [residual lower upper] environment. unfold eliminate_state,
    qoutput_conjunction_semantics. cbn. rewrite Forall_app, Forall_map.
  split; intros [Hr Hp]; split.
  - exact Hr.
  - unfold pair_atoms in Hp. rewrite Forall_flat_map in Hp.
    apply Forall_forall. intros l Hl.
    apply Forall_forall with (x := l) in Hp; [|exact Hl].
    rewrite Forall_map in Hp. exact Hp.
  - exact Hr.
  - unfold pair_atoms. rewrite Forall_flat_map. apply Forall_forall.
    intros l Hl. rewrite Forall_map.
    apply Forall_forall with (x := l) in Hp; assumption.
Qed.

Fixpoint endpoint_max (environment : QEnvironment) (head : QEndpoint)
    (tail : list QEndpoint) : QEndpoint :=
  match tail with
  | [] => head
  | next :: rest =>
      endpoint_max environment
        (if Qlt_le_dec (endpoint_value environment head)
             (endpoint_value environment next) then next else head) rest
  end.

Fixpoint endpoint_min (environment : QEnvironment) (head : QEndpoint)
    (tail : list QEndpoint) : QEndpoint :=
  match tail with
  | [] => head
  | next :: rest =>
      endpoint_min environment
        (if Qlt_le_dec (endpoint_value environment head)
             (endpoint_value environment next) then head else next) rest
  end.

Lemma endpoint_max_in : forall environment head tail,
    List.In (endpoint_max environment head tail) (head :: tail).
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intro head; cbn; [now left|].
  destruct (Qlt_le_dec (endpoint_value environment head)
    (endpoint_value environment next)).
  - specialize (IH next). cbn in *. tauto.
  - specialize (IH head). cbn in *. tauto.
Qed.

Lemma endpoint_max_ge_head : forall environment head tail,
    endpoint_value environment head <=
      endpoint_value environment (endpoint_max environment head tail).
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intro head; cbn.
  - apply Qle_refl.
  - destruct (Qlt_le_dec (endpoint_value environment head)
      (endpoint_value environment next)) as [Hlt|Hle].
    + eapply Qle_trans; [apply Qlt_le_weak; exact Hlt|apply IH].
    + apply IH.
Qed.

Lemma endpoint_max_ge : forall environment head tail endpoint,
    List.In endpoint (head :: tail) ->
    endpoint_value environment endpoint <=
      endpoint_value environment (endpoint_max environment head tail).
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intros head endpoint Hin; cbn.
  - destruct Hin as [->|[]]. apply Qle_refl.
  - destruct (Qlt_le_dec (endpoint_value environment head)
      (endpoint_value environment next)) as [Hlt|Hle].
    + destruct Hin as [->|Hin].
      * eapply Qle_trans; [apply Qlt_le_weak; exact Hlt|].
        apply endpoint_max_ge_head.
      * apply IH. exact Hin.
    + destruct Hin as [->|[->|Hin]].
      * apply endpoint_max_ge_head.
      * eapply Qle_trans; [exact Hle|apply endpoint_max_ge_head].
      * apply IH. now right.
Qed.

Lemma endpoint_min_in : forall environment head tail,
    List.In (endpoint_min environment head tail) (head :: tail).
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intro head; cbn; [now left|].
  destruct (Qlt_le_dec (endpoint_value environment head)
    (endpoint_value environment next)).
  - specialize (IH head). cbn in *. tauto.
  - specialize (IH next). cbn in *. tauto.
Qed.

Lemma endpoint_min_le_head : forall environment head tail,
    endpoint_value environment (endpoint_min environment head tail) <=
      endpoint_value environment head.
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intro head; cbn.
  - apply Qle_refl.
  - destruct (Qlt_le_dec (endpoint_value environment head)
      (endpoint_value environment next)) as [Hlt|Hle].
    + apply IH.
    + eapply Qle_trans; [apply IH|exact Hle].
Qed.

Lemma endpoint_min_le : forall environment head tail endpoint,
    List.In endpoint (head :: tail) ->
    endpoint_value environment (endpoint_min environment head tail) <=
      endpoint_value environment endpoint.
Proof.
  intros environment head tail. revert head.
  induction tail as [|next rest IH]; intros head endpoint Hin; cbn.
  - destruct Hin as [->|[]]. apply Qle_refl.
  - destruct (Qlt_le_dec (endpoint_value environment head)
      (endpoint_value environment next)) as [Hlt|Hle].
    + destruct Hin as [->|[->|Hin]].
      * apply endpoint_min_le_head.
      * eapply Qle_trans; [apply endpoint_min_le_head|apply Qlt_le_weak; exact Hlt].
      * apply IH. now right.
    + destruct Hin as [->|Hin].
      * eapply Qle_trans; [apply endpoint_min_le_head|exact Hle].
      * apply IH. exact Hin.
Qed.

Lemma qle_lt_plus_one : forall value ceiling,
    value <= ceiling -> value < ceiling + 1.
Proof.
  intros value ceiling Hle. eapply Qle_lt_trans; [exact Hle|].
  assert (Hone : (0 : Q) < 1) by (unfold Qlt; cbn; lia).
  pose proof (proj2 (Qplus_lt_r 0 1 ceiling) Hone) as Hplus.
  setoid_replace (ceiling + 0) with ceiling in Hplus by ring. exact Hplus.
Qed.

Lemma qminus_one_lt_of_le : forall floor value,
    floor <= value -> floor - 1 < value.
Proof.
  intros floor value Hle. eapply Qlt_le_trans; [|exact Hle].
  assert (Hneg : (-1 : Q) < 0) by (unfold Qlt; cbn; lia).
  pose proof (proj2 (Qplus_lt_r (-1) 0 floor) Hneg) as Hplus.
  setoid_replace (floor + (-1)) with (floor - 1) in Hplus by ring.
  setoid_replace (floor + 0) with floor in Hplus by ring. exact Hplus.
Qed.

Lemma qrational_midpoint : forall lower upper,
    lower < upper ->
    lower < (lower + upper) / 2 /\
    (lower + upper) / 2 < upper.
Proof.
  intros lower upper Hlt. split.
  - apply Qlt_shift_div_l.
    + unfold Qlt; cbn; lia.
    + setoid_replace (lower * 2) with (lower + lower) by ring.
      setoid_replace (lower + upper) with (upper + lower) by ring.
      apply Qplus_lt_le_compat; [exact Hlt|apply Qle_refl].
  - apply Qlt_shift_div_r.
    + unfold Qlt; cbn; lia.
    + setoid_replace (upper * 2) with (upper + upper) by ring.
      apply Qplus_lt_le_compat; [exact Hlt|apply Qle_refl].
Qed.

Lemma finite_bounds_have_witness : forall environment lowers uppers,
    List.Forall (fun lower => List.Forall
      (endpoints_compatible environment lower) uppers) lowers ->
    exists bound,
      List.Forall (lower_holds environment bound) lowers /\
      List.Forall (upper_holds environment bound) uppers.
Proof.
  intros environment lowers uppers Hcompatible.
  destruct lowers as [|lower lower_tail]; destruct uppers as [|upper upper_tail].
  - exists 0. split; constructor.
  - set (least := endpoint_min environment upper upper_tail).
    exists (endpoint_value environment least - 1). split; [constructor|].
    apply Forall_forall. intros endpoint Hin.
    pose proof (endpoint_min_le environment upper upper_tail endpoint Hin) as Hle.
    unfold upper_holds. destruct (endpoint_strict endpoint).
    + apply qminus_one_lt_of_le. exact Hle.
    + apply Qlt_le_weak. apply qminus_one_lt_of_le. exact Hle.
  - set (greatest := endpoint_max environment lower lower_tail).
    exists (endpoint_value environment greatest + 1). split.
    + apply Forall_forall. intros endpoint Hin.
      pose proof (endpoint_max_ge environment lower lower_tail endpoint Hin) as Hle.
      unfold lower_holds. destruct (endpoint_strict endpoint).
      * apply qle_lt_plus_one. exact Hle.
      * apply Qlt_le_weak. apply qle_lt_plus_one. exact Hle.
    + constructor.
  - set (greatest := endpoint_max environment lower lower_tail).
    set (least := endpoint_min environment upper upper_tail).
    assert (Hgreatest_in : List.In greatest (lower :: lower_tail)).
    { unfold greatest. apply endpoint_max_in. }
    assert (Hleast_in : List.In least (upper :: upper_tail)).
    { unfold least. apply endpoint_min_in. }
    pose proof Hcompatible as Hallpairs.
    apply Forall_forall with (x := greatest) in Hcompatible; [|exact Hgreatest_in].
    apply Forall_forall with (x := least) in Hcompatible; [|exact Hleast_in].
    destruct (Qlt_le_dec (endpoint_value environment greatest)
      (endpoint_value environment least)) as [Hgap|Hnogap].
    + pose proof (qrational_midpoint _ _ Hgap) as [Hmid_lower Hmid_upper].
      unfold greatest, least in Hmid_lower, Hmid_upper.
      exists ((endpoint_value environment greatest +
        endpoint_value environment least) / 2). split.
      * apply Forall_forall. intros endpoint Hin.
        pose proof (endpoint_max_ge environment lower lower_tail endpoint Hin) as Hle.
        unfold lower_holds. destruct (endpoint_strict endpoint).
        -- eapply Qle_lt_trans; [exact Hle|exact Hmid_lower].
        -- apply Qlt_le_weak. eapply Qle_lt_trans;
             [exact Hle|exact Hmid_lower].
      * apply Forall_forall. intros endpoint Hin.
        pose proof (endpoint_min_le environment upper upper_tail endpoint Hin) as Hle.
        unfold upper_holds. destruct (endpoint_strict endpoint).
        -- eapply Qlt_le_trans; [exact Hmid_upper|exact Hle].
        -- apply Qlt_le_weak. eapply Qlt_le_trans;
             [exact Hmid_upper|exact Hle].
    + assert (Hequal : endpoint_value environment greatest ==
          endpoint_value environment least).
      { unfold endpoints_compatible in Hcompatible.
        destruct (orb (endpoint_strict greatest) (endpoint_strict least)).
        - exfalso. exact (Qlt_not_le _ _ Hcompatible Hnogap).
        - apply Qle_antisym; assumption. }
      exists (endpoint_value environment greatest). split.
      * apply Forall_forall. intros endpoint Hin.
        pose proof (endpoint_max_ge environment lower lower_tail endpoint Hin) as Hle.
        unfold lower_holds. destruct (endpoint_strict endpoint) eqn:Hstrict; [|exact Hle].
        pose proof Hallpairs as Hpair.
        apply Forall_forall with (x := endpoint) in Hpair; [|exact Hin].
        apply Forall_forall with (x := least) in Hpair;
          [|exact Hleast_in].
        unfold endpoints_compatible in Hpair. rewrite Hstrict in Hpair. cbn in Hpair.
        setoid_rewrite <- Hequal in Hpair. exact Hpair.
      * apply Forall_forall. intros endpoint Hin.
        pose proof (endpoint_min_le environment upper upper_tail endpoint Hin) as Hle.
        unfold upper_holds. destruct (endpoint_strict endpoint) eqn:Hstrict; [|].
        -- pose proof Hallpairs as Hall.
           apply Forall_forall with (x := greatest) in Hall; [|exact Hgreatest_in].
           apply Forall_forall with (x := endpoint) in Hall; [|exact Hin].
           unfold endpoints_compatible in Hall. rewrite Hstrict, orb_true_r in Hall.
           exact Hall.
        -- setoid_rewrite Hequal. exact Hle.
Qed.

Lemma state_exists_iff_eliminated : forall state environment,
    (exists bound, state_semantics environment bound state) <->
    qoutput_conjunction_semantics environment (eliminate_state state).
Proof.
  intros state environment. rewrite eliminate_state_semantics.
  split.
  - intros [bound [Hr [Hl Hu]]]. split; [exact Hr|].
    apply Forall_forall. intros lower Hlower.
    apply Forall_forall. intros upper Hupper.
    apply Forall_forall with (x := lower) in Hl; [|exact Hlower].
    apply Forall_forall with (x := upper) in Hu; [|exact Hupper].
    unfold lower_holds in Hl. unfold upper_holds in Hu.
    unfold endpoints_compatible.
    destruct (endpoint_strict lower), (endpoint_strict upper); cbn in *.
    + eapply Qlt_trans; eauto.
    + eapply Qlt_le_trans; eauto.
    + eapply Qle_lt_trans; eauto.
    + eapply Qle_trans; eauto.
  - intros [Hr Hpairs].
    destruct (finite_bounds_have_witness environment
      (state_lower state) (state_upper state) Hpairs) as [bound [Hl Hu]].
    exists bound. repeat split; assumption.
Qed.

Theorem eliminate_one_correct : forall body environment,
    (exists bound,
      qconjunction_semantics (qenvironment_extend environment bound) body) <->
    qdnf_semantics environment (eliminate_one body).
Proof.
  intros body environment. unfold eliminate_one.
  assert (Hsingleton : qdnf_semantics environment
      [eliminate_state (classify_constraints (normalize_conjunction body))] <->
      qoutput_conjunction_semantics environment
        (eliminate_state (classify_constraints (normalize_conjunction body)))).
  { unfold qdnf_semantics. split.
    - intros [output [[Heq|Hfalse] Hsem]]; [subst output; exact Hsem|contradiction].
    - intro Hsem. exists (eliminate_state
        (classify_constraints (normalize_conjunction body))).
      split; [now left|exact Hsem]. }
  rewrite Hsingleton, <- state_exists_iff_eliminated.
  split; intros [bound Hbody]; exists bound.
  - apply (proj1 (classify_constraints_correct
      (normalize_conjunction body) environment bound)).
    apply (proj1 (normalize_conjunction_correct body environment bound)).
    exact Hbody.
  - apply (proj2 (normalize_conjunction_correct body environment bound)).
    apply (proj2 (classify_constraints_correct
      (normalize_conjunction body) environment bound)). exact Hbody.
Qed.
