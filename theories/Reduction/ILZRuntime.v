From Coq Require Import List.
Require Import Yalla.fmformulas Yalla.nn_def.
From Yalla.OLlibs Require Import BOrders fmsetlist_Type.
From Mell.Logic Require Import Syntax.

Import ListNotations.
Module RuntimeIF := Yalla.iformulas.

Fixpoint mell_to_linear (formula : Syntax.formula) : Yalla.formulas.formula :=
  match formula with
  | Syntax.Atom atom => Yalla.formulas.var atom
  | Syntax.CoAtom atom => Yalla.formulas.covar atom
  | Syntax.One => Yalla.formulas.one
  | Syntax.Bottom => Yalla.formulas.bot
  | Syntax.Tensor left_formula right_formula =>
      Yalla.formulas.tens
        (mell_to_linear left_formula) (mell_to_linear right_formula)
  | Syntax.Par left_formula right_formula =>
      Yalla.formulas.parr
        (mell_to_linear left_formula) (mell_to_linear right_formula)
  | Syntax.Bang body => Yalla.formulas.oc (mell_to_linear body)
  | Syntax.WhyNot body => Yalla.formulas.wn (mell_to_linear body)
  end.

Definition classical_linear_sequent_runtime (Gamma : Syntax.sequent) :
    list Yalla.formulas.formula :=
  @elts (SortedList Yalla.fmformulas.border_formula) Yalla.formulas.formula
    Yalla.fmformulas.fmset_formula
    (@list2fm (SortedList Yalla.fmformulas.border_formula)
      Yalla.formulas.formula Yalla.fmformulas.fmset_formula
      (List.map mell_to_linear Gamma)).

Definition RuntimeILZGoal : Type :=
  (list RuntimeIF.iformula * RuntimeIF.iformula)%type.

Definition translation_atom_runtime (Gamma : Syntax.sequent) :
    Yalla.yalla_ax.Atom :=
  Yalla.subs.fresh_of_list Yalla.yalla_ax.a2n Yalla.yalla_ax.n2a
    (classical_linear_sequent_runtime Gamma).

Definition translation_parameter_runtime (Gamma : Syntax.sequent) :
    RuntimeIF.iformula :=
  RuntimeIF.ivar (Yalla.yalla_ax.a2i (translation_atom_runtime Gamma)).

Fixpoint close_ilz_context_runtime
    (context : list RuntimeIF.iformula) (conclusion : RuntimeIF.iformula) :
    RuntimeIF.iformula :=
  match context with
  | [] => conclusion
  | formula :: tail =>
      close_ilz_context_runtime tail (RuntimeIF.ilmap formula conclusion)
  end.

Definition translate_mell_runtime (Gamma : Syntax.sequent) : RuntimeILZGoal :=
  ([], close_ilz_context_runtime
    (List.map (Yalla.nn_def.trans (translation_parameter_runtime Gamma))
      (classical_linear_sequent_runtime Gamma))
    (translation_parameter_runtime Gamma)).

Definition runtime_iformula_eq_dec : forall left right : RuntimeIF.iformula,
    {left = right} + {left <> right}.
Proof.
  decide equality.
  destruct (Yalla.yalla_ax.iateq i i0) eqn:Heq.
  - left. now apply Yalla.yalla_ax.iateq_eq.
  - right. intro H; subst.
    rewrite (proj2 (Yalla.yalla_ax.iateq_eq _ _) eq_refl) in Heq.
    discriminate.
Defined.

Fixpoint raw_runtime_ilz_subformulas
    (formula : RuntimeIF.iformula) : list RuntimeIF.iformula :=
  formula ::
  match formula with
  | RuntimeIF.ivar _ | RuntimeIF.ione | RuntimeIF.itop | RuntimeIF.izero => []
  | RuntimeIF.itens left_formula right_formula
  | RuntimeIF.ilpam left_formula right_formula
  | RuntimeIF.ilmap left_formula right_formula
  | RuntimeIF.iwith left_formula right_formula
  | RuntimeIF.iplus left_formula right_formula =>
      raw_runtime_ilz_subformulas left_formula ++
      raw_runtime_ilz_subformulas right_formula
  | RuntimeIF.igen body | RuntimeIF.ineg body =>
      RuntimeIF.N :: raw_runtime_ilz_subformulas body
  | RuntimeIF.ioc body => raw_runtime_ilz_subformulas body
  end.

Definition runtime_ilz_goal_formulas (goal : RuntimeILZGoal) :
    list RuntimeIF.iformula := snd goal :: fst goal.

Definition runtime_ilz_subformulas (goal : RuntimeILZGoal) :
    list RuntimeIF.iformula :=
  nodup runtime_iformula_eq_dec
    (flat_map raw_runtime_ilz_subformulas (runtime_ilz_goal_formulas goal)).
