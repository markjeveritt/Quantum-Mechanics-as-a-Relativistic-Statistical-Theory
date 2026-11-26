module
public import FreeShellDirac
public import FreeShellRadial
import all MassShell
public section

namespace MassShell.FreeSeries
open CompositionAndTransport CompositionAndTransport.FreeShellRadial
noncomputable section
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
abbrev Seq := ℕ → ScalarDistribution
abbrev Poly := MvPolynomial (Option Axis) ℂ

def px (i : Fin 4) : Poly := MvPolynomial.X (some (.inr i))
def dx (i : Fin 4) : Poly := MvPolynomial.X (some (.inl i))
def h : Poly := MvPolynomial.X none
def bopp (c : ℂ) (i : Fin 4) : Poly := px i + MvPolynomial.C c * h * dx i

def each (f : Operator) : Module.End ℂ Seq where
  toFun u n := f (u n)
  map_add' _ _ := funext fun _ => f.map_add _ _
  map_smul' _ _ := funext fun _ => f.map_smul _ _

def shift : Module.End ℂ Seq where
  toFun u := fun | 0 => 0 | n+1 => u n
  map_add' u v := by funext n; cases n <;> simp
  map_smul' c u := by funext n; cases n with
    | zero => ext φ; change (0 : ℂ) = c * 0; ring
    | succ n => rfl

def base : Axis → Operator := Sum.elim (fun i => «partial» (.inl i)) momentum

theorem base_comm (i j : Axis) : Commute (base i) (base j) := by
  cases i with
  | inl i => cases j with
             | inl j => exact partial_commute _ _
             | inr j => exact partial_x_commute _ _
  | inr i => cases j with
             | inl j => exact (partial_x_commute _ _).symm
             | inr j => exact momentum_commute _ _

def varOp : Option Axis → Module.End ℂ Seq
  | none => shift
  | some i => each (base i)

theorem varOp_comm (i j : Option Axis) : Commute (varOp i) (varOp j) := by
  have hs (f : Operator) : Commute shift (each f) := by
    ext u n : 2
    cases n with
    | zero => exact (map_zero f).symm
    | succ n => rfl
  cases i with
  | none => cases j with
            | none => exact Commute.refl _
            | some j => exact hs _
  | some i => cases j with
              | none => exact (hs _).symm
              | some j =>
                apply LinearMap.ext
                intro u
                funext n
                exact DFunLike.congr_fun (base_comm i j).eq (u n)

def evaluate : Poly →ₐ[ℂ] Module.End ℂ Seq := commuting_calculus varOp varOp_comm
scoped instance seriesModule : Module Poly Seq := Module.compHom Seq evaluate.toRingHom
scoped instance (priority := high) polySMul : SMul Poly Seq := seriesModule.toSMul
open scoped MassShell.FreeSeries

theorem C_apply (c : ℂ) (u : Seq) (n : ℕ) : ((MvPolynomial.C c : Poly) • u : Seq) n = c • u n := by
  change (evaluate (algebraMap ℂ Poly c)) u n = _
  rw [AlgHom.commutes]
  rfl

private theorem X_apply (i : Option Axis) (u : Seq) :
    (MvPolynomial.X i : Poly) • u = varOp i u := by
  change (commuting_calculus varOp varOp_comm (MvPolynomial.X i)) u = _
  rw [lemma_calculus_variable]

theorem px_apply (i : Fin 4) (u : Seq) (n : ℕ) : (px i • u) n = momentum i (u n) :=
  congrFun (X_apply _ _) n

theorem dx_apply (i : Fin 4) (u : Seq) (n : ℕ) : (dx i • u) n = «partial» (.inl i) (u n) :=
  congrFun (X_apply _ _) n

theorem h_zero (u : Seq) : (h • u) 0 = 0 := congrFun (X_apply _ _) 0
theorem h_succ (u : Seq) (n : ℕ) : (h • u) (n+1) = u n := congrFun (X_apply _ _) (n+1)

end
end MassShell.FreeSeries
