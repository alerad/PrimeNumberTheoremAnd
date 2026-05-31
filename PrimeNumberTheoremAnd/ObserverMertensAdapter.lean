import PrimeNumberTheoremAnd.IEANTN.Mertens

open Finset Filter Topology Real
open Asymptotics
open scoped BigOperators

namespace ObserverMertensAdapter

def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

noncomputable def prodMinus (n : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))

theorem prodMinus_eq_mertensProduct (n : ℕ) :
    prodMinus n =
      ∏ p ∈ Finset.Ioc 0 ⌊(n : ℝ)⌋₊ with p.Prime, (1 - (1 : ℝ) / p) := by
  unfold prodMinus primesUpTo
  apply Finset.prod_congr
  · ext p
    simp only [mem_filter, mem_range, mem_Ioc, Nat.floor_natCast]
    constructor
    · intro h
      exact ⟨⟨Nat.Prime.pos h.2, Nat.lt_succ_iff.mp h.1⟩, h.2⟩
    · intro h
      exact ⟨Nat.lt_succ_iff.mpr h.1.2, h.2⟩
  · intro p hp
    rfl

theorem mertens_third_from_pnt_mertens :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * prodMinus n)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  let f : ℝ → ℝ :=
    fun x => ∏ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p)
  let g : ℝ → ℝ := fun x => Real.exp (-Real.eulerMascheroniConstant) / Real.log x

  have hprod_real : f ~[atTop] g := by
    simpa [f, g] using Mertens.E₃.bound''

  have hprod_nat : (fun n : ℕ => prodMinus n) ~[atTop]
      (fun n : ℕ => Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)) := by
    have hcomp := hprod_real.comp_tendsto (k := fun n : ℕ => (n : ℝ))
      tendsto_natCast_atTop_atTop
    exact hcomp.congr_left (Filter.Eventually.of_forall fun n => by
      simp [f, prodMinus_eq_mertensProduct n])

  have hmul : (fun n : ℕ => Real.log (n : ℝ) * prodMinus n) ~[atTop]
      (fun n : ℕ =>
        Real.log (n : ℝ) *
          (Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ))) := by
    exact (show (fun n : ℕ => Real.log (n : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) from IsEquivalent.refl).mul hprod_nat

  have htarget : Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) *
          (Real.exp (-Real.eulerMascheroniConstant) / Real.log (n : ℝ)))
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : Real.log (n : ℝ) ≠ 0 := by
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      exact (Real.log_ne_zero_of_pos_of_ne_one (by positivity : (0 : ℝ) < n)
        (by linarith : (n : ℝ) ≠ 1))
    field_simp [hlog]

  exact hmul.symm.tendsto_nhds htarget

theorem mertens_third :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * prodMinus n)
      atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
  mertens_third_from_pnt_mertens

end ObserverMertensAdapter
