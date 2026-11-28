-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.RefNext

@[expose] public section

/-! # The paired Tensor Memory operations at a trace event

The ledger class `Cls.tmem` counts a thread's paired Tensor Memory operations
(`Tmem.Pair.isTmemOp`); the startup's slot keeps `Startup.RefT`, warpgroup 0's `Wg0.TmemAt` at
that count. `startup_tmem` and `wg0_tmem` take them at a trace event, at the thread's prefix
count `Tmem.Pair.tmemOps`; `exit_tmem`: a lane of warp 0 exits after three operations (its exit
is warpgroup 0's, the one case split on the role). The roles' exports import this file
privately. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The class `tmem` counts the paired operations. -/
theorem count_tmem {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) :
    σ.2 .tmem = Tmem.Pair.tmemOps ((X.tr g).take k) :=
  state_count hσ .tmem

/-- **A startup event at its count and warp words**: its state's `RefT` at the thread's prefix
count and its `RefW`. -/
theorem startup_tmemW (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc : e.pc < 103) :
    ∃ d sh, Startup.RefT d (Tmem.Pair.tmemOps ((X.tr g).take k)) ∧ Startup.RefW L g d sh ∧
      Startup.Ev L g d e ∧ Startup.exitOf d = none := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hW, hE, hx, -⟩ := startup_state hJ hi hev hpc' hpc
  obtain ⟨-, -, hT⟩ := hJ
  rw [show n .tmem = _ from count_tmem hσ] at hT
  exact ⟨d, _, hT, hW, hE, hx⟩

/-- **A startup event at its count**: its state's `RefT` at the thread's prefix count. -/
theorem startup_tmem (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hpc : e.pc < 103) :
    ∃ d, Startup.RefT d (Tmem.Pair.tmemOps ((X.tr g).take k)) ∧ Startup.Ev L g d e ∧
      Startup.exitOf d = none := by
  obtain ⟨d, -, hT, -, hE, hx⟩ := startup_tmemW hp hX hFw he hub hpc
  exact ⟨d, hT, hE, hx⟩

/-- **A warpgroup-0 event at its count**: its state's `TmemAt` at the thread's prefix count. -/
theorem wg0_tmem (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hr : 103 ≤ e.pc ∧ e.pc < 1842) :
    ∃ d : Wg0.Control.D, Wg0.TmemAt (warpW L g) d (Tmem.Pair.tmemOps ((X.tr g).take k)) ∧
      Wg0.Ev P L g (warpW L g) d e := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc hr
  obtain ⟨-, ⟨-, hT⟩, -, -⟩ := hJ
  have hT := hT (state_ub hX hσ he)
  rw [show n .tmem = _ from count_tmem hσ] at hT
  exact ⟨d, hT, hE⟩

/-- The warp word is `0` exactly in warp 0. -/
theorem warpW_zero (hp : Pre P L m) :
    scmpi .ne .b (warpW L g) 0 = false ↔ warp L g = 0 := by
  rw [Startup.warpW_ne hp]
  simp only [warpOf, tidOf_eq hp, warp, tidOf_x_eq hp, decide_eq_false_iff_not, not_not]

/-- **A lane of warp 0 exits after three paired operations**: its exit is warpgroup 0's return,
after the deallocation. -/
theorem exit_tmem (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hw : warp L g = 0) : Tmem.Pair.tmemOps ((X.tr g).take k) = 3 := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun f h => by cases h)
  have hR := state_role hJ hi
  have hw' : warpOf L g = 0 := by
    simp only [warp, tidOf_x_eq hp] at hw
    simp only [warpOf, tidOf_eq hp, hw]
  cases hR with
  | startup d n _ _ hx _ _ =>
    exfalso
    have hE : Startup.Ev L g d ⟨pc, .exit⟩ := hev
    obtain ⟨site, x1, x2⟩ := d
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hE
    | enter r => simp [Startup.exitOf] at hx
    | _ => simp [Startup.Ev] at hE
  | wg0 d n _ _ _ _ =>
    obtain ⟨-, ⟨-, hT⟩, -, -⟩ := hJ
    have hT := hT (state_ub hX hσ he)
    rw [show n .tmem = _ from count_tmem hσ] at hT
    have hs : (d : Wg0.Control.D).site = .exit := by
      obtain ⟨-, hE⟩ : Wg0.Ev P L g (warpW L g) d ⟨pc, .exit⟩ := hev
      obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
      cases s <;> simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
        Wg0.PollEv, Wg0.ArrEv] at hE ⊢
    have h0 : scmpi .ne .b (warpW L g) 0 = false := (warpW_zero hp).2 hw
    simp [Wg0.TmemAt, hs, h0] at hT
    exact hT
  | head _ _ _ _ _ _ h => omega
  | idle _ _ _ h _ _ => omega
  | index _ _ _ h _ _ => omega
  | mma _ _ _ _ _ h _ _ => omega
  | tma _ _ _ _ _ h _ _ => omega
  | dequant _ _ _ h _ _ => omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
