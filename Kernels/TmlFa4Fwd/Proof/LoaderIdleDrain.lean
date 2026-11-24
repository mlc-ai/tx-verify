-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderDrainPoll
public import Kernels.TmlFa4Fwd.Proof.LoaderIdle
public import Kernels.TmlFa4Fwd.Proof.LoaderExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The idle cursor visits all three KV release barriers at parity one. -/
def idleRelease (l : Launch) (g : Nat) (slot : Fin 3) (ok : Bool) : Event :=
  ⟨(drainWaitSite ⟨slot.val, by omega⟩).pc,
    .wait ⟨.shared, g / l.block, l.sharedBase + 56 + 8 * slot.val⟩ 1 ok true .cta⟩

def idleDrainCarry (l : Launch) (warp : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (258, .pred (decide (warp ≠ 14))), (7192, b32 1), (1062, b32 warp)]

/-- Registers retained across one initialized cache drain wait. -/
def idleSlotFacts (l : Launch) (warp : Nat) : Fin 3 → List (Nat × Value)
  | 0 => [(2288, b32 (l.sharedBase + 56)), (7180, b32 1), (7179, b32 0)] ++ idleDrainCarry l warp
  | 1 => [(2289, b32 (l.sharedBase + 64)), (2290, b32 1), (2296, b32 1)] ++ idleDrainCarry l warp
  | 2 => [(2291, b32 (l.sharedBase + 72)), (2292, b32 1), (2301, b32 2)] ++ idleDrainCarry l warp

/-- The local path from idle mode to the first cache release wait. -/
theorem idleFirst (l : Launch) (g : Nat) {warp : Nat} (hw : warp < 16)
    (hBase : l.sharedBase + 72 < 2 ^ 32) :
    Seg kernel [] l g 4 1862 (loaderIdleDrainFacts l warp) 1866 (idleSlotFacts l warp 0) := by
  intro t ht
  have hw32 : warp < 2 ^ 32 := by omega
  have hw64 : warp < 2 ^ 64 := by omega
  have h14 : (truncBits 32 (BitVec.ofInt 64 14)).toNat = 14 := rfl
  unfold loaderIdleDrainFacts at ht
  simp only [idleSlotFacts, idleDrainCarry, List.cons_append, List.nil_append]
  seg_fp ht using
    first
    | simp only [compare, Option.getD_some, truncBits_ofNat hw32 (by decide),
        toNat_ofNat_lt hw64, h14, ne_eq, Int.ofNat_inj]
    | norm_bits

/-- The local path between consecutive cache release waits. -/
theorem idleAdvance (slot : Fin 2) (l : Launch) (g warp : Nat)
    (hBase : l.sharedBase + 72 < 2 ^ 32) :
    let i : Fin 3 := ⟨slot.val, by omega⟩
    let j : Fin 3 := ⟨slot.val + 1, by omega⟩
    Seg kernel [] l g 8 ((drainWaitSite ⟨i.val, by omega⟩).pc + 3) (idleSlotFacts l warp i)
      (drainWaitSite ⟨j.val, by omega⟩).pc (idleSlotFacts l warp j) := by
  fin_cases slot
  · change Seg kernel [] l g 8 1869 (idleSlotFacts l warp 0) 1877 (idleSlotFacts l warp 1)
    intro t ht
    simp only [idleSlotFacts, idleDrainCarry, List.cons_append, List.nil_append] at ht ⊢
    seg_fp ht using first | rfl | norm_bits
  · change Seg kernel [] l g 8 1880 (idleSlotFacts l warp 1) 1888 (idleSlotFacts l warp 2)
    intro t ht
    simp only [idleSlotFacts, idleDrainCarry, List.cons_append, List.nil_append] at ht ⊢
    seg_fp ht using first | rfl | norm_bits

private theorem idleSlotTrace {l : Launch} {g warp : Nat} {t : TState} {events : List Event}
    (slot : Fin 3) (hBound : l.sharedBase + 72 < 2 ^ 32) (hAlign : l.sharedBase % 8 = 0)
    (ht : At t (drainWaitSite ⟨slot.val, by omega⟩).pc (idleSlotFacts l warp slot))
    (hr : Run kernel Assumptions.all l g t events none) :
    ∃ n u rest, events = List.replicate n (idleRelease l g slot false) ++
        (idleRelease l g slot true :: rest) ∧
      At u ((drainWaitSite ⟨slot.val, by omega⟩).pc + 3) (idleSlotFacts l warp slot) ∧
      Run kernel Assumptions.all l g u rest none := by
  have hSlot := slot.isLt
  have hAddress : l.sharedBase + 56 + 8 * slot.val < 2 ^ 32 := by omega
  have hAligned : (l.sharedBase + 56 + 8 * slot.val) % 8 = 0 := by omega
  exact drainWaitTrace (⟨slot.val, by omega⟩ : Fin 4) hAddress hAligned (by decide)
    (by
      intro x hm he
      have hx := List.mem_map_of_mem (f := Prod.fst) hm
      rw [he] at hx
      exact (show (drainWaitSite ⟨slot.val, by omega⟩).result ∉
          (idleSlotFacts l warp slot).map Prod.fst by
        fin_cases slot <;> exact of_decide_eq_true rfl) hx)
    (by fin_cases slot <;> simp [idleSlotFacts, drainWaitSite])
    (by fin_cases slot <;> simp [idleSlotFacts, drainWaitSite]) ht hr

/-- A terminated idle loader suffix has three finite retries, observing one release per
stage at the expected address and parity. The actual continuation is the warp-role split. -/
theorem loaderIdleKvDrained {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp : Nat} (hw : warp < 16) {t : TState} {events : List Event}
    (ht : At t 1862 (loaderIdleDrainFacts l warp))
    (hr : Run kernel Assumptions.all l g t events none) :
    ∃ (n : Fin 3 → Nat) (u : TState) (rest : List Event), events =
      (List.replicate (n 0) (idleRelease l g 0 false) ++ [idleRelease l g 0 true]) ++
      (List.replicate (n 1) (idleRelease l g 1 false) ++ [idleRelease l g 1 true]) ++
      (List.replicate (n 2) (idleRelease l g 2 false) ++ [idleRelease l g 2 true]) ++ rest ∧
      At u 1891 (idleDrainCarry l warp) ∧ Run kernel Assumptions.all l g u rest none := by
  have hBound : l.sharedBase + 72 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAlign : l.sharedBase % 8 = 0 := by have := hp.shared.1; omega
  obtain ⟨t0, h0, ht0⟩ := idleFirst l g hw hBound t ht
  obtain ⟨h0A, _⟩ := loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) h0
  obtain ⟨n0, u0, tail0, he0, hu0, hRun0⟩ := idleSlotTrace 0 hBound hAlign ht0
    (hr.after_local (run_rtg h0A))
  obtain ⟨t1, h1, ht1⟩ := idleAdvance 0 l g warp hBound u0 hu0
  have hPc0 : u0.pc = 1869 := hu0.1
  obtain ⟨h1A, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hPc0
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) h1
  obtain ⟨n1, u1, tail1, he1, hu1, hRun1⟩ := idleSlotTrace 1 hBound hAlign ht1
    (hRun0.after_local (run_rtg h1A))
  obtain ⟨t2, h2, ht2⟩ := idleAdvance 1 l g warp hBound u1 hu1
  have hPc1 : u1.pc = 1880 := hu1.1
  obtain ⟨h2A, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hPc1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) h2
  obtain ⟨n2, u2, rest, he2, hu2, hRun2⟩ := idleSlotTrace 2 hBound hAlign ht2
    (hRun1.after_local (run_rtg h2A))
  let n : Fin 3 → Nat := ![n0, n1, n2]
  exact ⟨n, u2, rest, by rw [he0, he1, he2]; simp [n, List.append_assoc],
    hu2.mono hu2.2.2.2.2.2.2.2, hRun2⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
