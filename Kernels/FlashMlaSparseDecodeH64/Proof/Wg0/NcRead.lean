-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Addr
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Warpgroup 0's length loads read the row's words

-- domain: consistent

The event a warpgroup-0 state at a length load fires (`Wg0.lenOk`, `Wg0/Nc.lean`) is the `.nc`
read of the four bytes of the row's word (`topk_read`, `extra_read`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}
  {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- A length load fires from the state's first element. -/
private theorem sub_zero (hinv : (code P L g w).inv d) (hsub : t.sub = d.el) {s : Site}
    (hs : d.site = s) (h1 : elems s = 1) : t.sub = 0 := by
  have h : d.el < elems d.site := hinv
  rw [hs, h1] at h
  rw [hsub]
  exact Nat.lt_one_iff.mp h

/-- **The top-k length load reads the row's word.** -/
theorem topk_read (hp : Pre P L m) {x : Nat} (hx : P.topkLenBase = some x)
    (hs : d.site = .lenA) (hat : (code P L g w).AtD d t) (hinv : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.topkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g w).pc d = 168 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3140) (by rw [hs]; decide +kernel)
  simp only [valueOf, values, valuesLen, valuesLoop, valuesConst, valuesSetup, hx,
    Option.getD_some, List.lookup, List.cons_append, List.nil_append, Nat.reduceBEq] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_168)
  exact len_read hp hrange hal hpc (sub_zero hinv hsub hs rfl) hreg (by decide) hf

/-- **The extra length load reads the row's word.** -/
theorem extra_read (hp : Pre P L m) {x : Nat} (hx : P.extraTopkLenBase = some x)
    (hs : d.site = .lenB) (hat : (code P L g w).AtD d t) (hinv : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.extraTopkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g w).pc d = 181 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3142) (by rw [hs]; decide +kernel)
  simp only [valueOf, values, valuesLen, valuesLoop, valuesConst, valuesSetup, hx,
    Option.getD_some, List.lookup, List.cons_append, List.nil_append, Nat.reduceBEq] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_181)
  exact len_read hp hrange hal hpc (sub_zero hinv hsub hs rfl) hreg (by decide) hf

/-- **The sink load reads the head's word**: the four bytes at `x + 4 (t % 64)` (the sink's head
`t % 64`, `%r10`). -/
theorem sink_read (hp : Pre P L m) {x : Nat} (hx : P.sinkBase = some x)
    (hs : d.site = .sink) (hat : (code P L g w).AtD d t) (hinv : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * (tidOf L g % 64)) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.sinkAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g w).pc d = 156 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3138) (by rw [hs]; decide +kernel)
  simp only [valueOf, values, valuesLen, valuesLoop, valuesConst, valuesSetup, hx,
    Option.getD_some, List.lookup, List.cons_append, List.nil_append, Nat.reduceBEq] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_156)
  have hr10 : r10W L g = W (tidOf L g % 64) := andi_W_low (k := 6) (tidOf_lt hp g) (by decide)
  have hrow : tidOf L g % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hw : add64 (pw8 x) (mulWide .u (r10W L g) 4) = W (x + 4 * (tidOf L g % 64)) := by
    rw [pw8_eq x (by omega), hr10]
    exact lenAddr_eq (by omega) (by omega)
  rw [hw] at hreg
  have hA : Assumptions.all.any (·.ncLoads t.pc) = true := by
    have hm : 156 ∈ ncLoads := by decide
    rw [hpc]
    simp [Assumptions.all, Assumptions.ncReadOnly, Assumption.ncReadOnly, hm]
  have hf' : Fires 156 (loadTmpl Assumptions.all L g t .global true 32 [932] 3138 0) e o := hf
  rw [loadTmpl_global_nc (sub_zero hinv hsub hs rfl) hreg (by omega) (by decide) (by omega)
    hA] at hf'
  obtain ⟨bs, -, rfl, -⟩ := hf'
  exact ⟨bs, rfl, by show ncLoads.contains 156 = true; decide⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
