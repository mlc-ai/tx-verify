-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Flow.Code.Part000
public import Kernels.TmlFa4Fwd.Flow.Code.Part001
public import Kernels.TmlFa4Fwd.Flow.Code.Part002
public import Lemmas.Flow.Regs
public import Lemmas.Flow.Next
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX Proof

noncomputable section

/-- The shared mbarrier locations and initial arrival counts in PTX issue order.
The effective address is the dynamic shared base plus `baseOffset + displacement`. -/
structure InitSite where
  pc : Nat
  baseReg : Nat
  baseOffset : Nat
  displacement : Nat
  countReg : Nat
  count : Nat

def initSites : Vector InitSite 34 := #v[
  ⟨50, 2535, 0, 0, 1675, 1⟩,
  ⟨51, 2535, 0, 8, 1675, 1⟩,
  ⟨60, 1064, 16, 0, 1677, 1⟩,
  ⟨61, 2535, 0, 24, 1677, 1⟩,
  ⟨66, 1063, 32, 0, 1679, 64⟩,
  ⟨67, 2535, 0, 40, 1679, 64⟩,
  ⟨68, 2535, 0, 48, 1679, 64⟩,
  ⟨77, 1066, 56, 0, 1681, 1⟩,
  ⟨78, 2535, 0, 64, 1681, 1⟩,
  ⟨79, 2535, 0, 72, 1681, 1⟩,
  ⟨84, 1065, 80, 0, 1683, 1⟩,
  ⟨85, 2535, 0, 88, 1683, 1⟩,
  ⟨94, 1068, 96, 0, 1685, 256⟩,
  ⟨95, 2535, 0, 104, 1685, 256⟩,
  ⟨100, 1067, 112, 0, 1687, 4⟩,
  ⟨101, 2535, 0, 120, 1687, 4⟩,
  ⟨109, 2535, 0, 128, 1689, 1⟩,
  ⟨110, 2535, 0, 136, 1689, 1⟩,
  ⟨115, 6495, 144, 0, 1691, 1⟩,
  ⟨116, 2535, 0, 152, 1691, 1⟩,
  ⟨123, 2535, 0, 160, 1693, 128⟩,
  ⟨124, 2535, 0, 168, 1693, 128⟩,
  ⟨129, 2535, 0, 176, 1695, 128⟩,
  ⟨130, 2535, 0, 184, 1695, 128⟩,
  ⟨139, 1069, 192, 0, 1697, 128⟩,
  ⟨140, 2535, 0, 200, 1697, 128⟩,
  ⟨145, 2390, 208, 0, 1699, 128⟩,
  ⟨146, 2535, 0, 216, 1699, 128⟩,
  ⟨155, 6497, 224, 0, 1701, 32⟩,
  ⟨156, 2535, 0, 232, 1701, 32⟩,
  ⟨161, 1070, 320, 0, 1703, 1⟩,
  ⟨162, 2535, 0, 328, 1703, 1⟩,
  ⟨170, 1071, 336, 0, 1705, 4⟩,
  ⟨171, 2535, 0, 344, 1705, 4⟩]

def initSite (i : Fin 34) : InitSite := initSites[i]

theorem initCode (i : Fin 34) :
    let s := initSite i
    kernel.code[s.pc]? = some ⟨none, .mbarInit s.baseReg s.displacement (.reg s.countReg)⟩ := by
  fin_cases i
  · exact Flow.code_50
  · exact Flow.code_51
  · exact Flow.code_60
  · exact Flow.code_61
  · exact Flow.code_66
  · exact Flow.code_67
  · exact Flow.code_68
  · exact Flow.code_77
  · exact Flow.code_78
  · exact Flow.code_79
  · exact Flow.code_84
  · exact Flow.code_85
  · exact Flow.code_94
  · exact Flow.code_95
  · exact Flow.code_100
  · exact Flow.code_101
  · exact Flow.code_109
  · exact Flow.code_110
  · exact Flow.code_115
  · exact Flow.code_116
  · exact Flow.code_123
  · exact Flow.code_124
  · exact Flow.code_129
  · exact Flow.code_130
  · exact Flow.code_139
  · exact Flow.code_140
  · exact Flow.code_145
  · exact Flow.code_146
  · exact Flow.code_155
  · exact Flow.code_156
  · exact Flow.code_161
  · exact Flow.code_162
  · exact Flow.code_170
  · exact Flow.code_171

private theorem initRanges (i : Fin 34) :
    let s := initSite i
    s.baseOffset + s.displacement ≤ 344 ∧ (s.baseOffset + s.displacement) % 8 = 0 ∧
      0 < s.count ∧ s.count < 2 ^ 20 := by
  fin_cases i <;> decide

/-- The initializer's physical object, kept in shared memory for the CTA. -/
def initObject (l : Launch) (cta : Nat) (i : Fin 34) : Loc :=
  ⟨.shared, cta, l.sharedBase + (initSite i).baseOffset + (initSite i).displacement⟩

private theorem initOffsetInj : Function.Injective (fun i : Fin 34 =>
    (initSite i).baseOffset + (initSite i).displacement) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | cases h

/-- Distinct initializers name distinct eight-byte objects. -/
theorem initObject_ne {l : Launch} {cta : Nat} {i j : Fin 34} (h : i ≠ j) :
    initObject l cta i ≠ initObject l cta j := by
  intro hLoc
  apply h
  apply initOffsetInj
  dsimp only
  have hAddr := congrArg Loc.addr hLoc
  dsimp only [initObject] at hAddr
  omega

/-- Each initialized object is eight-byte aligned and allocated through its last byte. -/
theorem initObject_allocated {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {cta : Nat} (hc : cta < l.grid) (i : Fin 34) :
    (initObject l cta i).addr % 8 = 0 ∧ ∀ k < 8, m ((initObject l cta i).at k) ≠ none := by
  obtain ⟨hBound, hAlign, _, _⟩ := initRanges i
  refine ⟨?_, ?_⟩
  · have hShared := hp.shared.1
    change (l.sharedBase + (initSite i).baseOffset + (initSite i).displacement) % 8 = 0
    omega
  · intro k hk
    have ha := hp.shared.2.2 cta hc ((initSite i).baseOffset + (initSite i).displacement + k)
      (by omega)
    simpa only [initObject, Loc.at, Nat.add_assoc] using ha

/-- An aligned in-range shared address register resolves to the same CTA's mbarrier. -/
theorem mbarOff {l : Launch} {g : Nat} {t : TState} {r a off : Nat}
    (hr : t.regs r = some (b32 a)) (hb : a + off < 2 ^ 32) (hal : (a + off) % 8 = 0) :
    mbarLoc l g t r off = .ok ⟨.shared, g / l.block, a + off⟩ := by
  have ha : a < 2 ^ 32 := by omega
  have hb64 : a + off < 2 ^ 64 := lt_trans hb (by decide)
  have hv : (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + BitVec.ofNat 64 off)).toNat =
      a + off := by
    rw [truncBits_ofNat ha (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hb (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
  simp [mbarLoc, effAddr, sharedEffAddr, readReg, hr, b32, readBits, bind, Except.bind,
    pure, Except.pure, hv, hal]

/-- Each decoded mbarrier initializer issues an aligned, in-range initialization event. -/
theorem initOut {p : Params} {l : Launch} {m : Mem0} (hpre : Pre p l m) (i : Fin 34)
    (g : Nat) (t : TState) (hp : t.pc = (initSite i).pc) (hf : t.fault = none)
    (ha : t.regs (initSite i).baseReg = some (b32 (l.sharedBase + (initSite i).baseOffset)))
    (hn : t.regs (initSite i).countReg = some (b32 (initSite i).count)) :
    out kernel [] l g t = .ev (.mbInit
      ⟨.shared, g / l.block, l.sharedBase + (initSite i).baseOffset + (initSite i).displacement⟩
      (initSite i).count (next t)) := by
  obtain ⟨hrange, hal, hpos, hc⟩ := initRanges i
  have hr : l.sharedBase + (initSite i).baseOffset + (initSite i).displacement < 2 ^ 32 := by
    have := hpre.shared.2.1
    omega
  have h8 : (l.sharedBase + (initSite i).baseOffset + (initSite i).displacement) % 8 = 0 := by
    have := hpre.shared.1
    omega
  have hc32 : (initSite i).count < 2 ^ 32 := lt_trans hc (by decide)
  have hc64 : (initSite i).count < 2 ^ 64 := lt_trans hc (by decide)
  have hLoc := mbarOff (l := l) (g := g) ha hr h8
  have hRead : readBits l g t 32 (.reg (initSite i).countReg) = .ok
    (BitVec.ofNat 64 (initSite i).count) := by
    simp [readBits, readReg, hn, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat hc32 (by decide)]
  unfold out
  rw [hp, hf, initCode i]
  change Out.ev (tmaTmpl l g t (.mbarInit (initSite i).baseReg (initSite i).displacement
    (.reg (initSite i).countReg))) = _
  simp only [tmaTmpl, hLoc, hRead, ofExec, bind, Except.bind, pure, Except.pure, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc64, hpos, hc, and_self, ↓reduceIte]

/-- A successful initialization advances without changing any register. -/
theorem initFires {l : Launch} {g : Nat} {t u : TState} {e : Event} (i : Fin 34)
    (h : Fires (initSite i).pc (eventTmpl [] l g t (.mbarInit (initSite i).baseReg
      (initSite i).displacement (.reg (initSite i).countReg))) e (some u)) :
    u = next t :=
  PTX.Flow.fires_next (by trivial) h

end
end PTX.Kernels.TmlFa4Fwd.Prologue
