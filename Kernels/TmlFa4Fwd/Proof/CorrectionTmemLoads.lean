-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.TmemGeometry
public import Lemmas.Flow.TcTmpl
public import Lemmas.Flow.EventCont
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

def rescaleLoadPc (stage : Fin 2) (chunk : Fin 8) : Nat :=
  8012 + 219 * stage.val + 26 * chunk.val + if chunk.val = 0 then 0 else 1

def rescaleAddressReg (stage : Fin 2) (chunk : Fin 8) : Nat :=
  if chunk.val = 0 then 1629 + 4 * stage.val else 1636 + 7 * stage.val + chunk.val

/-- The final pass loads eight columns at a time, four loads per output subbox. -/
def finalizeLoadPc (stage : Fin 2) (chunk : Fin 16) : Nat :=
  8480 + 296 * stage.val + if chunk.val < 4 then 19 * chunk.val else 7 + 17 * chunk.val

def finalizeAddressReg (stage : Fin 2) (chunk : Fin 16) : Nat :=
  if chunk.val = 0 then 1629 + 4 * stage.val
  else 6514 + 280 * stage.val +
    if chunk.val < 4 then 19 * chunk.val else 8 + 17 * chunk.val

/-- Aligned row-field and output column of one correction Tensor Memory access. -/
def outputAddress (l : Launch) (g : Nat) (stage : Fin 2) (column : Nat) : Nat :=
  2 ^ 16 * laneBase l g + (outputColumn stage + column)

private theorem outputColumnBound (stage : Fin 2) {column : Nat} (hCol : column < 128) :
    outputColumn stage + column < 512 := by
  have h := outputColumn_range stage
  omega

theorem rescaleLoadCode (stage : Fin 2) (chunk : Fin 8) :
    ∃ ds : List Nat, ds.length = 16 ∧
      kernel.code[rescaleLoadPc stage chunk]? =
        some ⟨none, .tcLd ds (rescaleAddressReg stage chunk) .s32x32b none⟩ := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨_, rfl, Flow.code_8012⟩
  · exact ⟨_, rfl, Flow.code_8039⟩
  · exact ⟨_, rfl, Flow.code_8065⟩
  · exact ⟨_, rfl, Flow.code_8091⟩
  · exact ⟨_, rfl, Flow.code_8117⟩
  · exact ⟨_, rfl, Flow.code_8143⟩
  · exact ⟨_, rfl, Flow.code_8169⟩
  · exact ⟨_, rfl, Flow.code_8195⟩
  · exact ⟨_, rfl, Flow.code_8231⟩
  · exact ⟨_, rfl, Flow.code_8258⟩
  · exact ⟨_, rfl, Flow.code_8284⟩
  · exact ⟨_, rfl, Flow.code_8310⟩
  · exact ⟨_, rfl, Flow.code_8336⟩
  · exact ⟨_, rfl, Flow.code_8362⟩
  · exact ⟨_, rfl, Flow.code_8388⟩
  · exact ⟨_, rfl, Flow.code_8414⟩

theorem finalizeLoadCode (stage : Fin 2) (chunk : Fin 16) :
    ∃ ds : List Nat, ds.length = 8 ∧
      kernel.code[finalizeLoadPc stage chunk]? =
        some ⟨none, .tcLd ds (finalizeAddressReg stage chunk) .s32x32b none⟩ := by
  fin_cases stage <;> fin_cases chunk
  · exact ⟨_, rfl, Flow.code_8480⟩
  · exact ⟨_, rfl, Flow.code_8499⟩
  · exact ⟨_, rfl, Flow.code_8518⟩
  · exact ⟨_, rfl, Flow.code_8537⟩
  · exact ⟨_, rfl, Flow.code_8555⟩
  · exact ⟨_, rfl, Flow.code_8572⟩
  · exact ⟨_, rfl, Flow.code_8589⟩
  · exact ⟨_, rfl, Flow.code_8606⟩
  · exact ⟨_, rfl, Flow.code_8623⟩
  · exact ⟨_, rfl, Flow.code_8640⟩
  · exact ⟨_, rfl, Flow.code_8657⟩
  · exact ⟨_, rfl, Flow.code_8674⟩
  · exact ⟨_, rfl, Flow.code_8691⟩
  · exact ⟨_, rfl, Flow.code_8708⟩
  · exact ⟨_, rfl, Flow.code_8725⟩
  · exact ⟨_, rfl, Flow.code_8742⟩
  · exact ⟨_, rfl, Flow.code_8776⟩
  · exact ⟨_, rfl, Flow.code_8795⟩
  · exact ⟨_, rfl, Flow.code_8814⟩
  · exact ⟨_, rfl, Flow.code_8833⟩
  · exact ⟨_, rfl, Flow.code_8851⟩
  · exact ⟨_, rfl, Flow.code_8868⟩
  · exact ⟨_, rfl, Flow.code_8885⟩
  · exact ⟨_, rfl, Flow.code_8902⟩
  · exact ⟨_, rfl, Flow.code_8919⟩
  · exact ⟨_, rfl, Flow.code_8936⟩
  · exact ⟨_, rfl, Flow.code_8953⟩
  · exact ⟨_, rfl, Flow.code_8970⟩
  · exact ⟨_, rfl, Flow.code_8987⟩
  · exact ⟨_, rfl, Flow.code_9004⟩
  · exact ⟨_, rfl, Flow.code_9021⟩
  · exact ⟨_, rfl, Flow.code_9038⟩

set_option maxRecDepth 10000 in
theorem rescaleWaitHook (stage : Fin 2) (chunk : Fin 8) :
    Assumptions.all.any (·.tcLdWait (rescaleLoadPc stage chunk)) = true := by
  rw [Assumptions.all_tcLdWait]
  fin_cases stage <;> fin_cases chunk <;> kernel_rfl

private theorem finalizeWaitHook (stage : Fin 2) (chunk : Fin 16) :
    Assumptions.all.any (·.tcLdWait (finalizeLoadPc stage chunk)) = false := by
  rw [Assumptions.all_tcLdWait]
  have hlo : 8480 ≤ finalizeLoadPc stage chunk := by unfold finalizeLoadPc; omega
  have hNot : finalizeLoadPc stage chunk ∉ Assumptions.tcLdDataflowSites := by
    simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp [hNot]

private theorem resumeLoad {t u : TState} (hPc : u.pc = t.pc + 1) (hSub : u.sub = 0) :
    { next { u with pc := t.pc, sub := 1 } with sub := 0 } = u := by
  cases u
  simp_all [next]

variable {p : Params}

private theorem outputLoadTemplate {l : Launch} {m : Mem0} {g pc r column count : Nat} {t : TState}
    {ds : List Nat} {hook : Bool} (hp : Pre p l m) (stage : Fin 2) (hColumn : column < 128)
    (hPc : t.pc = pc) (hSub : t.sub = 0) (hFault : t.fault = none)
    (hCode : kernel.code[pc]? = some ⟨none, .tcLd ds r .s32x32b none⟩) (hLen : ds.length = count)
    (hCount : TcShape.countOk .s32x32b count = true)
    (hHook : Assumptions.all.any (·.tcLdWait pc) = hook)
    (hReg : t.regs r = some (b32 (outputAddress l g stage column)))
    : out kernel Assumptions.all l g t = .ev
      (.tcLd (outputAddress l g stage column) count .s32x32b (fun vals =>
        if hook then {setRegs (next t) ds vals with pc := t.pc, sub := 1}
        else setRegs (next t) ds vals)) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCol := outputColumnBound stage hColumn
  have hCore := tc_ld_supported (L := l) (g := g) (ds := ds) (sh := .s32x32b)
    (by intro s hs; cases hs) hBlock hReg (tmem_warp_encoding_lt l g hCol)
    (hLen.symm ▸ hCount) (tcDataAddressOk_warp32 l g hCol)
  rw [out_event hFault (hPc.symm ▸ hCode) rfl rfl]
  change Out.ev (tcLdTmpl Assumptions.all l g t (.tcLd ds r .s32x32b none)) = _
  rw [tcLdTmpl, hPc, hHook]
  cases hook <;>
      simp only [hSub, hCore, hLen, Tmpl.thenWaitLd, Bool.false_eq_true, ↓reduceIte]

/-- Decode an eight-word final accumulator load independently of its trace suffix. -/
theorem finalizeLoadTemplate {l : Launch} {m : Mem0} (hp : Pre p l m) (stage : Fin 2)
    (chunk : Fin 16) {g : Nat} {t : TState}
    (ht : At t (finalizeLoadPc stage chunk)
      [(finalizeAddressReg stage chunk,b32 (outputAddress l g stage (8 * chunk.val)))]) :
    ∃ ds, ds.length = 8 ∧
      kernel.code[finalizeLoadPc stage chunk]? =
        some ⟨none,.tcLd ds (finalizeAddressReg stage chunk) .s32x32b none⟩ ∧
      out kernel Assumptions.all l g t = .ev
        (.tcLd (outputAddress l g stage (8 * chunk.val)) 8 .s32x32b
          (fun vals => setRegs (next t) ds vals)) := by
  obtain ⟨ds,hLen,hCode⟩ := finalizeLoadCode stage chunk
  have hCol : 8 * chunk.val < 128 := by have := chunk.isLt; omega
  exact ⟨ds,hLen,hCode,outputLoadTemplate hp stage hCol ht.1 ht.2.1 ht.2.2.2.1
    hCode hLen (by decide) (finalizeWaitHook stage chunk) ht.2.2.2.2.1⟩

private theorem observeLoad {l : Launch} {m : Mem0} {X : Execution} {g pos pc r column count : Nat}
    {t : TState} {ending : Option TState} {ds : List Nat} {hook : Bool} (hp : Pre p l m)
    (stage : Fin 2) (hColumn : column < 128) (hPc : t.pc = pc) (hSub : t.sub = 0)
    (hFault : t.fault = none) (hCode : kernel.code[pc]? = some ⟨none, .tcLd ds r .s32x32b none⟩)
    (hLen : ds.length = count) (hCount : TcShape.countOk .s32x32b count = true)
    (hHook : Assumptions.all.any (·.tcLdWait pc) = hook)
    (hReg : t.regs r = some (b32 (outputAddress l g stage column)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hPresent : ending = none ∨ pos + (if hook then 1 else 0) < (X.tr g).length) :
    ∃ vals, vals.length = count ∧
      X.get (g, pos) = some ⟨pc, .tc (.ld (outputAddress l g stage column)
        vals .s32x32b)⟩ ∧
      (hook = true → X.get (g, pos + 1) = some ⟨pc, .tc .waitLd⟩) ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (pos + if hook then 2 else 1)) ending := by
  let k := fun vals =>
    if hook then { setRegs (next t) ds vals with pc := t.pc, sub := 1 }
    else setRegs (next t) ds vals
  have hNext : Next kernel Assumptions.all l g t t
      (.tcLd (outputAddress l g stage column) count .s32x32b k) :=
    ⟨.refl,outputLoadTemplate hp stage hColumn hPc hSub hFault hCode hLen hCount hHook hReg⟩
  have hSeen : (X.tr g).drop pos ≠ [] := by
    intro hNil
    rcases hPresent with rfl | hIndex
    · rw [hNil] at hr
      cases hr
    · have hLen := congrArg List.length hNil
      simp only [List.length_drop, List.length_nil] at hLen
      omega
  obtain ⟨e, _, he, ⟨vals, hv, rfl, hState⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr hSeen
  obtain rfl := Option.some.inj hState
  rw [hPc] at he
  cases hook with
  | false => exact ⟨vals, hv, he, (by intro h; cases h), hTail⟩
  | true =>
    let u := setRegs (next t) ds vals
    let s := { u with pc := t.pc, sub := 1 }
    have hSkel := setRegs_skel (next t) ds vals
    have hs : s.pc = pc := hPc
    have hf : s.fault = none := hSkel.2.2.2.trans hFault
    have hPending : out kernel Assumptions.all l g s = .ev (.tc .waitLd u) := by
      rw [out_event hf (hs.symm ▸ hCode) rfl rfl]
      change Out.ev (tcLdTmpl Assumptions.all l g s (.tcLd ds r .s32x32b none)) = _
      rw [tcLdTmpl, hs, hHook]
      simp only [show s.sub ≠ 0 from Nat.one_ne_zero, ↓reduceIte]
      exact congrArg (fun state => Out.ev (.tc .waitLd state))
        (resumeLoad hSkel.1 (hSkel.2.1.trans hSub))
    have hw : Next kernel Assumptions.all l g s s (.tc .waitLd u) := ⟨.refl, hPending⟩
    have hSeenWait : (X.tr g).drop (pos + 1) ≠ [] := by
      intro hNil
      rcases hPresent with rfl | hIndex
      · rw [hNil] at hTail
        cases hTail
      · have hLen := congrArg List.length hNil
        simp only [List.length_drop, List.length_nil] at hLen
        exact (Nat.not_lt_of_ge (Nat.sub_eq_zero_iff_le.mp hLen)) hIndex
    obtain ⟨_, _, hWait, hFire, hRest⟩ := hw.continuing_at_nonempty (by
      rintro e ⟨_, hBad⟩
      cases hBad) hTail hSeenWait
    obtain ⟨rfl, hu⟩ := hFire
    obtain rfl := Option.some.inj hu
    rw [hs] at hWait
    refine ⟨vals, hv, he, fun _ => hWait, ?_⟩
    change Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) ending
    simpa only [Nat.add_assoc] using hRest

/-- A recorded rescale load and its implicit wait use two successive prefix entries. -/
theorem observeRescaleLoadInPrefix {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat}
    {t : TState} {ending : Option TState} (hp : Pre p l m) (stage : Fin 2) (chunk : Fin 8)
    (ht : At t (rescaleLoadPc stage chunk)
      [(rescaleAddressReg stage chunk, b32 (outputAddress l g stage (16 * chunk.val)))])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hPresent : ending = none ∨ pos + 1 < (X.tr g).length) :
    ∃ ds vals, ds.length = 16 ∧ vals.length = 16 ∧
      kernel.code[rescaleLoadPc stage chunk]? =
        some ⟨none, .tcLd ds (rescaleAddressReg stage chunk) .s32x32b none⟩ ∧
      X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ ∧
      X.get (g, pos + 1) = some ⟨rescaleLoadPc stage chunk, .tc .waitLd⟩ ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals)
        ((X.tr g).drop (pos + 2)) ending := by
  obtain ⟨ds, hLen, hCode⟩ := rescaleLoadCode stage chunk
  have hCol : 16 * chunk.val < 128 := by have := chunk.isLt; omega
  obtain ⟨vals, hv, he, hw, hRun⟩ := observeLoad hp stage hCol ht.1 ht.2.1 ht.2.2.2.1
    hCode hLen (by decide) (rescaleWaitHook stage chunk) ht.2.2.2.2.1 hr hPresent
  exact ⟨ds, vals, hLen, hv, hCode, he, hw rfl, hRun⟩

/-- A final output load uses the same row and its eight-column interval, with no implicit wait. -/
theorem observeFinalizeLoad {l : Launch} {m : Mem0} {X : Execution} {g pos : Nat} {t : TState}
    (hp : Pre p l m) (stage : Fin 2) (chunk : Fin 16)
    (ht : At t (finalizeLoadPc stage chunk)
      [(finalizeAddressReg stage chunk, b32 (outputAddress l g stage (8 * chunk.val)))])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ ds vals, ds.length = 8 ∧ vals.length = 8 ∧
      kernel.code[finalizeLoadPc stage chunk]? =
        some ⟨none, .tcLd ds (finalizeAddressReg stage chunk) .s32x32b none⟩ ∧
      X.get (g, pos) = some ⟨finalizeLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (8 * chunk.val)) vals .s32x32b)⟩ ∧
      Run kernel Assumptions.all l g (setRegs (next t) ds vals) ((X.tr g).drop (pos + 1)) none := by
  obtain ⟨ds, hLen, hCode⟩ := finalizeLoadCode stage chunk
  have hCol : 8 * chunk.val < 128 := by have := chunk.isLt; omega
  obtain ⟨vals, hv, he, _, hRun⟩ := observeLoad hp stage hCol ht.1 ht.2.1 ht.2.2.2.1
    hCode hLen (by decide) (finalizeWaitHook stage chunk) ht.2.2.2.2.1 hr (.inl rfl)
  exact ⟨ds, vals, hLen, hv, hCode, he, hRun⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
