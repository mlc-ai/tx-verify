-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.QxValues
public import Kernels.InklingRelDecode.Proof.Result.RsOSource
public import Kernels.InklingRelDecode.Proof.Result.RsEpiLoad
public import Kernels.InklingRelDecode.Proof.Interface.QxLayer

@[expose] public section

/-!
# The epilogue's load check (`ProtocolRest.epiLoad`)

`epiLoad_of`: on every consistent execution, at a `waitLd` state of the epilogue (every row) the
64 loaded words pack and their products by the reciprocal have outcomes
(`Interface.Lk.EpiLoadOk`). The state's load event (`Rs.ld_event'`) has the last PV MMA as the
read source of each register (`Rs.oSourceAll_of`); the source is completed (its completion is
observed before the load: `DoneBefore.done`), so its result at the cell is an `f32` number
(`ResultF32`, from `Qx.result_of`), and the register holds it (`TcMma.LoadReadOk`, a word of four
bytes). The reciprocal is an `f32` number at every epilogue state (`inv_fl_state`: the row sum the
softmax region leaves reads as an `f32` number, `Lk.nnInv_state`). `Epi.loadOk_of_fl` concludes.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Qx
open PTX PTX.Flow PTX.Proof PTX.TcMma PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Interface (St TSt ThreadFacts)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every result cell of a completed MMA has an `f32` value (the statement of `result_of`). -/
def ResultF32 (L : Launch) (X : Execution) : Prop :=
  ∀ (k : Nat) {g pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat},
    g < L.threads → X.get (g, k) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
    X.async.mmaDone (g, k) = true → ∀ {r c : Nat} {cell : Cell},
    writeCell sp dst mask r c = some cell →
    ∃ x, Result L Assumptions.all X (g, k) cell (.float .f32 x)

/-- **The reciprocal is an `f32` number at every epilogue state** of a launched thread. -/
theorem inv_fl_state (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hre : Interface.Lk.SmReal Q L X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {d : Epi.D}
    (hσ : St Q L X g k = some (some (.d (.epi d)))) : ∃ y, d.pr.inv = fl y := by
  obtain ⟨k', hk', hσ'⟩ : ∃ k', k' ≤ (X.tr g).length ∧
      St Q L X g k' = some (some (.d (.epi d))) := by
    by_cases h : k ≤ (X.tr g).length
    · exact ⟨k, h, hσ⟩
    · exact ⟨_, le_rfl, (Frame.stateAt_of_le (C := Interface.code L Q) (X := X) (g := g)
        (k := k) (by omega)).symm.trans hσ⟩
  obtain ⟨k0, dsm, -, h0, hpr⟩ := Interface.epi_pr hk' hσ'
  obtain ⟨x, -, hx⟩ :=
    (Interface.Lk.nnInv_state hpre hX hf hre hg h0).l
  rw [hpr]
  exact Epi.prm_inv_fl _ hx

/-- **A load whose read source is an MMA reads an `f32` result**: the source writes the cell as
an MMA, it is completed (its completion is observed before the load, `DoneBefore.done`), so its
result at the cell is an `f32` number. -/
theorem ldSource_result (hX : Consistent L kernel Assumptions.all mem0 X) (hres : ResultF32 L X)
    {mg mk pcm dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {e : EvId}
    {pc a : Nat} {vals : List Value} {sh : TcShape} {cell : Cell} (hml : mg < L.threads)
    (hem : X.get (mg, mk) = some ⟨pcm, .tc (.mma dst sp acc mask)⟩)
    (hget : X.get e = some ⟨pc, .tc (.ld a vals sh)⟩) (hrs : ReadSource L X .ld (mg, mk) e cell) :
    ∃ x, Result L Assumptions.all X (mg, mk) cell (.float .f32 x) := by
  obtain ⟨-, hw, hwb, -, -⟩ := hrs
  have hmc : X.MmaCell (mg, mk) cell := by
    rcases hw with h | ⟨a', v', sh', j', ⟨pc', h'⟩, -⟩ | ⟨c', -, -, -, ⟨pc', h'⟩, -⟩ |
        ⟨s', ⟨pc', h'⟩, -⟩
    · exact h
    all_goals (rw [hem] at h'; simp at h')
  have hd : X.async.mmaDone (mg, mk) = true := by
    rcases hwb with (h | h) | h | h
    · exact h.done hX.tcCommit
    · obtain ⟨-, -, h3⟩ := h
      obtain ⟨_, _, _, _, _, _, _, _, -, ⟨pc', h'⟩, -⟩ := h3
      simp [hget] at h'
    · obtain ⟨⟨a', v', sh', pc', h'⟩, -⟩ := h
      rw [hem] at h'; simp at h'
    · obtain ⟨-, -, h3⟩ := h
      obtain ⟨c', _, _, _, _, ⟨pc', h'⟩, -⟩ := h3
      rw [hem] at h'; simp at h'
  obtain ⟨d', s', acc', mask', row, col, ⟨pc', he''⟩, hwc⟩ := hmc
  exact hres mk hml he'' hd hwc

/-- **A load whose read source is an MMA with `f32` results reads an `f32` result** (the source's
results only). -/
theorem ldSource_result_at (hX : Consistent L kernel Assumptions.all mem0 X)
    {mg mk pcm dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat} {e : EvId}
    {pc a : Nat} {vals : List Value} {sh : TcShape} {cell : Cell}
    (hres : ∀ {pc dst : Nat} {sp : OperandSpec} {acc : Bool} {mask : List Nat},
      X.get (mg, mk) = some ⟨pc, .tc (.mma dst sp acc mask)⟩ →
      X.async.mmaDone (mg, mk) = true → ∀ {r c : Nat} {cell : Cell},
      writeCell sp dst mask r c = some cell →
      ∃ x, Result L Assumptions.all X (mg, mk) cell (.float .f32 x))
    (hem : X.get (mg, mk) = some ⟨pcm, .tc (.mma dst sp acc mask)⟩)
    (hget : X.get e = some ⟨pc, .tc (.ld a vals sh)⟩) (hrs : ReadSource L X .ld (mg, mk) e cell) :
    ∃ x, Result L Assumptions.all X (mg, mk) cell (.float .f32 x) := by
  obtain ⟨-, hw, hwb, -, -⟩ := hrs
  have hmc : X.MmaCell (mg, mk) cell := by
    rcases hw with h | ⟨a', v', sh', j', ⟨pc', h'⟩, -⟩ | ⟨c', -, -, -, ⟨pc', h'⟩, -⟩ |
        ⟨s', ⟨pc', h'⟩, -⟩
    · exact h
    all_goals (rw [hem] at h'; simp at h')
  have hd : X.async.mmaDone (mg, mk) = true := by
    rcases hwb with (h | h) | h | h
    · exact h.done hX.tcCommit
    · obtain ⟨-, -, h3⟩ := h
      obtain ⟨_, _, _, _, _, _, _, _, -, ⟨pc', h'⟩, -⟩ := h3
      simp [hget] at h'
    · obtain ⟨⟨a', v', sh', pc', h'⟩, -⟩ := h
      rw [hem] at h'; simp at h'
    · obtain ⟨-, -, h3⟩ := h
      obtain ⟨c', _, _, _, _, ⟨pc', h'⟩, -⟩ := h3
      rw [hem] at h'; simp at h'
  obtain ⟨d', s', acc', mask', row, col, ⟨pc', he''⟩, hwc⟩ := hmc
  exact hres he'' hd hwc

/-- **`ProtocolRest.epiLoad`** from the source of the epilogue's load and the `f32` values of the
completed MMAs. -/
theorem epiLoad_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hre : Interface.Lk.SmReal Q L X) (hso : Rs.OSourceAll Q L X)
    (hres : ResultF32 L X) : Interface.Lk.EpiLoadOk Q L X := by
  intro g k d e hg he _ hσ hs
  have he' : X.get (g, k) = some e := he
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he' hσ
  have hI : Epi.Inv d := hinv.2.1
  have hsk : d.sk = false := hI.pre (.inr (.inr hs))
  have hlen : d.o.length = 64 := hI.len (by rw [hs]; trivial) hsk
  obtain ⟨k0, pc, d0, hσ0, hs0, hpr, hget⟩ :=
    Result.Out.ld_event' hX hf hg k d hσ hsk (by rw [hs]; decide)
  obtain ⟨⟨mg, mk⟩, pcm, dst, sp, acc, mask, dm, P, hml, -, hem, -, -, -, -, hsrc⟩ :=
    hso hg hσ hsk hσ0 hs0 hpr hget
  obtain ⟨y, hy⟩ := inv_fl_state hpre hX hf hre hg hσ
  refine Epi.loadOk_of_fl d (fun j hj => ?_) hy
  set cell := tcDataCell L g (.s16x32bx2 64) d.pr.taddr j with hcell
  obtain ⟨x, hx⟩ := ldSource_result hX hres hml hem hget (hsrc j hj)
  have hLC : LoadCell L X (g, k0) j cell :=
    ⟨d.pr.taddr, d.o, .s16x32bx2 64, ⟨pc, hget⟩, by omega, rfl⟩
  obtain ⟨word, hword, hwc2⟩ :=
    hX.tcRead.1 (g, k0) _ _ _ j (mg, mk) cell _ ⟨pc, hget⟩ hLC (hsrc j hj) (.inl hx)
  rcases hwc2 with ⟨-, rfl⟩ | ⟨hb2, -⟩
  · refine ⟨x, ?_⟩
    rw [List.getD_eq_getElem?_getD, hword]
    rfl
  · simp [Value.bytes, FloatFmt.bytes] at hb2

end
end PTX.Kernels.InklingRelDecode.Proof.Qx
