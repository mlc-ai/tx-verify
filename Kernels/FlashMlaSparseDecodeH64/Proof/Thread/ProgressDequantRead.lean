-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Lemmas.Flow.LoadShared

public section

/-! # Scale and raw read extensions for the dequantizer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
open PTX PTX.Flow PTX.Proof

/-- The two kinds of shared loads that prepare a dequantized chunk. -/
inductive DequantRead where
  | scale (row element : Fin 4)
  | raw (row : Fin 4) (word : Fin 8)

@[expose] def DequantRead.site : DequantRead → Wg2.Site
  | .scale r j => .scale r j
  | .raw r s => .raw r s

private theorem scale_read_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg2.D} {r j : Fin 4} (hpre : Pre P L mem0)
    (hd : d.site = .scale r j) (ha : Wg2.AtD P L g d t) (hi : Wg2.Inv P L g d) :
    ∃ a k, eventTmpl Assumptions.all L g t (.mem (Wg2.scaleLoad r)) = .read a k := by
  let base := L.sharedBase + Wg2.rawBase d.buf + Wg2.rawRowOff L g 0
  let off := 512 + 9216 * r.val
  have hbase : t.regs 2796 = some (b32 base) := by
    have hl : 2796 ∈ (Flow.live d.site.pc).filter (fun reg => Wg2.tracked.contains reg) := by
      rw [hd]
      fin_cases r <;> fin_cases j <;> decide +kernel
    have h := ha.reg hl
    simp only [Wg2.valueOf, Wg2.table, PTX.Flow.lookupLit, Option.getD_some] at h
    simpa [base, sb, Nat.add_assoc] using h
  have hsum : base + off = L.sharedBase + Wg2.rawBase d.buf + Wg2.scaleRowOff L g r.val := by
    simp only [base, off, Wg2.scaleRowOff, Wg2.rawRowOff, Wg2.rawRow, Wg2.rawRowStride,
      Wg2.numGroups, Wg2.quantBytes]
    omega
  have hal : (base + off) % 16 = 0 := by
    have hs : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
    simp only [base, off, Wg2.rawBase, Wg2.rawBufBytes, Wg2.rawRowOff, Wg2.rawRowStride]
    omega
  have hlt : base + off < 2 ^ 32 := by
    rw [hsum]
    have hs := sharedBase_lt hpre
    have hfit := hi.scaleFit r.val r.isLt
    have hslot := hi.bufLt
    simp only [Wg2.rawBase, Wg2.rawBufBytes, Wg2.scaleLoadBytes] at hfit ⊢
    omega
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 2796) (w := 32)
    (by fin_cases r <;> rfl) rfl rfl rfl rfl]
  dsimp only [off] at hlt
  simp only [Wg2.scaleLoad, DType.width, loadTmpl, effAddr_b32_off hbase hlt,
    bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  change ∃ a k, (match elemAcc _ 4 4 t.sub with
    | .error f => Tmpl.ub f
    | .ok b => Tmpl.read b (afterLoad t (Wg2.scaleLoad r).regs)) = Tmpl.read a k
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  exact ⟨_, _, rfl⟩

private theorem raw_read_template {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {t : TState} {d : Wg2.D} {r : Fin 4} {s : Fin 8} (hpre : Pre P L mem0)
    (hd : d.site = .raw r s) (ha : Wg2.AtD P L g d t) (hi : Wg2.Inv P L g d) :
    ∃ a k, eventTmpl Assumptions.all L g t (.mem (Wg2.rawLoad r s)) = .read a k := by
  let base := L.sharedBase + Wg2.rawBase d.buf + Wg2.rawWordOff L g 0 0
  let off := 9216 * r.val + 64 * s.val
  have hbase : t.regs 2817 = some (b32 base) := by
    have hl : 2817 ∈ (Flow.live d.site.pc).filter (fun reg => Wg2.tracked.contains reg) := by
      rw [hd]
      exact Wg2.rawBase_live r s
    have h := ha.reg hl
    simp only [Wg2.valueOf, Wg2.table, PTX.Flow.lookupLit, Option.getD_some] at h
    simpa [base, sb, Nat.add_assoc] using h
  have hsum : base + off = L.sharedBase + Wg2.rawBase d.buf + Wg2.rawWordOff L g r.val s.val := by
    simp only [base, off, Wg2.rawWordOff, Wg2.rawRowOff, Wg2.rawRow, Wg2.rawRowStride,
      Wg2.numGroups, Wg2.rawBytesPerStep]
    omega
  have hal : (base + off) % 8 = 0 := by
    have hs : L.sharedBase % 1024 = 0 := hpre.sharedBase ▸ hpre.sharedAlignment
    simp only [base, off, Wg2.rawBase, Wg2.rawBufBytes, Wg2.rawWordOff, Wg2.rawRowOff,
      Wg2.rawRowStride, Wg2.rawBytesPerThread, Wg2.rawBytesPerStep]
    omega
  have hlt : base + off < 2 ^ 32 := by
    rw [hsum]
    have hs := sharedBase_lt hpre
    have hfit := Wg2.rawWord_fit (L := L) (g := g) r.isLt s.isLt
    have hslot := hi.bufLt
    simp only [Wg2.rawBase, Wg2.rawBufBytes, Wg2.rawBytesPerThread] at hfit ⊢
    omega
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 2817) (w := 32)
    rfl rfl rfl rfl rfl]
  dsimp only [off] at hlt
  simp only [Wg2.rawLoad, DType.width, loadTmpl, effAddr_b32_off hbase hlt,
    bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
  change ∃ a k, (match elemAcc _ 8 1 t.sub with
    | .error f => Tmpl.ub f
    | .ok b => Tmpl.read b (afterLoad t (Wg2.rawLoad r s).regs)) = Tmpl.read a k
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  exact ⟨_, _, rfl⟩

/-- A released dequantizer at a scale or raw load takes a counted step in a safe tracked prefix. -/
theorem dequant_read_extension {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g : Nat} {d : Wg2.D} {which : DequantRead} (hpre : Pre P L mem0)
    (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hsafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hσ : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg2 d)))
    (hd : d.site = which.site) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne : X.tr g ≠ [] := by
    intro he
    rw [he, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  obtain ⟨t, hr⟩ := Frame.run_some hX (fun hub => hsafe (.inl hub)) hp
  obtain ⟨u, ins, hτ, ha, hi, hc, hout⟩ := Frame.end_at hs hp.1 hr hσ
  change kernel.code[d.site.pc]? = some ins at hc
  rw [hd] at hc
  have hread : ∃ a k, eventTmpl Assumptions.all L g u ins.op = .read a k := by
    cases which with
    | scale r j =>
      obtain rfl := Option.some.inj (hc.symm.trans (Wg2.scaleLoad_code r j))
      exact scale_read_template hpre hd ha hi
    | raw r s =>
      obtain rfl := Option.some.inj (hc.symm.trans (Wg2.rawLoad_code r s))
      exact raw_read_template hpre hd ha hi
  obtain ⟨a, k, htmpl⟩ := hread
  rw [htmpl] at hout
  exact shared_read_extension hX hp.1 hne hrel hr hτ hout (sync_guarded hX hsafe)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
