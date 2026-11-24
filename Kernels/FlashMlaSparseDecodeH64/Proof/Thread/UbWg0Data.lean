-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Exchange
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput

public section

/-! # Live softmax data accesses and the rescale vote -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0

open PTX PTX.Proof PTX.Flow Wg0

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- Softmax data events before the final output path. -/
@[expose] def DataSite : Wg0.Site → Prop
  | .scoreLoad _ _ | .maskRead | .exchStore _ | .peerRead _ | .rowMax | .maxRead
  | .rescaleVote | .pStore _ | .rescaleLoad _ | .rescaleStore _ | .lseStore0
  | .lseRead | .lseStore => True
  | _ => False

set_option maxRecDepth 100000

private theorem writeStep_live {d : D} {s : Wg0.Site} {e : Event} {a : Acc} {bs : List Byte}
    (hk : e.kind = .wr a bs) : writeStep L g d s e ≠ none := by
  simp only [writeStep, hk]
  split
  · split <;> simp
  · simp

private def scoreAddrReg (a k : Fin 2) : Nat :=
  ([[986, 987], [984, 985]].getD a.val []).getD k.val 0

private def scoreAddr (k : Fin 2) : Nat := if k.val = 0 then 400 else 432

private theorem score_template (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr}
    {a k : Fin 2} (hd : d.site = .scoreLoad a k) (ha : (Wg0.code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) :
    eventTmpl Assumptions.all L g t ins.op =
      .tcLd (scoreAddr k) 32 .s32x32b
        (fun words => setRegs (PTX.next t) (scoreDsts (a.val == k.val)) words) := by
  let own := a.val == k.val
  have hcode : kernel.code[(Wg0.Site.scoreLoad a k).pc]? =
      some ⟨none, .tcLd (scoreDsts own) (scoreAddrReg a k) .s32x32b none⟩ := by
    fin_cases a <;> fin_cases k
    · exact Flow.code_278
    · exact Flow.code_280
    · exact Flow.code_283
    · exact Flow.code_285
  have hr : t.regs (scoreAddrReg a k) = some (b32 (scoreAddr k)) := by
    have h := reg_value ha (r := scoreAddrReg a k) (by
      rw [hd]
      fin_cases a <;> fin_cases k <;> decide +kernel)
    rw [h]
    fin_cases a <;> fin_cases k <;> rfl
  rw [hd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have haddr : scoreAddr k = 400 ∨ scoreAddr k = 432 := by fin_cases k <;> decide
  have hlen : (scoreDsts own).length = 32 := by simp [scoreDsts]
  simpa only [hlen] using (scoreLoad_template (g := g) hpre haddr hlen hr)

private theorem data_fires (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hData : DataSite d.site)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∀ f, e.kind ≠ .ub f) ∧ Wg0.next P L g d e ≠ none := by
  cases h : d.site <;> simp only [h, DataSite] at hData
  case scoreLoad a k =>
    rw [score_template hpre h ha hc] at hf
    obtain ⟨words, _, he, _⟩ := hf
    have hk : e.kind = .tc (.ld (scoreAddr k) words .s32x32b) := congrArg Event.kind he
    refine ⟨by simp [hk], ?_⟩
    simp only [Wg0.next, nextSite, h, hk]
    split <;> simp
  case maskRead =>
    obtain ⟨_, _, hk, _, _, _⟩ := fired_maskRead hpre h ha hi hc hf
    refine ⟨by simp [hk], ?_⟩
    simp only [Wg0.next, nextSite, h, hk]
    repeat' first | exact Option.some_ne_none _ | split
  case exchStore j =>
    obtain ⟨_, hk, _, _, _⟩ := fired_exchangeStore hpre j h ha hi hc hf
    refine ⟨by simp [hk], ?_⟩
    simpa only [Wg0.next, nextSite, h] using
      (writeStep_live (L := L) (g := g) (d := d) (s := if hw : j.val + 1 < 8 then
        .exchStore ⟨j.val + 1, hw⟩ else .pairBar) hk)
  case peerRead j =>
    obtain ⟨_, _, hk, _, _, _⟩ := fired_peerRead_at hpre h hi ha hc hf
    refine ⟨by simp [hk], ?_⟩
    simp only [Wg0.next, nextSite, h, hk]
    repeat' first | exact Option.some_ne_none _ | split
  case rowMax =>
    obtain ⟨_, hk, _, _, _⟩ := fired_rowMax hpre h ha hi hc hf
    exact ⟨by simp [hk], by
      simpa only [Wg0.next, nextSite, h] using
        (writeStep_live (L := L) (g := g) (d := d) (s := .wg0Sync2) hk)⟩
  case maxRead =>
    obtain ⟨_, _, hk, _, _, _, _⟩ := fired_maxRead hpre h ha hi hc hf
    exact ⟨by simp [hk], by
      simp only [Wg0.next, nextSite, h, hk]
      split <;> simp⟩
  case rescaleVote =>
    rw [rescaleVote_template hpre h ha hc] at hf
    obtain ⟨r, he, _⟩ := hf
    have hk : e.kind = .voteMode .any (2 ^ 32 - 1) d.voteTest r := congrArg Event.kind he
    exact ⟨by simp [hk], by simp [Wg0.next, nextSite, h, hk]⟩
  case pStore j =>
    obtain ⟨_, _, _, _, _, hk, _, _, _⟩ := fired_pStore hpre h ha hi hc hf
    refine ⟨by simp [hk], ?_⟩
    simp only [Wg0.next, nextSite, h]
    split <;> exact writeStep_live hk
  case rescaleLoad j =>
    rw [rescaleLoad_template hpre h ha hc] at hf
    obtain ⟨words, _, he, _⟩ := hf
    have hk : e.kind = .tc (.ld (64 * j.val) words .s32x32b) := congrArg Event.kind he
    exact ⟨by simp [hk], by simp [Wg0.next, nextSite, h, hk]⟩
  case rescaleStore j =>
    rw [rescaleStore_template hpre h ha hc] at hf
    have hk : e.kind = .tc (.st (64 * j.val) (rescaleStoreValues d) .s32x32b) :=
      congrArg Event.kind hf.1
    exact ⟨by simp [hk], by simp [Wg0.next, nextSite, h, hk]⟩
  case lseStore0 =>
    obtain ⟨_, hk, _, _, _⟩ := fired_lseStore0 hpre h ha hi hc hf
    exact ⟨by simp [hk], by
      simpa only [Wg0.next, nextSite, h] using
        (writeStep_live (L := L) (g := g) (d := d) (s := .lseBar2) hk)⟩
  case lseRead =>
    obtain ⟨_, _, hk, _, _, _, _⟩ := fired_lseRead hpre h ha hi hc hf
    refine ⟨by simp [hk], ?_⟩
    simp only [Wg0.next, nextSite, h, hk]
    repeat' first | exact Option.some_ne_none _ | split
  case lseStore =>
    have hb := Wg1Mma.eOf_lt_b (g := g) hpre
    have hq := Wg1Mma.queryOf_lt hpre hg
    obtain ⟨_, hk, hl, hs, _⟩ := fired_lseStore hpre hb hq h ha hi hc hf
    exact ⟨by simp [hk], by simp [Wg0.next, nextSite, h, hk, hl, hs]⟩

/-- The softmax score, exchange, probability, rescale and LSE data templates are defined. -/
theorem data_tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads)
    {d : D} {t : TState} {ins : Instr} (ha : (Wg0.code P L g).AtD d t) (hi : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins) (hData : DataSite d.site) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  intro hu
  have hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op)
      ⟨d.site.pc, .ub f⟩ none := by
    rw [hu]
    exact ⟨rfl, rfl⟩
  exact (data_fires hpre hg ha hi hc hData hf).1 f rfl

/-- The softmax data events keep a represented successor. -/
theorem data_next_live (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {i : Nat} {e : Event} {d : D} (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hData : DataSite d.site) : Machine.next P L g (.wg0 d) e ≠ none := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, ha, hi, hc, hf⟩ := Frame.fired_site hs hX he hd
  have hn := (data_fires hpre hg ha hi hc hData hf).2
  cases h : Wg0.next P L g d e with
  | none => exact (hn h).elim
  | some u =>
    cases u with
    | some u => simp [Machine.next, h]
    | none =>
      simp only [Machine.next, h]
      split <;> simp

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.UbWg0
