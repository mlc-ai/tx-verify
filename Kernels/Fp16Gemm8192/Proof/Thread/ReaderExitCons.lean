-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ReaderExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerAcc

@[expose] public section

/-! # A consumer that read a non-claiming response never polls the response barrier again

The consumer's version of `ReaderExit`: from its status query on, a consumer that read a response
claiming no CTA is on its no-return path; its claimed first CTA `x` is `none32` from its proxy
fence on, and it re-enters its response wait only at the drain commit, which takes the exit when
`x = none32` (`Consumer.next`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Consumer

variable {L : Launch} {g : Nat} {P : Params} {mem0 : Mem0}

/-- The consumer's states after its read of a non-claiming response: from its status query on, with
`x = none32` from the fence on. -/
def NcSite (d : D) : Prop :=
  match d.site with
  | .setMaxReg | .clcWait | .clcLoad => False
  | .clcStatus | .clcFirst => True
  | _ => d.x = Loader.none32

/-- The consumer's read facts: the poll-and-read exclusion, the last event at the load, and the held
response at the queries. -/
def ReadInv (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  FailRel L g (NcSite d) (d.site = .clcLoad) es ∧
  (d.site = .clcLoad → LastPoll L g es) ∧
  ((d.site = .clcStatus ∨ d.site = .clcFirst) →
    ∃ rr, d.resp = .clc rr ∧ Scheduler.HeldRead L g es rr)

set_option maxHeartbeats 8000000 in
/-- One step of the consumer's read facts. -/
theorem read_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} {pre : List Event} (hi : Inv d)
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : ReadInv L g d pre) : ReadInv L g d' (pre ++ [e]) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hW : d.site ≠ .clcWait → okPoll (clcResp L g) e = false := fun h1 =>
    Bool.eq_false_iff.mpr fun h => by
      obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form h
      exact h1 ((clc_sites hpre hg hi hat.2.2.2.2 hc hf).1 p true acq sc hk).1
  unfold ReadInv at hq ⊢
  obtain ⟨hF, hLd, hSt⟩ := hq
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case clcWait =>
    obtain ⟨p, ok, acq, sc, -, rfl⟩ := clcWait_event hpre rfl hat.2.2.2.2 hc hf
    simp only [next] at hn
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      refine ⟨FailRel.step _ hF (by simp) (by simp [okPoll, sourceWaitSuccess]) id, by simp, by
        simp⟩
    · simp only [↓reduceIte, Option.some.injEq] at hn
      subst hn
      rw [← clcResp_loc L g]
      refine ⟨FailRel.poll hF (by simp [NcSite]) rfl, fun _ => ?_, by simp⟩
      exact ⟨Site.clcWait.pc, p, acq, sc, by simp⟩
  case clcLoad =>
    code_at hc
    subst hc
    have hr : t.regs 142 = some (b32 (L.sharedBase + 144)) :=
      (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))
    rcases fires_ldAcquire_kind hf with ⟨a, bs, hk⟩ | ⟨f, hk⟩
    · obtain ⟨ha, hs⟩ := (fires_ldAcquire128 (effAddr_b32 hr (by omega)) hat.2.1 hf) a bs hk
      obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp only [next, Option.map_eq_some_iff, Option.some.injEq] at hn
      obtain ⟨rr, hrr, rfl⟩ := hn
      obtain ⟨pc, p, acq, sc, hl⟩ := hLd rfl
      refine ⟨FailRel.read hF (fun h => by simp [NcSite] at h ⊢) (by simp [NcSite]), by simp,
        fun _ => ⟨rr, rfl, heldRead_of_read hl ha hs hrr⟩⟩
    · obtain ⟨epc, ek⟩ := e
      simp only at hk
      subst hk
      simp [next] at hn
  case clcStatus =>
    obtain ⟨rr0, hres0, hH⟩ := hSt (Or.inl rfl)
    simp only [next] at hn
    split at hn
    · rename_i q' r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hrr := (query_site hat hc hf hk).2 rr0 hres0
      subst hrr
      have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
      split_ifs with hfc
      · exact ⟨FailRel.step _ hF (by simp) hq0 (fun _ => by simp [NcSite]), by simp,
          fun _ => ⟨r, hres0, hH.snoc hq0⟩⟩
      · exact ⟨FailRel.step _ hF (by simp) hq0 (fun _ => by simp [NcSite]), by simp, by simp⟩
    · cases hn
  case clcFirst =>
    obtain ⟨rr0, hres0, hH⟩ := hSt (Or.inr rfl)
    simp only [next] at hn
    split at hn
    · rename_i q' r hk
      simp only [Option.some.injEq] at hn
      subst hn
      have hrr := (query_site hat hc hf hk).2 rr0 hres0
      subst hrr
      have hq0 : okPoll (clcResp L g) e = false := hW (by simp)
      refine ⟨FailRel.step_dep _ hF (by simp) hq0 ?_, by simp, by simp⟩
      intro j pc p acq sc pcr src bs rr hj hr' hl hs hrr' hcl _
      obtain ⟨hT, -⟩ := hF.1 j pc p acq sc pcr src bs rr hj hr' hl hs hrr' hcl
      have := heldRead_nc hH hj hr' hT hrr' hcl
      simp only [NcSite]
      exact this
    · cases hn
  all_goals clear hat hc hf
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals exact ⟨FailRel.step _ hF (by simp) (hW (by simp)) (by simp_all [NcSite]), by simp, by
    simp⟩

end Consumer

end
end PTX.Kernels.Fp16Gemm8192.Proof
