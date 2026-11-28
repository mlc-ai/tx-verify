-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid

@[expose] public section

/-! # The TMA lane's extra length and its gathers' bytes
-- domain: consistent

An event of the TMA lane is fired from a concrete thread state with the TMA state's facts
(`tma_fired`, from the thread machine's soundness). With the extra cache off
(`P.extra_topk = 0`) the lane's extra length word is zero at every state after its election
(`tma_l1`): the elected lane starts with the parameter word and the extra length load, the only
step that changes it, reads the row's length, at most `extra_topk` (`Pre.paramExtraTopkLen`).
So a gather of a block that is not a main one has the extra cache on, and every gather moves 2304
bytes (`tma_gather_bytes`, `Tma/Gather.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- **The thread state behind a TMA event.** -/
theorem tma_fired (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {d : Tma.D} {n : Cls → Nat} (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n))) :
    ∃ t ins o, (Tma.code P L g).AtD d t ∧ kernel.code[(Tma.code P L g).pc d]? = some ins ∧
      Fires ((Tma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
  exact ⟨t, ins, o, hat, hc, hf⟩

/-- **A length load's step**: its pointer is set (`SiteOk`) and the machine continues with the
row's length word. -/
theorem load_next (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : Nat} {f : Event} {d a : Tma.D} {n : Cls → Nat}
    (hs : d.site = .loadTopk ∨ d.site = .loadExtra)
    (hσ : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hf : (X.tr g)[i]? = some f) (ha : Tma.succ P L g d f = some (some a)) :
    Tma.SiteOk P L g d ∧
      (d.site = .loadTopk → a = Tma.afterTopk P d (Arith32.W (P.topkLen (ctaidY L g)))) ∧
      (d.site = .loadExtra → a = Tma.lensD d d.l0 (Arith32.W (P.extraTopkLen (ctaidY L g)))) := by
  have hget : X.get (g, i) = some f := hf
  have hub : ∀ fl, f.kind ≠ .ub fl := by
    intro fl hk
    rcases hs with hs | hs <;> simp [Tma.succ, hs, Tma.ncWord, hk] at ha
  obtain ⟨σ, hσ', hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hget hub
  rw [hσ] at hσ'
  cases hσ'
  have hr : 2162 ≤ f.pc ∧ f.pc < 2332 := by
    have h1 : f.pc = d.site.pc := hpc
    rw [h1]
    rcases hs with hs | hs <;> rw [hs] <;> decide
  obtain ⟨d', n', heq, -, hok, -, -, -⟩ := tma_state hJ hi hev hpc hr
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq
  obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq
  obtain ⟨t, ins, o, hat, hc, hf'⟩ := tma_fired hp hX hget hub hσ
  refine ⟨hok, fun h => ?_, fun h => ?_⟩
  · rw [Tma.tma_topk hp hX hget hok hat hc hf' h, Option.some.injEq, Option.some.injEq] at ha
    exact ha.symm
  · rw [Tma.tma_extra hp hX hget hok hat hc hf' h, Option.some.injEq, Option.some.injEq] at ha
    exact ha.symm

/-- **The election's winner's next state** is the elected lane's first state (or none). -/
theorem tma_lead (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩) :
    Frame.stateAt (thread P L) X g (j + 1) = none ∨ ∃ dj n,
      Frame.stateAt (thread P L) X g (j + 1) =
        some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, Tma.leadNext P L g dj⟩⟩, n)) := by
  obtain ⟨σj, hσj, hJj, hij, hevj, hpcj⟩ := ev_at hp hX hFw hj (fun _ h => by cases h)
  obtain ⟨dj, nj, rfl, -, -, hEj, hlj, -⟩ := tma_state hJj hij hevj hpcj
    ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
  obtain ⟨hsj, -, -⟩ := Tma.ev_elect hlj hEj
  rw [Frame.stateAt_succ hj, hσj]
  simp only [Option.bind_some]
  cases hn' : (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, dj⟩⟩, nj))
      ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩ with
  | none => exact .inl rfl
  | some o =>
    cases o with
    | none => simp [Code.toMachine, Tma.succ, Tma.electNext, hsj] at hn'
    | some σ1 =>
      obtain ⟨a, ha, rfl⟩ := sub_step hn' fun a ha => by
        simp only [Code.withStubsAt] at ha
        simp [Tma.succ, Tma.electNext, hsj] at ha
        subst ha
        simp [subBack, (Tma.lead_post (P := P) (L := L) (g := g) dj).1.2 _]
      simp only [Code.withStubsAt] at ha
      simp only [Tma.succ, Tma.electNext, hsj, ↓reduceIte, Option.some.injEq] at ha
      subst ha
      exact .inr ⟨dj, _, rfl⟩

/-- **The winner's region**: after the election that lane `g` won (at `j`), every state is a TMA
state after the election with `Q`, when every elected first state has `Q` and every step of the
lane keeps it. -/
theorem tma_region (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (Q : Tma.D → Prop) {j inst : Nat}
    (hj : X.get (g, j) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩)
    (hlead : ∀ d, Q (Tma.leadNext P L g d))
    (hstep : ∀ {i0 : Nat} {d a : Tma.D} {n : Cls → Nat} {f : Event},
      Frame.stateAt (thread P L) X g i0 =
        some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) →
      Tma.Post d.site → Q d → (X.tr g)[i0]? = some f → Tma.succ P L g d f = some (some a) → Q a)
    {i : Nat} (hji : j < i) {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    SubR .tma (fun d => Tma.Post d.site ∧ Q d) σ := by
  rcases tma_lead hp hX hFw hj with hn | ⟨dj, nj, hn⟩
  · rw [Frame.stateAt_none_mono hn (show j + 1 ≤ i by omega)] at hσ
    cases hσ
  obtain ⟨hP, -⟩ := Tma.lead_post (P := P) (L := L) (g := g) dj
  refine region_stays_ev _ (j := j + 1) ?_ hn ⟨_, _, rfl, hP, hlead dj⟩ i (by omega) σ hσ
  rintro i0 σ0 σ' f - hσ0 ⟨d, n, rfl, hP, hq⟩ hf hn0
  obtain ⟨a, ha, rfl⟩ := sub_step hn0 fun a ha =>
    by simp [subBack, (Tma.succ_post (P := P) (L := L) (g := g) hP ha).2 _]
  exact ⟨a, _, rfl, Tma.succ_post hP ha, hstep hσ0 hP hq hf ha⟩

/-- The TMA states after the election with an extra length word of zero. -/
def tmaL1R : (thread P L g).D → Prop := SubR .tma fun d => Tma.Post d.site ∧ d.l1 = 0

/-- The extra length load reads zero when the extra cache is off. -/
private theorem extra_zero (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (h0 : P.extra_topk = 0) {i : Nat} {f : Event} {d a : Tma.D}
    {n : Cls → Nat} (hs : d.site = .loadExtra)
    (hσ : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)))
    (hf : (X.tr g)[i]? = some f) (ha : Tma.succ P L g d f = some (some a)) : a.l1 = 0 := by
  obtain ⟨hok, -, hx⟩ := load_next hp hX hFw (.inr hs) hσ hf ha
  rw [hx hs]
  obtain ⟨x, hx⟩ := len_ptr (hok.2.1 hs)
  have hm := hp.paramExtraTopkLen
  rw [hx] at hm
  obtain ⟨-, -, hmem⟩ := hm
  have h := (hmem _ (ctaid_lt hp g).2 0 (by decide)).2 _ (ctaid_lt hp g).2
  simp only [Tma.lensD]
  rw [h0] at h
  rw [Nat.le_zero.mp h]
  rfl

/-- **With the extra cache off, the TMA lane's extra length word is zero** at its states after an
event of the TMA code after the election. -/
theorem tma_l1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (h0 : P.extra_topk = 0) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hr : 2165 < e.pc ∧ e.pc < 2332) {i : Nat} (hki : k ≤ i)
    {σ : (thread P L g).D} (hσ : Frame.stateAt (thread P L) X g i = some (some σ)) :
    tmaL1R σ := by
  obtain ⟨j, hjk, inst, hj⟩ := tma_won hp hX hFw he hub hr
  refine tma_region hp hX hFw (fun d => d.l1 = 0) hj (fun d => ?_) ?_ (by omega) hσ
  · rw [(Tma.lead_post (P := P) (L := L) (g := g) d).2, h0]
    rfl
  · intro i0 d a n f hσ0 hP hl hf ha
    by_cases hx : d.site = .loadExtra
    · exact extra_zero hp hX hFw h0 hx hσ0 hf ha
    · rw [Tma.l1_step hP.1 hx ha, hl]

/-- **The thread state behind a TMA gather**: a loop state at a gather site whose block is a main
one or has the extra cache on. -/
theorem tma_gather_at_n (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hr : 2165 < e.pc ∧ e.pc < 2332)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    ∃ d n t ins o kk, Frame.stateAt (thread P L) X g k =
      some (some (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)) ∧
      (Tma.code P L g).AtD d t ∧ d.site = .gather kk ∧
      kernel.code[(Tma.code P L g).pc d]? = some ins ∧
      Fires ((Tma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o ∧
      (Tma.isMain d = true ∨ P.extra_topk ≠ 0) ∧ Tma.LoopOk d ∧ Tma.Ev L g d e ∧
      ∀ c, c ≠ .ub → ((X.tr g).take k).countP (Tma.cls c) =
        Tma.cntAt (Tma.objs L g) 3 d.cnt.toNat d.site.stage d.site.rdN d.site.gN false c := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, -, hE, hl, -⟩ := tma_state hJ hi hev hpc ⟨by omega, hr.2⟩
  obtain ⟨kk, hs⟩ := Tma.ev_gather hl hE hk
  have hu : n (.tma .ub) = 0 := (state_count hσ (.tma .ub)).trans (lane5_take_noUb hX he)
  have hloop : d.site.inLoop = true := by rw [hs]; rfl
  obtain ⟨hL, hn⟩ := (Tma.core_loop hloop).mp (hR (state_ub hX hσ he) hu)
  have hmain : Tma.isMain d = true ∨ P.extra_topk ≠ 0 := by
    by_cases h0 : P.extra_topk = 0
    · obtain ⟨d', n', heq, -, hl1⟩ := tma_l1 hp hX hFw h0 he hub hr (Nat.le_refl k) hσ
      simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq
      exact .inl (Tma.isMain_of hL hl1)
    · exact .inr h0
  obtain ⟨t, ins, o, hat, hc, hf⟩ := tma_fired hp hX he hub hσ
  exact ⟨d, n, t, ins, o, kk, hσ, hat, hs, hc, hf, hmain, hL, hE,
    fun c hc => (state_count hσ (.tma c)).symm.trans (hn c hc)⟩

/-- **The thread state behind a TMA gather**, without its state. -/
theorem tma_gather_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hr : 2165 < e.pc ∧ e.pc < 2332)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    ∃ d t ins o kk, (Tma.code P L g).AtD d t ∧ d.site = .gather kk ∧
      kernel.code[(Tma.code P L g).pc d]? = some ins ∧
      Fires ((Tma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o ∧
      (Tma.isMain d = true ∨ P.extra_topk ≠ 0) ∧ Tma.LoopOk d ∧ Tma.Ev L g d e ∧
      ∀ c, c ≠ .ub → ((X.tr g).take k).countP (Tma.cls c) =
        Tma.cntAt (Tma.objs L g) 3 d.cnt.toNat d.site.stage d.site.rdN d.site.gN false c := by
  obtain ⟨d, -, t, ins, o, kk, -, h⟩ := tma_gather_at_n hp hX hFw he hr hk
  exact ⟨d, t, ins, o, kk, h⟩

/-- **A TMA gather moves 2304 bytes.** -/
theorem tma_gather_bytes (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hr : 2165 < e.pc ∧ e.pc < 2332)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    TensorTransfer.bytes s.descriptor = 2304 := by
  obtain ⟨d, t, ins, o, kk, hat, hs, hc, hf, hmain, -⟩ := tma_gather_at hp hX hFw he hr hk
  exact Tma.gather_bytes hp hat hs hc hf hmain hk

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
