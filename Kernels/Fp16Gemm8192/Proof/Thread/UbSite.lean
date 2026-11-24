-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbMma
public import Kernels.Fp16Gemm8192.Proof.Thread.UbSched
public import Kernels.Fp16Gemm8192.Proof.Thread.UbConsSites
public import Kernels.Fp16Gemm8192.Proof.Thread.UbPro
public import Kernels.Fp16Gemm8192.Proof.Thread.UbPred
public import Kernels.Fp16Gemm8192.Proof.Thread.Tracked

@[expose] public section

/-! # Undefined behaviour fires only after the machine stopped

A thread's undefined-behaviour event fires from no state its machine follows (`ub_site_fact`):
no site's template is undefined behaviour (`Prologue.tmpl_ok`, `Loader.tmpl_ok`, ...), given what
a reached state holds. A role at a query holds the response it read (`queryInv`); at its first-CTA
query a cancelling one, since it got there from its status query by a query of that response
(`next_first`). A consumer at its deallocation holds the value its read of the base word rebuilt
to (`Consumer.next_dealloc`): unless that read's bytes rebuild to an integer, the deallocation is
the one site whose template can be undefined behaviour. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-- The state before a reached state, with the event between them. -/
theorem state_pred (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {k : Nat} {d' : ThreadD} (hk : k + 1 ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g (k + 1) = some (some d')) :
    ∃ e d, X.get (g, k) = some e ∧ Frame.stateAt (code L) X g k = some (some d) ∧
      (code L g).next d e = some (some d') := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [Frame.stateAt_succ he] at hσ
  cases hs : Frame.stateAt (code L) X g k with
  | none => rw [hs] at hσ; cases hσ
  | some σ =>
    rw [hs] at hσ
    cases σ with
    | none => exact absurd hs (tracked hpre hX g k hg)
    | some d => exact ⟨e, d, he, rfl, hσ⟩

/-- A role's query on a response register reports that response. -/
theorem role_query {d : Prologue.Role} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr d) t) (hc : kernel.code[(code L g).pc (.inr d)]? = some ins)
    (hf : Fires ((code L g).pc (.inr d)) (eventTmpl Prod L g t ins.op) e o) {q : ClcQuery}
    {rr : ClcResponse} (hk : e.kind = .clcQuery q rr) : ∀ r0, d.resp = .clc r0 → rr = r0 := by
  rcases d with l | m | sd | cs
  · exact (Loader.query_site hat hc hf hk).2
  · exact (Mma.query_site hat hc hf hk).2
  · exact (Scheduler.query_site hat hc hf hk).2
  · exact (Consumer.query_site hat hc hf hk).2

/-- A role's step into its first-CTA query is from its status query, by a query of a cancelling
response, keeping the response it holds. -/
theorem role_next_first {d : ThreadD} {r : Prologue.Role} {e : Event}
    (hn : (code L g).next d e = some (some (.inr r))) (h3 : r.clcStage = 3) :
    ∃ r0, d = .inr r0 ∧ r0.clcStage = 2 ∧ r.resp = r0.resp ∧
      ∃ q rr, e.kind = .clcQuery q rr ∧ rr.firstCta.isSome = true := by
  rcases d with p | (l | m | sd | cs)
  · change Prologue.next L g p e = some (some (.inr r)) at hn
    rw [Prologue.clc_stage_start hn] at h3
    cases h3
  · obtain ⟨l', hl, he⟩ := next_of_loader hn
    cases he
    have hs : l'.site = .clcFirst := by
      simp only [Prologue.Role.clcStage, Loader.D.clcStage] at h3; split at h3 <;> simp_all
    obtain ⟨h1, h2, h3'⟩ := Loader.next_first hl hs
    exact ⟨_, rfl, by simp [Prologue.Role.clcStage, Loader.D.clcStage, h1], h2, h3'⟩
  · obtain ⟨m', hm, he⟩ := next_of_mma hn
    cases he
    have hs : m'.site = .clcFirst := by
      simp only [Prologue.Role.clcStage, Mma.D.clcStage] at h3; split at h3 <;> simp_all
    obtain ⟨h1, h2, h3'⟩ := Mma.next_first hm hs
    exact ⟨_, rfl, by simp [Prologue.Role.clcStage, Mma.D.clcStage, h1], h2, h3'⟩
  · obtain ⟨s', hs', he⟩ := next_of_sched hn
    cases he
    have hs : s'.site = .clcFirst := by
      simp only [Prologue.Role.clcStage, Scheduler.D.clcStage] at h3; split at h3 <;> simp_all
    obtain ⟨h1, h2, h3'⟩ := Scheduler.next_first hs' hs
    exact ⟨_, rfl, by simp [Prologue.Role.clcStage, Scheduler.D.clcStage, h1], h2, h3'⟩
  · obtain ⟨c', hc', he⟩ := next_of_cons hn
    cases he
    have hs : c'.site = .clcFirst := by
      simp only [Prologue.Role.clcStage, Consumer.D.clcStage] at h3; split at h3 <;> simp_all
    obtain ⟨h1, h2, h3'⟩ := Consumer.next_first hc' hs
    exact ⟨_, rfl, by simp [Prologue.Role.clcStage, Consumer.D.clcStage, h1], h2, h3'⟩

/-- **A reached role state holds a response at its status query and a cancelling response at its
first-CTA query.** -/
theorem role_held (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g < L.threads)
    {k : Nat} {r : Prologue.Role} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr r))) :
    (r.clcStage = 2 → ∃ rr, r.resp = .clc rr) ∧
      (r.clcStage = 3 → ∃ rr, r.resp = .clc rr ∧ rr.firstCta.isSome = true) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hrel : QueryRel L g r.clcStage r.resp ((X.tr g).take k) := queryInv hpre hg htr k _ hσ
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, rr, -, -, -, -, -, -, hv⟩ := hrel.2 (by omega)
    exact ⟨rr, hv⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => simp [stateAt_zero] at hσ
      | succ k' => exact ⟨k', rfl⟩
    obtain ⟨e, d, he, hd, hn⟩ := state_pred hpre hX hg hk hσ
    obtain ⟨r0, rfl, h2, hresp, q, rr, hq, hsome⟩ := role_next_first hn h3
    have hrel0 : QueryRel L g r0.clcStage r0.resp ((X.tr g).take k') :=
      queryInv hpre hg htr k' _ hd
    obtain ⟨-, -, -, -, -, -, -, -, rr0, -, -, -, -, -, -, hv⟩ := hrel0.2 (by omega)
    obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hd
    have hrr := role_query hat hc hfire hq rr0 hv
    subst hrr
    exact ⟨rr, hresp.trans hv, hsome⟩

/-- A consumer at its deallocation got there from its load of the base word, holding what the
bytes it read rebuild to. -/
theorem dealloc_pred (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (hg : g <
    L.threads)
    {k : Nat} {c : Consumer.D} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.cons c)))) (hs : c.site = .dealloc) :
    0 < k ∧ ∃ pcr a bs, X.get (g, k - 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 ∧ rebuild 3 bs = .ok c.base := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => simp [stateAt_zero] at hσ
    | succ k' => exact ⟨k', rfl⟩
  obtain ⟨e, d, he, hd, hn⟩ := state_pred hpre hX hg hk hσ
  refine ⟨by omega, ?_⟩
  simp only [Nat.add_sub_cancel]
  rcases d with p | (l | m | sd | c0)
  · change Prologue.next L g p e = some (some (.inr (.cons c))) at hn
    rw [Prologue.next_cons hn] at hs
    cases hs
  · obtain ⟨_, -, he'⟩ := next_of_loader hn; cases he'
  · obtain ⟨_, -, he'⟩ := next_of_mma hn; cases he'
  · obtain ⟨_, -, he'⟩ := next_of_sched hn; cases he'
  · obtain ⟨c', hc', he'⟩ := next_of_cons hn
    cases he'
    obtain ⟨h0, a, bs, hk', hrb⟩ := Consumer.next_dealloc hc' hs
    have htr := Frame.trace (fun _ => sound hpre) hX hg
    obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hd
    obtain ⟨epc, ek⟩ := e
    simp only at hk'
    subst hk'
    obtain ⟨hloc, hsz⟩ := Consumer.ldBase_read hpre h0 hat hc hfire a bs rfl
    exact ⟨epc, a, bs, he, hloc, hsz, hrb⟩

/-- **Undefined behaviour fires after the machine stopped**, or at a deallocation right after a
read of the base word whose bytes do not rebuild to an integer. -/
theorem ub_site_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (hg : g < L.threads) {k pc : Nat} {f : Fault} (he : X.get (g, k) = some ⟨pc, .ub f⟩) :
    Frame.stateAt (code L) X g k = none ∨
      (0 < k ∧ ∃ pcr a bs, X.get (g, k - 1) = some ⟨pcr, .rd a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧ a.size = 4 ∧
        ∀ w x, rebuild 3 bs ≠ .ok (.bits w x)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases htr.fired he with ⟨τ, o, ha, hf⟩ | ⟨ha, -⟩
  · cases τ with
    | none => exact absurd ha (tracked hpre hX g k hg)
    | some d =>
      have hσ : Frame.stateAt (code L) X g k = some (some d) := ha
      obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site (sound hpre hg) hf
      have hT := fires_ub hfire rfl
      rcases d with p | (l | m | sd | cs)
      · exact absurd hT (Prologue.tmpl_ok hpre hat hc f)
      · have hh := role_held hpre hX hg hklt.le hσ
        exact absurd hT (Loader.tmpl_ok hpre hg hinv.1 hat hc
          ⟨fun hs => hh.1 (by simp [Prologue.Role.clcStage, Loader.D.clcStage, hs]),
            fun hs => hh.2 (by simp [Prologue.Role.clcStage, Loader.D.clcStage, hs])⟩ f)
      · have hh := role_held hpre hX hg hklt.le hσ
        exact absurd hT (Mma.tmpl_ok hpre hg hinv.1 hat hc
          ⟨fun hs => hh.1 (by simp [Prologue.Role.clcStage, Mma.D.clcStage, hs]),
            fun hs => hh.2 (by simp [Prologue.Role.clcStage, Mma.D.clcStage, hs])⟩ f)
      · have hh := role_held hpre hX hg hklt.le hσ
        exact absurd hT (Scheduler.tmpl_ok hpre hg hinv.1 hat hc
          ⟨fun hs => hh.1 (by simp [Prologue.Role.clcStage, Scheduler.D.clcStage, hs]),
            fun hs => hh.2 (by simp [Prologue.Role.clcStage, Scheduler.D.clcStage, hs])⟩ f)
      · by_cases hbad : cs.site = .dealloc ∧ ∀ w x, cs.base ≠ .bits w x
        · obtain ⟨hk0, pcr, a, bs, hrd, hloc, hsz, hrb⟩ :=
            dealloc_pred hpre hX hg hklt.le hσ hbad.1
          exact .inr ⟨hk0, pcr, a, bs, hrd, hloc, hsz, fun w x h => hbad.2 w x (by
            rw [hrb] at h; exact Except.ok.inj h)⟩
        · have hh := role_held hpre hX hg hklt.le hσ
          refine absurd hT (Consumer.tmpl_ok hpre hg hinv.1 hinv.2.1 hat hc
            ⟨fun hs => hh.1 (by simp [Prologue.Role.clcStage, Consumer.D.clcStage, hs]),
              fun hs => hh.2 (by simp [Prologue.Role.clcStage, Consumer.D.clcStage, hs]),
              fun hs => ?_⟩ f)
          by_contra hn
          exact hbad ⟨hs, fun w x h => hn ⟨w, x, h⟩⟩
  · exact .inl ha

end

end PTX.Kernels.Fp16Gemm8192.Proof
