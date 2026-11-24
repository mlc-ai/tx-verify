-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Protocol.Pos
public import Lemmas.Step.CtaBarNamed
public import Kernels.RmsNorm.Proof.NoBarArrive

@[expose] public section

/-! # The CTA barriers

Every arrival on barrier `0` or `1` is a thread's arrival for the whole CTA (`count = none`, the
CTA's 8 warps), so the records of a CTA's history follow the named-barrier protocol
(`protocol`). An arrival that a thread passed released its generation, the arrival's ordinal
(`released`). Every thread of the CTA then has its arrival of that ordinal (`arrival_exists`):
a thread that never exits by the release's records, a thread that exited because it arrives at
every barrier of its rows, which are its CTA's rows. What a thread did before its arrival
happens before what any thread of the CTA does after passing the arrival of the same ordinal
(`bar_baseCausality`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The barrier's thread count, omitted, is the CTA's 8 warps. -/
theorem target_none (hpre : Pre P L mem0) : target L.block none = .ok 8 := by
  rw [hpre.hyp.block]; rfl

theorem warps_bound (hpre : Pre P L mem0) : ∀ w ∈ Finset.range 8, w < L.block / 32 := by
  intro w hw
  rw [hpre.hyp.block]
  simpa using hw

theorem cta_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid := by
  have hb : 0 < L.block := by rw [hpre.hyp.block]; decide
  exact (Nat.div_lt_iff_lt_mul hb).mpr hg

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A barrier arrival** fires from a barrier site, for the whole CTA. -/
theorem bar_facts {g k id pc : Nat} {count : Option Nat} (he : X.IsBarrier (g, k) id count pc) :
    g < L.threads ∧ count = none ∧ ∃ d, At P L X g k d ⟨pc, .bar id count⟩ ∧
      ((d.site = .bar0 ∧ id = 0) ∨ (d.site = .bar1 ∧ id = 0) ∨ (d.site = .bar2 ∧ id = 1)) := by
  obtain ⟨hg, d, hA⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨hc, hs⟩ := bar_site hA.event
  exact ⟨hg, hc, d, hA, hs⟩

/-- **The barrier's protocol**: every arrival on barrier `id` in a CTA's history is by one of its
8 warps, for the whole CTA. -/
theorem protocol {c : Nat} (hc : c < L.grid) (id : Nat) :
    NamedBar.Protocol none (Finset.range 8) id (X.barriers c) := by
  refine NamedBar.protocol_of_src hX (fun e pc cnt hbar hec => ?_) hc
    (by rw [hpre.hyp.block]; decide)
  obtain ⟨-, hcnt, -⟩ := bar_facts hpre hX ht hbar
  refine ⟨?_, hcnt⟩
  rw [Finset.mem_range, hpre.hyp.block]
  omega

theorem protocol_prefix {c : Nat} (hc : c < L.grid) (id i : Nat) :
    NamedBar.Protocol none (Finset.range 8) id ((X.barriers c).take i) :=
  fun r hr => protocol hpre hX ht hc id r (List.mem_of_mem_take hr)

theorem prefixFor {e : EvId} (he : e.1 < L.threads) (id : Nat) :
    NamedBar.PrefixFor L X none (Finset.range 8) id e := by
  intro index warp cnt lanes hr _
  have hproto := protocol hpre hX ht (cta_lt hpre he) id
  exact ⟨protocol_prefix hpre hX ht (cta_lt hpre he) id index,
    hproto _ (List.mem_of_getElem? hr) rfl⟩

/-- **A passed barrier released its generation**, the arrival's ordinal. -/
theorem released {h j id pc : Nat} (hf : X.IsBarrier (h, j) id none pc)
    (hpassed : j + 1 < (X.tr h).length) :
    Released L.block (X.barriers (h / L.block)) id
      (((X.tr h).take j).countP (Execution.isBarId id)) := by
  have hge := Frame.lt_of_get hX hf
  have hk := NamedBar.passed_key hX (n := 8) (by decide) (target_none hpre) hf hpassed
    (prefixFor hpre hX ht hge id) (Finset.card_range 8) (warps_bound hpre)
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have := CtaBarK.key_unique hX.ctaBar hkey hk
  subst this
  obtain ⟨-, -, d, hA, hs⟩ := bar_facts hpre hX ht hf
  have hid : id < 2 := by rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  unfold CtaBarDone at hdone
  rw [show (id + 16 * ((X.tr h).take j).countP (Execution.isBarId id)) % 16 = id by omega,
    show (id + 16 * ((X.tr h).take j).countP (Execution.isBarId id)) / 16 =
      ((X.tr h).take j).countP (Execution.isBarId id) by omega] at hdone
  exact hdone

/-- The position of a row's arrival of a given kind: the first, second or third barrier. -/
def barPos (g : Nat) : Nat → Nat
  | 0 => 29 + l0 g
  | 1 => p1 g
  | _ => p1 g + 34

/-- **The arrival at a row's barrier**, for a thread with a later event than it. -/
theorem arrival_before {w k i b : Nat} {e : Event} (hx : X.get (w, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hb : b < 3) (hlt : rowBase w i + barPos w b < k) :
    ∃ d' pc', X.get (w, rowBase w i + barPos w b) = some ⟨pc', .bar (if b = 2 then 1 else 0) none⟩ ∧
      At P L X w (rowBase w i + barPos w b) d' ⟨pc', .bar (if b = 2 then 1 else 0) none⟩ ∧
      d'.i = i ∧ d'.site = (if b = 0 then .bar0 else if b = 1 then .bar1 else .bar2) := by
  have hR : barPos w b < rowLen w := by
    have := l0_le w; unfold barPos rowLen p1; split <;> omega
  have hjl : rowBase w i + barPos w b < (X.tr w).length := by
    have := len_of_get hx; simp only at this; omega
  obtain ⟨d', e', he', hA'⟩ := earlier_facts hpre hX ht hx hub hlt.le hjl
  have hwg := Frame.lt_of_get hX hx
  have hin : d'.site.inRow = true := by
    have hix := hA'.index
    cases hs : d'.site <;> simp only [Site.inRow]
    · simp only [D.idx, hs] at hix; unfold rowBase at hix; omega
    · obtain ⟨pcq, rfl⟩ := exit_site_of hA'.event hs
      have := Execution.exit_last hX hwg he'
      have := len_of_get hx; simp only at this
      omega
  obtain ⟨hi', hp'⟩ := idx_row hA'.inv hin hR (hA'.index.symm)
  have hsite : d'.site = (if b = 0 then .bar0 else if b = 1 then .bar1 else .bar2) := by
    interval_cases b
    · exact bar0_of_pos hA'.inv hp'
    · exact bar1_of_pos hA'.inv hp'
    · exact bar2_of_pos hA'.inv hp'
  obtain ⟨t, o, hf⟩ := hA'.event
  have hev : ∃ pc', e' = ⟨pc', .bar (if b = 2 then 1 else 0) none⟩ := by
    interval_cases b <;> simp only [siteTmpl, hsite, Fires, ↓reduceIte] at hf <;>
      exact ⟨_, hf.1⟩
  obtain ⟨pc', rfl⟩ := hev
  exact ⟨d', pc', he', hA', hi', hsite⟩

/-- **Every thread of a CTA has its arrival of a released ordinal**, when a thread of the CTA
arrived with that ordinal. -/
theorem arrival_exists {c id n w r k pc : Nat} (hd : Released L.block (X.barriers c) id n)
    (hw : w < L.threads) (hwc : w / L.block = c) (hrb : X.IsBarrier (r, k) id none pc)
    (hrc : r / L.block = c) (hn : ((X.tr r).take k).countP (Execution.isBarId id) = n) :
    ∃ j pc', X.IsBarrier (w, j) id none pc' ∧
      ((X.tr w).take j).countP (Execution.isBarId id) = n := by
  have hB := hpre.hyp.block
  have hc : c < L.grid := hwc ▸ cta_lt hpre hw
  by_cases hex : ∃ j pc, X.get (w, j) = some ⟨pc, .exit⟩
  · obtain ⟨jx, pcx, hx⟩ := hex
    obtain ⟨-, dx, hAx⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
    have hxs := exit_site hAx.event
    obtain ⟨-, -, dr, hAr, hs⟩ := bar_facts hpre hX ht hrb
    have hrow := hAr.inv.row (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.inRow])
    have hex' := hAx.inv.exit hxs
    have hcw : w / 256 = r / 256 := by rw [← hB]; omega
    have hlt : dr.i < dx.i := by unfold row at hrow; omega
    have hidx : jx = rowBase w dx.i := by rw [hAx.index]; simp [D.idx, hxs]
    have hpos : ∀ b < 3, rowBase w dr.i + barPos w b < jx := by
      intro b hb
      have hR : barPos w b < rowLen w := by
        have := l0_le w; unfold barPos rowLen p1; split <;> omega
      rw [hidx]; unfold rowBase
      have : rowLen w * dr.i + rowLen w ≤ rowLen w * dx.i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    rcases hs with ⟨hs, rfl⟩ | ⟨hs, rfl⟩ | ⟨hs, rfl⟩
    · obtain ⟨d', pc', he', hA', hi', hs'⟩ := arrival_before hpre hX ht hx (by intro _ _ h; cases h)
        (b := 0) (by decide) (hpos 0 (by decide))
      refine ⟨_, pc', he', ?_⟩
      rw [hA'.bc0, ← hn, hAr.bc0]
      simp only [↓reduceIte] at hs'
      simp [D.bc0, hs, hs', hi']
    · obtain ⟨d', pc', he', hA', hi', hs'⟩ := arrival_before hpre hX ht hx (by intro _ _ h; cases h)
        (b := 1) (by decide) (hpos 1 (by decide))
      refine ⟨_, pc', he', ?_⟩
      rw [hA'.bc0, ← hn, hAr.bc0]
      simp only [↓reduceIte, Nat.one_ne_zero] at hs'
      simp [D.bc0, hs, hs', hi']
    · obtain ⟨d', pc', he', hA', hi', hs'⟩ := arrival_before hpre hX ht hx (by intro _ _ h; cases h)
        (b := 2) (by decide) (hpos 2 (by decide))
      refine ⟨_, pc', he', ?_⟩
      rw [hA'.bc1, ← hn, hAr.bc1]
      simp at hs'
      simp [D.bc1, hs, hs', hi']
  · push Not at hex
    have hb : 0 < L.block := by rw [hB]; decide
    have hwr : c * L.block + w % L.block = w := by
      rw [← hwc, Nat.mul_comm]; exact Nat.div_add_mod w L.block
    have hid : id < 16 := by
      obtain ⟨-, -, d, -, hs⟩ := bar_facts hpre hX ht hrb
      rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
    obtain ⟨e, pce, he1, hbe, hord, -⟩ := NamedBar.released_member_key hX (n := 8) (by decide)
      (target_none hpre) (p := Finset.range 8) hc hid hd
      (fun i _ => protocol_prefix hpre hX ht hc id (i + 1)) (Finset.card_range 8)
      (warps_bound hpre) (Nat.mod_lt _ hb) (by rw [hB, Finset.mem_range]; omega)
      (by rw [hwr]; exact hex)
    obtain ⟨e1, e2⟩ := e
    simp only at he1 hord
    rw [hwr] at he1
    subst he1
    exact ⟨e2, pce, hbe, hord⟩

/-- **The barriers synchronize the CTA**: a thread's events before its arrival happen before a
thread's events after it passed the arrival of the same ordinal. -/
theorem bar_baseCausality {r w i id pc : Nat} (hr : X.IsBarrier (r, i) id none pc)
    (hpassed : i + 1 < (X.tr r).length) (hw : w < L.threads) (hwc : w / 256 = r / 256) :
    ∃ j pc', X.IsBarrier (w, j) id none pc' ∧
      ((X.tr w).take j).countP (Execution.isBarId id) =
        ((X.tr r).take i).countP (Execution.isBarId id) ∧
      ∀ before after, before < j → i < after → after < (X.tr r).length →
        baseCausality L X (w, before) (r, after) := by
  have hB := hpre.hyp.block
  have hrg := Frame.lt_of_get hX hr
  have hd := released hpre hX ht hr hpassed
  have hcw : w / L.block = r / L.block := by rw [hB]; exact hwc
  obtain ⟨j, pc', hbw, hord⟩ := arrival_exists hpre hX ht hd hw hcw hr rfl rfl
  have hid : id < 16 := by
    obtain ⟨-, -, d, -, hs⟩ := bar_facts hpre hX ht hr
    rcases hs with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  refine ⟨j, pc', hbw, hord, fun before after hb ha hl => ?_⟩
  have hwp : (w % L.block) / 32 ∈ Finset.range 8 := by rw [hB, Finset.mem_range]; omega
  exact NamedBar.reached_same_ordinal_baseCausality hX (n := 8) (by decide) (target_none hpre)
    (p := Finset.range 8) hid ⟨hw, hrg, hcw⟩ hbw hr hpassed hwp
    (prefixFor hpre hX ht hrg id) hord
    (fun idx _ => protocol_prefix hpre hX ht (cta_lt hpre hrg) id (idx + 1)) (Finset.card_range 8)
    (warps_bound hpre) hb ha hl

end
end PTX.Kernels.RmsNorm.Proof
