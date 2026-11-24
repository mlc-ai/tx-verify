-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.Protocol.Events
public import Lemmas.Step.CtaBarNamed
public import Lemmas.Protocol.NamedBarSync
public import Kernels.TcGemm.Proof.NoBarArrive

@[expose] public section

/-! # `tc_gemm`: the CTA barrier

Every arrival on a CTA barrier is a thread's `bar.sync 0` for the whole CTA (`count = none`, the
CTA's 4 warps): its first, before the address read (ordinal 0), or its second, after the stores
(ordinal 1) (`Wit.barK`). So the CTA's barrier history follows the named-barrier protocol of the
4 warps (`protocol`), and a thread's events before its arrival happen before a thread's events
after its own arrival at the same ordinal, once that thread has passed (`sync0`, `sync1`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

section
variable (hpre : Pre L A B D a b mem0)
include hpre

/-- The barrier's thread count, omitted, is the CTA's 4 warps. -/
theorem target_none : target L.block none = .ok 4 := by rw [hpre.block]; rfl

theorem warps_bound : ∀ w ∈ Finset.range 4, w < L.block / 32 := by
  intro w hw
  rw [hpre.block]
  simpa using hw

end

section
variable (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X)
  (hW : Wit A B D L.sharedBase X P m u)
include hpre hX hW

omit hX in
/-- Every arrival is barrier `0` of the whole CTA, by one of its 4 warps. -/
theorem bar_src {e : EvId} {id pc : Nat} {cnt : Option Nat} (he : X.IsBarrier e id cnt pc) :
    id = 0 ∧ cnt = none ∧ e.1 < 128 ∧ (e.1 % L.block) / 32 ∈ Finset.range 4 := by
  obtain ⟨g, j⟩ := e
  have hcnt := hW.bar_full he
  subst hcnt
  obtain ⟨hg, -, rfl, -⟩ := hW.bar he
  refine ⟨rfl, rfl, hg, ?_⟩
  rw [Finset.mem_range, hpre.block]
  simp only
  omega

/-- **The barrier's protocol**: every arrival in the CTA's history is by one of its 4 warps, for
the whole CTA. -/
theorem protocol : NamedBar.Protocol none (Finset.range 4) 0 (X.barriers 0) := by
  refine NamedBar.protocol_of_src hX (fun e pc cnt hbar _ => ?_) (by rw [hpre.grid]; decide)
    (by rw [hpre.block]; decide)
  obtain ⟨-, hc, -, hw⟩ := bar_src hpre hW hbar
  exact ⟨hw, hc⟩

theorem prefixFor {e : EvId} (he : e.1 < 128) :
    NamedBar.PrefixFor L X none (Finset.range 4) 0 e := by
  intro index warp cnt lanes hr _
  rw [cta_zero hpre he] at hr ⊢
  have hproto := protocol hpre hX hW
  exact ⟨fun r hr' => hproto r (List.mem_of_mem_take hr'), hproto _ (List.mem_of_getElem? hr) rfl⟩

/-- On a thread's trace, barrier-0 arrivals are all its barrier arrivals. -/
theorem barId_eq {g j : Nat} :
    ((X.tr g).take j).countP (Execution.isBarId 0) = ((X.tr g).take j).countP Execution.isBar := by
  apply List.countP_congr
  intro ev hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem (List.mem_of_mem_take hm)
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp [Execution.isBarId, Execution.isBar]
  rename_i id cnt mode
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (g, k) _ _ _ hk).elim
  have he : X.IsBarrier (g, k) id cnt pc := hk
  exact (bar_src hpre hW he).1

omit hX hW in
theorem sameCta {g h : Nat} (hg : g < 128) (hh : h < 128) : SameCta L g h :=
  ⟨by rw [threads_eq hpre]; exact hg, by rw [threads_eq hpre]; exact hh,
    (cta_zero hpre hg).trans (cta_zero hpre hh).symm⟩

/-- **Synchronization through a barrier ordinal**: an event of `h` before its arrival happens
before an event of `g` after its own arrival at the same ordinal. -/
theorem sync_of {h g bh bg i j pch pcg : Nat} (hh : h < 128) (hg : g < 128)
    (bhe : X.IsBarrier (h, bh) 0 none pch) (bge : X.IsBarrier (g, bg) 0 none pcg)
    (hord : ((X.tr h).take bh).countP Execution.isBar = ((X.tr g).take bg).countP Execution.isBar)
    (hi : i < bh) (hj : bg < j) (hjl : j < (X.tr g).length) : baseCausality L X (h, i) (g, j) := by
  have hproto := protocol hpre hX hW
  refine NamedBar.reached_same_ordinal_baseCausality hX (n := 4) (by decide) (target_none hpre)
      (by decide)
    (sameCta hpre hh hg) bhe bge (by omega) ?_ (prefixFor hpre hX hW hg)
    (by rw [barId_eq hpre hX hW, barId_eq hpre hX hW]; exact hord)
    (fun _ _ r hr => hproto r (by rw [cta_zero hpre hg] at hr; exact List.mem_of_mem_take hr))
    (Finset.card_range 4) (warps_bound hpre) hi hj hjl
  rw [Finset.mem_range, hpre.block]
  omega

omit hpre hX in
/-- The first barrier of a thread that has events after it is in its whole trace. -/
theorem bar0_in {g j : Nat} (hg : g < 128) (hj : hd g ≤ j) (hjl : j < (X.tr g).length) :
    hd g - 1 < m g := by
  have hl := hW.length g hg
  have := hd_pos (g := g)
  rcases hW.ub g hg with hu | ⟨pc, f, hu, -⟩ <;> rw [hu] at hl <;> simp at hl <;> omega

omit hpre hX in
/-- The second barrier of a thread that has events after it is in its whole trace. -/
theorem bar1_in {g j : Nat} (hg : g < 128) (hj : ldIdx g (P g) + 11 < j)
    (hjl : j < (X.tr g).length) : ldIdx g (P g) + 11 < m g := by
  have hl := hW.length g hg
  rcases hW.ub g hg with hu | ⟨pc, f, hu, -⟩ <;> rw [hu] at hl <;> simp at hl <;> omega

/-- **Synchronization through the first barrier**: an event of `h` before its first arrival
happens before an event of `g` after its own. -/
theorem sync0 {h g i j : Nat} (hh : h < 128) (hg : g < 128) (hi : i + 1 < hd h)
    (hmh : hd h - 1 < m h) (hj : hd g ≤ j) (hjl : j < (X.tr g).length) :
    baseCausality L X (h, i) (g, j) := by
  have hmg := bar0_in hW hg hj hjl
  have := hd_pos (g := g)
  have bh : X.IsBarrier (h, hd h - 1) 0 none Flow.bar_0 := by
    show X.get _ = _; rw [hW.get_of_lt hh hmh, fullAt_bar0]; rfl
  have bg : X.IsBarrier (g, hd g - 1) 0 none Flow.bar_0 := by
    show X.get _ = _; rw [hW.get_of_lt hg hmg, fullAt_bar0]; rfl
  have kh := hW.barK (k := ((X.tr h).take (hd h - 1)).countP Execution.isBar) ⟨⟨0, _, bh⟩, rfl⟩
  have kg := hW.barK (k := ((X.tr g).take (hd g - 1)).countP Execution.isBar) ⟨⟨0, _, bg⟩, rfl⟩
  have := ldIdx_eq (g := h) (P h)
  have := ldIdx_eq (g := g) (P g)
  have := tl_ge (g := h) (P h)
  have := tl_ge (g := g) (P g)
  refine sync_of hpre hX hW hh hg bh bg ?_ (by omega) (by omega) hjl
  rcases kh.2.2 with ⟨-, h1⟩ | ⟨h1, -⟩ <;> rcases kg.2.2 with ⟨-, h2⟩ | ⟨h2, -⟩ <;> omega

/-- **Synchronization through the second barrier**: an event of `h` before its second arrival
happens before an event of `g` after its own. -/
theorem sync1 {h g i j : Nat} (hh : h < 128) (hg : g < 128) (hi : i < ldIdx h (P h) + 11)
    (hmh : ldIdx h (P h) + 11 < m h) (hj : ldIdx g (P g) + 11 < j) (hjl : j < (X.tr g).length) :
    baseCausality L X (h, i) (g, j) := by
  have hmg := bar1_in hW hg hj hjl
  have bh : X.IsBarrier (h, ldIdx h (P h) + 11) 0 none Flow.bar_1 := by
    show X.get _ = _
    rw [hW.get_of_lt hh hmh, show ldIdx h (P h) + 11 = ldIdx h (P h) + 1 + 10 by omega, fullAt_post]
    rfl
  have bg : X.IsBarrier (g, ldIdx g (P g) + 11) 0 none Flow.bar_1 := by
    show X.get _ = _
    rw [hW.get_of_lt hg hmg, show ldIdx g (P g) + 11 = ldIdx g (P g) + 1 + 10 by omega, fullAt_post]
    rfl
  have kh := hW.barK (k := ((X.tr h).take (ldIdx h (P h) + 11)).countP Execution.isBar)
    ⟨⟨0, _, bh⟩, rfl⟩
  have kg := hW.barK (k := ((X.tr g).take (ldIdx g (P g) + 11)).countP Execution.isBar)
    ⟨⟨0, _, bg⟩, rfl⟩
  have := ldIdx_eq (g := h) (P h)
  have := ldIdx_eq (g := g) (P g)
  have := tl_ge (g := h) (P h)
  have := tl_ge (g := g) (P g)
  refine sync_of hpre hX hW hh hg bh bg ?_ hi hj hjl
  rcases kh.2.2 with ⟨h1, -⟩ | ⟨-, h1⟩ <;> rcases kg.2.2 with ⟨h2, -⟩ | ⟨-, h2⟩ <;> omega

/-- A passed arrival's generation is released. -/
theorem released_of_passed {f : EvId} {pc : Nat} (hf : X.IsBarrier f 0 none pc)
    (hpassed : f.2 + 1 < (X.tr f.1).length) :
    Released L.block (X.barriers 0) 0 (((X.tr f.1).take f.2).countP Execution.isBar) := by
  have hf128 := (bar_src hpre hW hf).2.2.1
  have hk := NamedBar.passed_key hX (n := 4) (by decide) (target_none hpre) hf hpassed
    (prefixFor hpre hX hW hf128) (Finset.card_range 4) (warps_bound hpre)
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have := CtaBarK.key_unique hX.ctaBar hkey hk
  subst this
  rw [barId_eq hpre hX hW] at hdone
  unfold CtaBarDone at hdone
  rw [cta_zero hpre hf128] at hdone
  simpa using hdone

/-- **Every thread arrives at a passed barrier ordinal**: once a thread has passed its arrival at
ordinal `k`, every thread of the CTA has an arrival at ordinal `k`. -/
theorem member_bar {g bg pc : Nat} (hf : X.IsBarrier (g, bg) 0 none pc)
    (hpassed : bg + 1 < (X.tr g).length) {h : Nat} (hh : h < 128) :
    ∃ j pc', X.IsBarrier (h, j) 0 none pc' ∧
      ((X.tr h).take j).countP Execution.isBar = ((X.tr g).take bg).countP Execution.isBar := by
  have hrel := released_of_passed hpre hX hW hf hpassed
  have hg := (bar_src hpre hW hf).2.2.1
  have kg := hW.barK (k := ((X.tr g).take bg).countP Execution.isBar) ⟨⟨0, _, hf⟩, rfl⟩
  by_cases hex : ∃ j pc, X.get (h, j) = some ⟨pc, .exit⟩
  · -- an exited thread made both arrivals
    obtain ⟨jx, pcx, hx⟩ := hex
    obtain ⟨-, hjx, hpos⟩ := hW.exit hx
    have := hd_pos (g := h)
    have := ldIdx_eq (g := h) (P h)
    have := tl_ge (g := h) (P h)
    have b0 : X.IsBarrier (h, hd h - 1) 0 none Flow.bar_0 := by
      show X.get _ = _; rw [hW.get_of_lt hh (by split at hpos <;> omega), fullAt_bar0]; rfl
    have b1 : X.IsBarrier (h, ldIdx h (P h) + 11) 0 none Flow.bar_1 := by
      show X.get _ = _
      rw [hW.get_of_lt hh (by split at hpos <;> omega),
        show ldIdx h (P h) + 11 = ldIdx h (P h) + 1 + 10 by omega, fullAt_post]
      rfl
    have k0 := hW.barK (k := ((X.tr h).take (hd h - 1)).countP Execution.isBar) ⟨⟨0, _, b0⟩, rfl⟩
    have k1 := hW.barK (k := ((X.tr h).take (ldIdx h (P h) + 11)).countP Execution.isBar)
      ⟨⟨0, _, b1⟩, rfl⟩
    rcases kg.2.2 with ⟨-, hk⟩ | ⟨-, hk⟩
    · refine ⟨_, _, b0, ?_⟩
      rcases k0.2.2 with ⟨-, h0⟩ | ⟨h0, -⟩ <;> omega
    · refine ⟨_, _, b1, ?_⟩
      rcases k1.2.2 with ⟨h0, -⟩ | ⟨-, h0⟩ <;> omega
  · push Not at hex
    have hproto := protocol hpre hX hW
    have hh' : h < L.block := by rw [hpre.block]; exact hh
    obtain ⟨e, pc', he1, hbar, hord, -⟩ := NamedBar.released_member_key hX (n := 4) (by decide)
      (target_none hpre) (p := Finset.range 4) (by rw [hpre.grid]; decide) (by decide) hrel
      (fun i _ r hr => hproto r (List.mem_of_mem_take hr)) (Finset.card_range 4) (warps_bound hpre)
      hh' (by rw [Finset.mem_range, hpre.block] at *; omega)
      (by simpa using hex)
    obtain ⟨e1, e2⟩ := e
    simp only [zero_mul, zero_add] at he1
    subst he1
    rw [barId_eq hpre hX hW] at hord
    exact ⟨e2, pc', hbar, hord⟩

end

end

end PTX.Kernels.TcGemm.Proof
