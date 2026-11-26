-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PrevPc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.SuccLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.VoteCmp
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepInto

@[expose] public section

/-! # The events around the row-maximum exchange follow the code's chain

Consecutive events of a lane of warpgroup 0 sit at consecutive sites of the code's chain: the store
at pc 566 (`mst`) is followed by the barrier at 569, the epilogue's store at 1155 by the barrier
at 1156 (`w0_next_566`, `w0_next_1155`), and an event at 569 or 1156 follows a store at 566 or
1155 (`w0_prev_569`, `w0_prev_1156`). Read off `PrevPc` of the data machine (`FollowW`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem W0Trace.take {P : Params} {X : Execution} {g : Nat} (h : W0Trace P X g) (j : Nat) :
    W0Valid P.scale ((X.tr g).take j) := W0Valid.take h

namespace Wg0
open Wg0.Data

private theorem site_of_pc (s : Site) (h : s.pc = 566 ∨ s.pc = 569 ∨ s.pc = 1155 ∨ s.pc = 1156) :
    s = .mst ∨ s = .bar2 ∨ s = .est ∨ s = .ebar1 := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

private theorem succOk_ebar1 {c c' : Control.D} (h : succOk c c' = true)
    (hs : c'.site = .ebar1) : c.site = .est := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem arrS_not {c c' : Control.D} {f : Event} {s : Site}
    (h : Control.succ P L g (warpW L g) c f = some (some c')) (hc : c.site = .arrS)
    (hs : c'.site = s) (hn : s ≠ .bar0 ∧ s ≠ .ebar0) : False := by
  simp only [Control.succ, hc] at h
  split at h <;> cases h <;> simp_all

/-- **An event at pc 569 follows the store at pc 566.** -/
theorem w0_prev_569 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u) (hpc : e'.pc = 569)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ f, X.get (g, j) = some f ∧ f.pc = 566 := by
  obtain ⟨f, hf, hm⟩ := w0_prev_pc hp hX hFw hw he' hub (by rw [hpc]; decide) hv0
  rw [hpc] at hm
  exact ⟨f, hf, by simpa [w0Prev] using hm⟩

/-- **An event at pc 1156 follows the store at pc 1155.** -/
theorem w0_prev_1156 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u) (hpc : e'.pc = 1156)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ f, X.get (g, j) = some f ∧ f.pc = 1155 := by
  obtain ⟨f, c, d, hf, hpcf, hs, hsucc, hc⟩ := w0_step_into_hub hp hX hFw hw he' hub (by omega)
    hv0 (s := .ebar1) (fun s' h => by
      rcases site_of_pc s' (by omega) with h1 | h1 | h1 | h1 <;> subst h1 <;>
        first | rfl | (exfalso; revert h; rw [hpc]; decide))
    (by decide)
  refine ⟨f, hf, ?_⟩
  rcases hc with hc | hc
  · exact (arrS_not hsucc hc hs (by simp)).elim
  · rw [← hpcf, succOk_ebar1 hc hs]; rfl

/-- **The step out of an event**: from the event at index `j` at a site `s` of pc `pcs` the next
event's data state is reached through the control step. -/
private theorem w0_step_out (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u)
    (hge : 103 ≤ f.pc)
    (hv : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ (c : Control.D) (d : D), c.site.pc = f.pc ∧ e'.pc = d.c.site.pc ∧
      Control.succ P L g (warpW L g) c f = some (some d.c) := by
  obtain ⟨st, hst, hslot, hpre, hI, hPrev, -⟩ :=
    followW hp hX hFw hw he' hub (w0_scale_rd hp) hv (j + 1) le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he' hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    have hmem : f ∈ (X.tr g).take (j + 1) := by
      have : (X.tr g)[j]? = some f := hf
      rw [List.mem_iff_getElem?]
      exact ⟨j, by rw [List.getElem?_take]; simpa using this⟩
    have := hpre b rfl f hmem
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  rcases hPrev d rfl j rfl with ⟨-, hlt⟩ | ⟨f', c, hf', hpcf, hsucc, -⟩
  · have hmem : f ∈ (X.tr g).take (j + 1) := by
      have : (X.tr g)[j]? = some f := hf
      rw [List.mem_iff_getElem?]
      exact ⟨j, by rw [List.getElem?_take]; simpa using this⟩
    have := hlt f hmem
    omega
  · have hff : f' = f := by
      have : (X.tr g)[j]? = some f := hf
      rw [this] at hf'
      exact (Option.some.inj hf').symm
    subst hff
    exact ⟨c, d, hpcf, hpc', hsucc⟩

/-- **The store at pc 566 is followed by the barrier at pc 569.** -/
theorem w0_next_566 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 566) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) : e'.pc = 569 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) hv0
  have hs : c.site = .mst := by
    rcases site_of_pc c.site (by omega) with h | h | h | h <;>
      first | exact h | (exfalso; rw [h, hpc] at hc; exact absurd hc (by decide))
  rw [he]
  simp only [Control.succ, hs] at hsucc
  have := Option.some.inj (Option.some.inj hsucc)
  rw [← this]
  rfl

/-- The only site at pc 572 is the exchange load. -/
private theorem site_of_pc_572 (s : Site) (h : s.pc = 572) : s = .mld := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The exchange load at pc 572 is followed by the vote at pc 578.** -/
theorem w0_next_572 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 572) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) : e'.pc = 578 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) hv0
  have hs : c.site = .mld := site_of_pc_572 _ (hc.trans hpc)
  rw [he]
  simp only [Control.succ, hs, Control.dataRd] at hsucc
  split at hsucc
  · have := Option.some.inj (Option.some.inj hsucc)
    rw [← this]
    rfl
  · have := Option.some.inj (Option.some.inj hsucc)
    rw [← this]
    rfl
  · cases hsucc

/-- **The vote at pc 578 is followed by an event past it** (the first site of the output
stores). -/
theorem w0_next_578 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 578) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Trace P X g) : 578 < e'.pc := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) (hv0.take (j + 1))
  have hs : c.site = .vote := site_vote_of_pc (hc.trans hpc)
  rw [he]
  simp only [Control.succ, hs] at hsucc
  split at hsucc
  · have := Option.some.inj (Option.some.inj hsucc)
    rw [← this]
    show 578 < Site.pc (.ost 0)
    decide
  · cases hsucc

/-- **The store at pc 1155 is followed by the barrier at pc 1156.** -/
theorem w0_next_1155 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 1155) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) : e'.pc = 1156 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) hv0
  have hs : c.site = .est := by
    rcases site_of_pc c.site (by omega) with h | h | h | h <;>
      first | exact h | (exfalso; rw [h, hpc] at hc; exact absurd hc (by decide))
  rw [he]
  simp only [Control.succ, hs] at hsucc
  have := Option.some.inj (Option.some.inj hsucc)
  rw [← this]
  rfl

/-- **The barrier at pc 1156 is followed by the row-sum load at pc 1157.** -/
theorem w0_next_1156 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 1156) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Trace P X g) : e'.pc = 1157 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) (hv0.take (j + 1))
  have hs : c.site = .ebar1 := by
    rcases site_of_pc c.site (by omega) with h | h | h | h <;>
      first | exact h | (exfalso; rw [h, hpc] at hc; exact absurd hc (by decide))
  rw [he]
  simp only [Control.succ, hs] at hsucc
  have := Option.some.inj (Option.some.inj hsucc)
  rw [← this]
  rfl

/-- **The row-sum load at pc 1157 is followed by the log-sum-exp store or the wait after it.** -/
theorem w0_next_1157 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {f e' : Event}
    (hf : X.get (g, j) = some f) (hpc : f.pc = 1157) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Trace P X g) : e'.pc = 1178 ∨ e'.pc = 1184 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) (hv0.take (j + 1))
  have hs : c.site = .eld := Data.site_pc_1157 (hc.trans hpc)
  rw [he]
  simp only [Control.succ, hs, Control.dataRd] at hsucc
  split at hsucc
  all_goals first
    | (cases hsucc)
    | (have h2 := Option.some.inj (Option.some.inj hsucc)
       rw [← h2]
       rcases Control.site_afterEld (L := L) (g := g) c with h | h <;> simp [h, Site.pc])

/-- A valid prefix has valid shorter prefixes. -/
theorem W0Valid.take_le {sc : ℝ} {l : List Event} {k m : Nat} (h : W0Valid sc (l.take k))
    (hm : m ≤ k) : W0Valid sc (l.take m) := by
  have := h.take (j := m)
  rwa [List.take_take, Nat.min_eq_left hm] at this

/-- **The pcs of a block do not go back**: between the events at indices `i` and `i + n` of a lane
of warpgroup 0, none of the first `n` at the arrival pc 1122, the pc does not fall. -/
theorem w0_pc_mono (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {N : Nat}
    (hv0 : W0Valid P.scale ((X.tr g).take N)) {i : Nat} :
    ∀ (n : Nat) {f f' : Event}, i + n ≤ N → X.get (g, i) = some f → X.get (g, i + n) = some f' →
      (∀ u, f'.kind ≠ .ub u) → 103 ≤ f.pc → (∀ q < n, ∀ ev, X.get
      (g, i + q) = some ev → ev.pc ≠ 1122) → f.pc ≤ f'.pc
  | 0, f, f', _, hf, hf', _, _, _ => by
    rw [Nat.add_zero, hf] at hf'
    cases hf'
    exact le_rfl
  | n + 1, f, f', hN, hf, hf', hub, hge, hno => by
    have hlen : i + n < (X.tr g).length := by
      have hf2 : (X.tr g)[i + (n + 1)]? = some f' := hf'
      have := (List.getElem?_eq_some_iff.mp hf2).1
      omega
    obtain ⟨f'', hf''⟩ : ∃ f'', X.get (g, i + n) = some f'' :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    have hub'' := NoUbBefore.ne (noUbBefore_of_get hX hf') (Nat.lt_succ_self _) hf''
    have h1 := w0_pc_mono hp hX hFw hw hv0 n (by omega) hf hf'' hub'' hge
      (fun q hq ev hev => hno q (by omega) ev hev)
    obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf'' hf' hub (by omega)
      (W0Valid.take_le hv0 (by omega))
    have hs : c.site ≠ .arrS := fun h => hno n (by omega) f'' hf'' (by
      rw [← hc, h]; rfl)
    have := Control.succ_pc_mono hsucc hs
    rw [he]
    omega

/-- **A block's pcs stay in the block**: from an event at pc 566 to 1121, no event at the arrival
pc 1122 up to the event `n` later, that event is at pc 566 to 1121. -/
theorem w0_loop_stays (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hv0 : W0Trace P X g) {i : Nat}
    {f : Event} (hf : X.get (g, i) = some f) (h1 : 566 ≤ f.pc) (h2 : f.pc ≤ 1121) :
    ∀ (n : Nat) {f' : Event}, X.get (g, i + n) = some f' → (∀ u, f'.kind ≠ .ub u) →
      (∀ q ≤ n, ∀ ev, X.get (g, i + q) = some ev → ev.pc ≠ 1122) →
      566 ≤ f'.pc ∧ f'.pc ≤ 1121
  | 0, f', hf', _, _ => by
    rw [Nat.add_zero, hf] at hf'
    cases hf'
    exact ⟨h1, h2⟩
  | n + 1, f', hf', hub, hno => by
    have hlen : i + n < (X.tr g).length := by
      have hf2 : (X.tr g)[i + (n + 1)]? = some f' := hf'
      have := (List.getElem?_eq_some_iff.mp hf2).1
      omega
    obtain ⟨f'', hf''⟩ : ∃ f'', X.get (g, i + n) = some f'' :=
      ⟨_, List.getElem?_eq_getElem hlen⟩
    have hub'' := NoUbBefore.ne (noUbBefore_of_get hX hf') (Nat.lt_succ_self _) hf''
    obtain ⟨hl, hu⟩ := w0_loop_stays hp hX hFw hw hv0 hf h1 h2 n hf'' hub''
      (fun q hq ev hev => hno q (by omega) ev hev)
    obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf'' hf' hub (by omega)
      (hv0.take (i + n + 1))
    have hs : c.site ≠ .arrS := fun h => by rw [h] at hc; simp [Site.pc] at hc; omega
    have hm := Control.succ_pc_mono hsucc hs
    have hb := Control.succ_loop hsucc (by omega) (by omega)
    have hne := hno (n + 1) le_rfl f' hf'
    rw [he]
    omega

/-- No event of a lane of warpgroup 0 at a pc of its loop is its first. -/
theorem w0_not_first (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {e : Event} (he : X.get (g, 0) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hr : 103 ≤ e.pc ∧ e.pc < 1842) : False := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d0, n0, hσe, -⟩ := wg0_state hJ hi hev hpc hr
  rw [Frame.stateAt_zero] at hσ
  have h0 := Option.some.inj (Option.some.inj hσ)
  rw [hσe] at h0
  simp [thread, Code.roleThread, Code.enter, Code.gatedExit, startupEnter, Startup.exitOf] at h0

/-- **A rescale store follows its load and the load's wait**: the events before a store of
warpgroup 0 at the pc of chunk `c`'s rescale store are the chunk's load (a `tcgen05.ld`) and its
wait, the two events before it. -/
theorem w0_rst_prev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat}
    (hv0 : W0Valid P.scale ((X.tr g).take k))
    {e : Event} (he : X.get (g, k) = some e) (hub : ∀ u, e.kind ≠ .ub u) {c : Fin 4}
    (hpc : e.pc = [814, 915, 1016, 1117].getD c.val 0) :
    ∃ (j : Nat) (f0 f1 : Event) (a : Nat) (vals : List Value) (sh : TcShape), k = j + 2 ∧
      X.get (g, j) = some f0 ∧ f0.pc = [716, 817, 918, 1019].getD c.val 0 ∧
      f0.kind = .tc (.ld a vals sh) ∧ X.get (g, j + 1) = some f1 ∧
      f1.pc = [717, 818, 919, 1020].getD c.val 0 := by
  have hpcs : ∀ c : Fin 4, 103 ≤ [814, 915, 1016, 1117].getD c.val 0 ∧
      [814, 915, 1016, 1117].getD c.val 0 < 1842 := by decide
  obtain ⟨j1, rfl⟩ : ∃ j1, k = j1 + 1 := by
    cases k with
    | zero => exact (w0_not_first hp hX hFw he hub (hpc ▸ hpcs c)).elim
    | succ j => exact ⟨j, rfl⟩
  obtain ⟨f1, c1, d1, hf1, hpcf1, hs1, hsucc1, hc1⟩ := w0_step_into_hub hp hX hFw hw he hub
    (by rw [hpc]; exact (hpcs c).1) hv0 (s := .rst c)
    (fun s' h => site_pc_inj (h.trans hpc)) (by fin_cases c <;> decide)
  have hub1 : ∀ u, f1.kind ≠ .ub u := NoUbBefore.ne (noUbBefore_of_get hX he)
    (Nat.lt_succ_self _) hf1
  have hrldw : c1.site = .rldw c := by
    rcases hc1 with hc1 | hc1
    · exact (arrS_not hsucc1 hc1 hs1 (by simp)).elim
    · exact succOk_rst hc1 hs1
  have hpcf1' : f1.pc = [717, 818, 919, 1020].getD c.val 0 := by
    rw [← hpcf1, hrldw]; rfl
  obtain ⟨j0, rfl⟩ : ∃ j0, j1 = j0 + 1 := by
    cases j1 with
    | zero =>
      refine (w0_not_first hp hX hFw hf1 hub1 ?_).elim
      rw [hpcf1']
      fin_cases c <;> decide
    | succ j => exact ⟨j, rfl⟩
  obtain ⟨f0, c0, d0, hf0, hpcf0, hs0, hsucc0, hc0⟩ := w0_step_into_hub hp hX hFw hw hf1 hub1
    (by rw [hpcf1']; fin_cases c <;> decide) (W0Valid.take_le hv0 (by omega)) (s := .rldw c)
    (fun s' h => site_pc_inj (h.trans hpcf1')) (by fin_cases c <;> decide)
  have hrld : c0.site = .rld c := by
    rcases hc0 with hc0 | hc0
    · exact (arrS_not hsucc0 hc0 hs0 (by simp)).elim
    · exact succOk_rldw hc0 hs0
  have hsl : Control.succ P L g (warpW L g) c0 f0 = some (some d0.c) := hsucc0
  have hkind : ∃ a vals sh, f0.kind = .tc (.ld a vals sh) := by
    simp only [Control.succ, hrld, Control.tcLoad] at hsl
    split at hsl
    · rename_i a vals sh hk
      exact ⟨a, vals, sh, hk⟩
    · cases hsl
  obtain ⟨a, vals, sh, hk⟩ := hkind
  refine ⟨j0, f0, f1, a, vals, sh, rfl, hf0, ?_, hk, hf1, hpcf1'⟩
  rw [← hpcf0, hrld]
  rfl


/-- The sites at the peer stores' pcs and the pair barrier's pc. -/
private theorem site_pst_of_pc (s : Site) (h : (∃ k < 8, s.pc = 403 + 10 * k) ∨ s.pc = 475) :
    (∃ k : Fin 8, s = .pst k) ∨ s = .bar1 := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

private theorem innerSite_pst (k : Fin 8) : innerSite (.pst k) = true := by
  fin_cases k <;> rfl

private theorem succOk_pst {c c' : Control.D} (h : succOk c c' = true) {k : Fin 8}
    (hk : k.val < 7) (hs : c'.site = .pst ⟨k.val + 1, by omega⟩) : c.site = .pst k := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  obtain ⟨k, hk8⟩ := k
  simp only at hk
  interval_cases k <;> cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

/-- **The store at pc `403 + 10 k` is followed by the store `k + 1` or the barrier at pc 475.** -/
theorem w0_next_pst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j k : Nat} {f e' : Event}
    (hk : k < 8) (hf : X.get (g, j) = some f) (hpc : f.pc = 403 + 10 * k)
    (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) :
    e'.pc = if k < 7 then 403 + 10 * (k + 1) else 475 := by
  obtain ⟨c, d, hc, he, hsucc⟩ := w0_step_out hp hX hFw hw hf he' hub (by omega) hv0
  have hs : c.site = .pst ⟨k, hk⟩ := by
    rcases site_pst_of_pc c.site (.inl ⟨k, hk, hc.trans hpc⟩) with ⟨k', h⟩ | h
    · rw [h] at hc ⊢
      have : k'.val = k := by simp only [Site.pc] at hc; omega
      exact congrArg _ (Fin.ext this)
    · rw [h] at hc
      simp only [Site.pc] at hc
      omega
  rw [he]
  simp only [Control.succ, hs] at hsucc
  have := Option.some.inj (Option.some.inj hsucc)
  rw [← this]
  interval_cases k <;> rfl

/-- **An event at the store `k + 1` follows the store `k`.** -/
theorem w0_prev_pst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j k : Nat} {e' : Event}
    (hk : k < 7) (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u)
    (hpc : e'.pc = 403 + 10 * (k + 1))
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ f, X.get (g, j) = some f ∧ f.pc = 403 + 10 * k := by
  obtain ⟨f, hf, hm⟩ := w0_prev_pc hp hX hFw hw he' hub (by
    rw [hpc]; interval_cases k <;> decide) hv0
  rw [hpc] at hm
  refine ⟨f, hf, ?_⟩
  interval_cases k <;> simpa [w0Prev] using hm

/-- **An event at the pair barrier (pc 475) follows the store 7.** -/
theorem w0_prev_bar1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u) (hpc : e'.pc = 475)
    (hv0 : W0Valid P.scale ((X.tr g).take (j + 1))) :
    ∃ f, X.get (g, j) = some f ∧ f.pc = 473 := by
  obtain ⟨f, hf, hm⟩ := w0_prev_pc hp hX hFw hw he' hub (by rw [hpc]; decide) hv0
  rw [hpc] at hm
  exact ⟨f, hf, by simpa [w0Prev] using hm⟩

end Wg0

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
