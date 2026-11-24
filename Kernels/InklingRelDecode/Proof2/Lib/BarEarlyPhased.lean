-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.BarFirst
public import Kernels.InklingRelDecode.Proof2.Lib.BarLaneKeys

@[expose] public section

/-!
# The hand-off of a barrier whose instances have their own groups

Generic, for promotion next to `Handoff.of_barEarly` (lane L). `Handoff.of_barEarly` asks one
`(count, p)` for every instance up to `N`. A barrier id used by several groups in turn has, per
instance, its own group and thread count. The form proved here is the one `NamedBar.PhSources`
describes: the instances below `start` are the CTA's whole block without a thread count, the
instances from `start` on are the warps `D` with the count `cD`, and the warps outside `D` may
make later arrivals of any form without a count (Inkling's barrier 0: the startup's two
`bar.sync 0`, then the default partition's `bar.sync 0, 128`, while the workers' last
`bar.sync 0` comes later). Instance `q` has the group `PhGroup L D start q`.

* `D_member_arrival`: a thread of `D` has the arrival of every ordinal a thread of `D` of its CTA
  passed, unless it exits, in which case the kernel says it made the arrival (`hexited`);
* `Handoff.of_barPhased`: an event of `g` whose producer use `q` (the barrier's events up to and
  including it) is at most `N` happens before an event of `h` of the same CTA after more barrier
  events of `h`, when `g` and `h` are in instance `q`'s group; every exiting thread has made
  `N + 1` arrivals before its exit.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {D : Finset Nat} {cD : Option Nat} {start id nD : Nat} [hK : Fact K.NoBarArrive]

/-- The group of instance `q`: the CTA's whole block below `start`, `D` from `start` on. -/
def PhGroup (L : Launch) (D : Finset Nat) (start q : Nat) : Finset Nat :=
  if q < start then Finset.range (warps L.block) else D

/-- **A thread of the loop group has the arrival of every ordinal a loop thread passed**: from the
release of the passed arrival's generation when the thread never exits, from `hexited` when it
exits. -/
theorem D_member_arrival (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) {f : EvId} {pc : Nat} {cnt : Option Nat}
    (hf : X.IsBarrier f id cnt pc) (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hwf : (f.1 % L.block) / 32 ∈ D) {g : Nat} (hcta : g / L.block = f.1 / L.block)
    (hw : (g % L.block) / 32 ∈ D)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc' cnt', X.IsBarrier (g, i) id cnt' pc' ∧
        ((X.tr g).take i).countP (Execution.isBarId id) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ i pc' cnt', X.IsBarrier (g, i) id cnt' pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  by_cases hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩
  · exact hexited hex
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkeq := D_arrival_key hX hS hD hcard hnD hcD hf hwf (CtaBarK.arrival hkf)
  have hfg : f.1 < L.threads := hkf.1
  have hb0 : 0 < L.block := block_pos_of_thread_lt hfg
  have hc : f.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb0).mpr hfg
  set c := f.1 / L.block with hcdef
  set φ := ((X.tr f.1).take f.2).countP (Execution.isBarId id) with hφ
  have hid : key % 16 = id := by
    obtain ⟨count', pc'', he'⟩ := hkf.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hf))).2).1
  have hmod : (id + 16 * φ) % 16 = id := by omega
  have hdiv : (id + 16 * φ) / 16 = φ := by omega
  have hrel : Released L.block (X.barriers c) id φ := by
    unfold CtaBarDone at hdone
    rw [hkeq, hmod, hdiv] at hdone
    exact hdone
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 c hc
  have hlt : φ < (last.slots id).generation := released_generation_lt hlast hrel
  have hthr : c * L.block + g % L.block = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hlive : g % L.block ∉ last.exited := by
    intro hm
    obtain ⟨a, ha⟩ := run_exited_mem hlast hm
    obtain ⟨-, hy, pcx, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ ha
    have hae : a = (c * L.block + g % L.block, a.2) := Prod.ext hy rfl
    rw [hthr] at hae
    exact hex ⟨a.2, pcx, hae ▸ hget⟩
  have hlocal : g % L.block < L.block := Nat.mod_lt _ hb0
  obtain ⟨i, cnt', lanes, e', hi, hmem, hord, -⟩ :=
    completed_D_record hD hcard hnD hcD (hS.protocol hX hc) hlast hlt hlocal hw hlive
  obtain ⟨s1, t1, hat, -⟩ := run_at_record hlast hi
  obtain ⟨-, hq2, -, ⟨pce, mode, hget⟩, hord', -⟩ :=
    record_ordinal hX hc hlast hi hat (q := (g % L.block, e')) hmem
  have hee : e'.1 = g := by
    simp only at hq2
    rw [hq2, hthr]
  have hbar : X.IsBarrier e' id cnt' pce := hX.isBarrier_of_arrival hK.out ⟨mode, hget⟩
  obtain ⟨e1, e2⟩ := e'
  simp only at hee
  subst hee
  exact ⟨e2, pce, cnt', hbar, hord'.symm.trans hord⟩

/-- The arrivals of ordinal below `start` are the whole block's, without a count. -/
theorem PhSources.early (hS : PhSources L X D cD start id) (hblk : L.block % 32 = 0) {N : Nat}
    (hN : N < start) : EarlySources L X none (Finset.range (warps L.block)) id N := by
  intro e pc cnt hb hg hle
  have hb0 := block_pos_of_thread_lt hg
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_range, warps]
    have := Nat.mod_lt e.1 hb0
    omega
  · rcases hS e pc cnt hb hg with h | ⟨-, -, h⟩
    · exact h
    · omega

end
end PTX.NamedBar

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [Fact K.NoBarArrive]

/-- The barrier event of ordinal `q` of a thread with more barrier events before position `f`. -/
theorem nth_bar {g f q id : Nat} (hlt : q + 1 ≤ ((X.tr g).take f).countP (Execution.isBarId id)) :
    ∃ j pc cnt md, j < f ∧ X.get (g, j) = some ⟨pc, .bar id cnt md⟩ ∧
      ((X.tr g).take j).countP (Execution.isBarId id) = q := by
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id) hlt
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (g, j) = some ev := by
    change (X.tr g)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    exact ⟨j, pcj, cntj, modej, hjf, hgetj, hcj⟩
  | _ => simp [Execution.isBarId] at hbj

/-- **The instances of a barrier with their own groups hand off from their participants to their
`bar.sync` participants** (the instances of `NamedBar.PhSources`): an event of `g` whose producer
use `q` (the barrier's events up to and including it) is at most `N` and below the consumer use of
an event of `h` of the same CTA happens before that event, when both threads are in instance `q`'s
group (`PhGroup`). -/
theorem Handoff.of_barPhased (hX : Consistent L K A mem0 X) {D : Finset Nat} {cD : Option Nat}
    {start id nD N : Nat} (hS : NamedBar.PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (CtaBarrier.warps L.block)) (hcard : D.card = nD)
    (hnD : nD ≠ CtaBarrier.warps L.block) (hcD : CtaBarrier.target L.block cD = .ok nD)
    (hblk : L.block % 32 = 0) (hid : id < 16)
    (hexit : ∀ g, g < L.threads → ∀ j pc, X.get (g, j) = some ⟨pc, .exit⟩ →
      N + 1 ≤ ((X.tr g).take j).countP (Execution.isBarId id))
    {g h e f : Nat} (hsame : SameCta L g h) (hf : f < (X.tr h).length)
    (hlt : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) <
      ((X.tr h).take f).countP (Execution.isBarId id))
    (hle : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) ≤ N)
    (hpg : (g % L.block) / 32 ∈
      NamedBar.PhGroup L D start (((X.tr g).take (e + 1)).countP (Execution.isBarId id)))
    (hph : (h % L.block) / 32 ∈
      NamedBar.PhGroup L D start (((X.tr g).take (e + 1)).countP (Execution.isBarId id))) :
    baseCausality L X (g, e) (h, f) := by
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hb0 := NamedBar.block_pos_of_thread_lt hgt
  by_cases hqs : q < start
  · -- an instance of the whole block
    have hn : 0 < CtaBarrier.warps L.block := by
      simp only [CtaBarrier.warps]; omega
    refine Handoff.of_barEarly hX hn rfl (Finset.card_range _) (fun w hw => ?_) hid
      (hS.early hblk (N := min N (start - 1)) (by omega))
      (fun g hg _ j pc hx => le_trans (by omega) (hexit g hg j pc hx)) hsame
      (by simp only [Finset.mem_range, CtaBarrier.warps]; have := Nat.mod_lt g hb0; omega)
      hf hlt (by omega)
    simp only [Finset.mem_range, CtaBarrier.warps] at hw
    omega
  · -- an instance of the group `D`
    simp only [NamedBar.PhGroup, hqs, ite_false] at hpg hph
    obtain ⟨j, pcj, cntj, mdj, hjf, hgetj, hcj⟩ :=
      nth_bar (X := X) (g := h) (q := q) (f := f) (id := id) (by omega)
    have hmd : mdj = .sync := by
      cases mdj with
      | sync => rfl
      | arrive => exact absurd hgetj (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
    subst hmd
    have hfb : X.IsBarrier (h, j) id cntj pcj := hgetj
    obtain ⟨i, pci, cnti, hbi, hci⟩ := NamedBar.D_member_arrival (f := (h, j)) hX hS hD hcard
      hnD hcD hfb (by dsimp only; omega) hph (show g / L.block = h / L.block from hsame.2.2) hpg
      (by
        rintro ⟨jx, pcx, hex⟩
        obtain ⟨i, pci, cnti, mdi, -, hgeti, hci⟩ :=
          nth_bar (X := X) (g := g) (q := q) (f := jx) (id := id)
          (by have := hexit g hgt jx pcx hex; omega)
        have hmi : mdi = .sync := by
          cases mdi with
          | sync => rfl
          | arrive => exact absurd hgeti (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
        subst hmi
        exact ⟨i, pci, cnti, hgeti, by dsimp only; omega⟩)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId id) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle'
      have h1 := Handoff.countP_take_succ_ge (P := Execution.isBarId id) (es := X.tr g) (e := e)
        hbi (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.D_same_ordinal_baseCausality hX hS hD hcard hnD hcD hsame hbi hfb
      (by omega) hpg hph (hiq.trans hcj.symm) hei hjf hf

end PTX.Frame
