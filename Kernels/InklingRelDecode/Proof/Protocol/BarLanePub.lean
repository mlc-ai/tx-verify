-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarOne
public import Kernels.InklingRelDecode.Proof.Interface.LedgerFacts

@[expose] public section

/-!
# Publication through the first generation of barrier 1

The barrier-1 half of the publication of the mbarrier initializations (`InitPub`, the development
notes,
"Protocol `Mbar`"): an event of a thread that has made no barrier-1 event (the prologue's
initialization is one) is base-causally before every event of another thread of the CTA that has
made at least one. The first generation of barrier 1 has all eight warps and no count, so the
library's single-group lemmas apply (`Bar.bar1_baseCausality`, `Bar.bar1_member`); the thread
layer's part is the count of barrier-1 events before an event, from the phases (`b1N`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event before a thread's first barrier-1 event is base-causally before every event that
follows a barrier-1 event of another thread of the CTA.** `e` is not itself a barrier-1 event and
has no barrier-1 event before it; `u` has at least one before it. -/
theorem pub_bar1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) {e u : EvId} {ev : Event} (hev : X.get e = some ev)
    (hnb : Execution.isBarId 1 ev = false) (hb0 : b1N X e.1 e.2 = 0)
    (hb1 : 1 ≤ b1N X u.1 u.2) (hcta : SameCta L e.1 u.1) (hu : u.2 < (X.tr u.1).length) :
    baseCausality L X e u := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  -- the user's first barrier-1 event
  have hlt : 0 < ((X.tr u.1).take u.2).countP (Execution.isBarId 1) := hb1
  obtain ⟨j, y, hj, hy, hjord⟩ := CtaBarrier.countP_index
    (xs := (X.tr u.1).take u.2) (p := Execution.isBarId 1) hlt
  have hju : j < u.2 := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hju] at hj
  obtain ⟨pcy, cy, my, rfl⟩ := NamedBar.isBarId_form hy
  have hyget : X.get (u.1, j) = some ⟨pcy, .bar 1 cy my⟩ := hj
  obtain ⟨hcy, hmy⟩ := bar_one_static hX hb hyget
  subst hcy hmy
  have hyb : X.IsBarrier (u.1, j) 1 none pcy := hyget
  rw [List.take_take, Nat.min_eq_left hju.le] at hjord
  have hjp : (u.1, j).2 + 1 < (X.tr (u.1, j).1).length := by
    show j + 1 < (X.tr u.1).length
    omega
  have hcta' : e.1 / L.block = (u.1, j).1 / L.block := hcta.2.2
  -- the event's thread has the same barrier-1 event
  obtain ⟨i, pci, hi, hiord⟩ := bar1_member hpre hX hyb hjp (g := e.1) hcta' (by
    rintro ⟨jx, pcx', hjx⟩
    have hex := ledger_exit hpre hX hS ht hR hjx
    have hlt' : 0 < ((X.tr e.1).take jx).countP (Execution.isBarId 1) := by
      have : 3 ≤ ((X.tr e.1).take jx).countP (Execution.isBarId 1) := hex
      omega
    obtain ⟨i, z, hi, hz, hiord⟩ := CtaBarrier.countP_index
      (xs := (X.tr e.1).take jx) (p := Execution.isBarId 1) hlt'
    have hijx : i < jx := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hijx] at hi
    obtain ⟨pcz, cz, mz, rfl⟩ := NamedBar.isBarId_form hz
    have hzget : X.get (e.1, i) = some ⟨pcz, .bar 1 cz mz⟩ := hi
    obtain ⟨hcz, hmz⟩ := bar_one_static hX hb hzget
    subst hcz hmz
    refine ⟨i, pcz, hzget, ?_⟩
    rw [List.take_take, Nat.min_eq_left hijx.le] at hiord
    simp only
    omega)
  -- the event is before it
  have hei : e.2 < i := by
    by_contra hge
    have hne : i ≠ e.2 := by
      intro h
      rw [h] at hi
      have h1 : X.get (e.1, e.2) = some ev := hev
      have h2 : X.get (e.1, e.2) = some ⟨pci, .bar 1 none .sync⟩ := hi
      have h3 : ev = ⟨pci, .bar 1 none .sync⟩ := by
        rw [h2] at h1
        exact (Option.some.inj h1).symm
      rw [h3] at hnb
      simp [Execution.isBarId] at hnb
    have hsucc : ((X.tr e.1).take (i + 1)).countP (Execution.isBarId 1) =
        ((X.tr e.1).take i).countP (Execution.isBarId 1) + 1 := by
      rw [countP_take_succ (Execution.isBarId 1) (l := X.tr e.1)
        (show (X.tr e.1)[i]? = some ⟨pci, .bar 1 none .sync⟩ from hi)]
      simp [Execution.isBarId]
    have hmono : ((X.tr e.1).take (i + 1)).countP (Execution.isBarId 1) ≤
        ((X.tr e.1).take e.2).countP (Execution.isBarId 1) :=
      (List.take_sublist_take_left (by omega : i + 1 ≤ e.2)).countP_le
    have hb0' : ((X.tr e.1).take e.2).countP (Execution.isBarId 1) = 0 := hb0
    omega
  exact bar1_baseCausality hpre hX (g := e.1) (h := u.1) (i := i) (j := j) (before := e.2)
    (after := u.2) hcta hi hyb (by omega) (by simp only at hiord ⊢; omega) hei hju hu

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
