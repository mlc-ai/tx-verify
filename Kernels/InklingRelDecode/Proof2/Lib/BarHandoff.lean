-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Handoff

@[expose] public section

/-!
# A named barrier's hand-off at every instance, from its exits

Generic, for promotion next to `Handoff.of_bar_upTo` (request L-p). `of_bar_upTo` asks of the
barrier's schedule only that an exiting participant arrived `n` times, for the first `n`
instances. `of_bar_exits` asks instead, per passed `bar.sync`, that every exiting participant of
its CTA made the arrival of its ordinal (`hexits`), and gives the hand-off at every instance. A
kernel proves `hexits` from the dependency order (an exit that is a witness of a barrier's
return closes a cycle through the thread's last CTA barrier), without knowing the roles first.
-/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

namespace Handoff

/-- **A named barrier is a hand-off at every instance** when every exiting participant made the
arrivals its CTA passed. -/
theorem of_bar_exits (hX : Consistent L K A mem0 X) {count : Option Nat} {p : Finset Nat}
    {id : Nat} (hS : NamedBar.Sources L X count p id) (hG : NamedBar.Shape L count p id)
    {syncs : Nat → Prop}
    (hsync : ∀ h j pc cnt mode, syncs h → X.get (h, j) = some ⟨pc, .bar id cnt mode⟩ →
      mode = .sync)
    (hexits : ∀ (f : EvId) pc cnt g, X.IsBarrier f id cnt pc → f.2 + 1 < (X.tr f.1).length →
      g / L.block = f.1 / L.block → (g % L.block) / 32 ∈ p →
      (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) → ∃ i pc' m,
        X.get (g, i) = some ⟨pc', .bar id count m⟩ ∧
        ((X.tr g).take i).countP (Execution.isBarId id) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    Handoff L X (fun g h => SameCta L g h ∧ (g % L.block) / 32 ∈ p ∧ syncs h)
      (fun i => ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId id))
      (fun i => ((X.tr i.1).take i.2).countP (Execution.isBarId id)) := by
  rintro g h e f ⟨hsame, hpg, hsh⟩ hf hlt
  simp only at hlt
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hht : h < L.threads := hsame.2.1
  -- the consumer's barrier of ordinal `q`
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id)
    (show q + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId id) by omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    have hmj := hsync h j pcj cntj modej hsh hgetj
    subst hmj
    have hfb : X.IsBarrier (h, j) idj cntj pcj := hgetj
    have hph : (h % L.block) / 32 ∈ p := (hS.sync hfb hht).1
    -- the producer's arrival of the same ordinal
    obtain ⟨i, pci, mi, hbi, hci⟩ := hS.member_arrival_any hX hG hfb (by simp only; omega)
      (show g / L.block = h / L.block from hsame.2.2) hpg
      (hexits (h, j) pcj cntj g hfb (by simp only; omega) hsame.2.2 hpg)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId idj) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle
      have h1 := countP_take_succ_ge (P := Execution.isBarId idj) (es := X.tr g) (e := e) hbi
        (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.Sources.arrive_sync_baseCausality hX hS hG hsame hbi hfb (by omega)
      (by omega) hei hjf hf
  | _ => simp [Execution.isBarId] at hbj

end Handoff

end PTX.Frame
