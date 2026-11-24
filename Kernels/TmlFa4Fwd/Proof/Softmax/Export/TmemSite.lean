-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemCol
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax Tensor Memory site on the trace: the counts of its place -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The counts of a score load's and a P store's place: the S-full polls `A`, the P-full arrivals
`B`, the P stores `C`. -/
def tabOk (lz : Bool) (inR : Nat → Bool) : Bool :=
  decide ((ptsOf lz (.acquire 80)).countP inR = 1) &&
    decide ((ptsOf lz (.arrive 96)).countP inR = 1) && decide ((ptsOf lz .tcst).countP inR = 4)

def ldOk (lz : Bool) (s : Site) : Bool :=
  decide ((ptsOf lz (.arrive 96)).countP (before s) + 1 =
      (ptsOf lz (.acquire 80)).countP (before s)) &&
    decide ((ptsOf lz .tcst).countP (before s) + 4 =
      4 * (ptsOf lz (.acquire 80)).countP (before s))

def stOk (lz : Bool) (s : Site) (q : Fin 4) : Bool :=
  decide ((ptsOf lz (.arrive 96)).countP (before s) + (if q.val < 3 then 1 else 0) =
      (ptsOf lz (.acquire 80)).countP (before s)) &&
    decide ((ptsOf lz .tcst).countP (before s) + 4 =
      4 * (ptsOf lz (.acquire 80)).countP (before s) + q.val)

theorem tab : [false, true].all (fun lz => tabOk lz inBias && tabOk lz inPlain &&
    allRd.all fun r => (List.finRange 4).all fun c =>
      ldOk lz (.sld r c) && stOk lz (.pst r c) c) = true := by
  decide +kernel

theorem tab_parr : [false, true].all (fun lz => allRd.all fun r =>
    decide ((ptsOf lz (.arrive 96)).countP (before (.parr r)) + 1 =
      (ptsOf lz (.acquire 80)).countP (before (.parr r)))) = true := by
  decide +kernel

/-- The trace counts of a softmax state on the pointed classes. -/
theorem count_at {k : Nat} {d : Control.D} {n : Cls → Nat} {c : Cnt} (hw : Prologue.warpIndex L g
    < 8)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hp : c.pointed = true) : ((X.tr g).take k).countP (Softmax.cls L g c) = n (.soft c) := by
  rw [← count hσ]
  congr 1
  funext e
  have hw' : g % L.block / 32 < 8 := hw
  simp [Proof.cls, hp, hw']

theorem bl_eq (hw : Prologue.warpIndex L g < 8) (o : Nat) :
    bl L g o = Tm.bar L (g / L.block) (o + 8 * (Prologue.warpIndex L g / 4)) := by
  have hw' : g % L.block / 32 < 8 := hw
  have h := colS_eq hw'
  have hst : stS L g = 8 * (g % L.block / 32 / 4) := by
    unfold colS at h
    unfold stS
    split <;> rename_i hs <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h <;> omega
  simp only [bl, Tm.bar, hst, Loc.mk.injEq, true_and]
  show _ = L.sharedBase + (o + 8 * (g % L.block / 32 / 4))
  omega

/-- The trace counts of a state, as the library's counts. -/
theorem tm_counts {k : Nat} {d : Control.D} {n : Cls → Nat} (hw : Prologue.warpIndex L g < 8)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n))) :
    Tm.sPolls L X g (Prologue.warpIndex L g / 4) k = n (.soft (.acquire 80)) ∧
      Tm.pArr L X g (Prologue.warpIndex L g / 4) k = n (.soft (.arrive 96)) ∧
      Tm.stN X g k = n (.soft .tcst) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← count_at hw hσ rfl]
    have hb := bl_eq hw 80
    show List.countP (okPoll (Tm.bar L (g / L.block) (80 + 8 * (Prologue.warpIndex L g / 4)))) _ = _
    rw [← hb]
    rfl
  · rw [← count_at hw hσ rfl]
    have hb := bl_eq hw 96
    show List.countP (arrivesOn (Tm.bar L (g / L.block) (96 + 8 * (Prologue.warpIndex L g / 4))))
      _ = _
    rw [← hb]
    rfl
  · rw [← count_at hw hσ rfl]
    rfl

theorem tab_at (lz : Bool) : tabOk lz inBias = true ∧ tabOk lz inPlain = true ∧
    ∀ r c, ldOk lz (.sld r c) = true ∧ stOk lz (.pst r c) c = true := by
  have h := List.all_eq_true.mp tab lz (by cases lz <;> simp)
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1.1, h.1.2, fun r c => h.2 r (by cases r <;> simp [allRd]) c (List.mem_finRange c)⟩

/-- **The counts at a score load and at a P store.** -/
theorem site_counts {d : D} {c : Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp) :
    (∀ r i, d.site = .sld r i → c (.arrive 96) + 1 = c (.acquire 80) ∧
      c .tcst + 4 = 4 * c (.acquire 80)) ∧
    ∀ r i, d.site = .pst r i → c (.arrive 96) + (if i.val < 3 then 1 else 0) = c (.acquire 80) ∧
      c .tcst + 4 = 4 * c (.acquire 80) + i.val := by
  obtain ⟨hB, hP, hT⟩ := tab_at (lz L g)
  simp only [tabOk, Bool.and_eq_true, decide_eq_true_eq] at hB hP
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  obtain ⟨⟨p1, p2⟩, p3⟩ := hP
  have e1 := hQ.cnt (.acquire 80) rfl
  have e2 := hQ.cnt (.arrive 96) rfl
  have e3 := hQ.cnt .tcst rfl
  unfold passed at e1 e2 e3
  rw [b1, p1] at e1
  rw [b2, p2] at e2
  rw [b3, p3] at e3
  refine ⟨fun r i hs => ?_, fun r i hs => ?_⟩ <;> rw [hs] at e1 e2 e3
  · have h := (hT r i).1
    simp only [ldOk, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · have h := (hT r i).2
    simp only [stOk, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

/-- **The counts at a P-full arrival.** -/
theorem parr_counts {d : D} {c : Cnt → Nat} {rb rp : Nat} (hQ : RefQ p L g d c rb rp) {r : Rd}
    (hs : d.site = .parr r) : c (.arrive 96) + 1 = c (.acquire 80) := by
  obtain ⟨hB, hP, -⟩ := tab_at (lz L g)
  simp only [tabOk, Bool.and_eq_true, decide_eq_true_eq] at hB hP
  obtain ⟨⟨b1, b2⟩, -⟩ := hB
  obtain ⟨⟨p1, p2⟩, -⟩ := hP
  have e1 := hQ.cnt (.acquire 80) rfl
  have e2 := hQ.cnt (.arrive 96) rfl
  unfold passed at e1 e2
  rw [b1, p1, hs] at e1
  rw [b2, p2, hs] at e2
  have h := List.all_eq_true.mp tab_parr (lz L g) (by cases lz L g <;> simp)
  have h2 := of_decide_eq_true (List.all_eq_true.mp h r (by cases r <;> simp [allRd]))
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
