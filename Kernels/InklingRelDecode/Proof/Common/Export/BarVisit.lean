-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.UbPrefix
public import Kernels.InklingRelDecode.Proof.Common.BarCount0
import Kernels.InklingRelDecode.Proof.Common.Export.TcForward
import Kernels.InklingRelDecode.Proof.Lib.BarZero

@[expose] public section

/-! # A lane never visits the optional rendezvous twice in a row

After the optional rendezvous (pc 2326) come the store, its wait and the mandatory rendezvous
(pc 999): the next barrier-0 event of the lane is not at pc 2326. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **Two visits of the optional rendezvous are not at consecutive barrier-0 ordinals.** -/
public theorem no_two_visits (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (nu : NoUbLane X g) {i1 i2 k1 k2}
    (g1 : X.get (g, i1) = some ⟨2326, k1⟩) (g2 : X.get (g, i2) = some ⟨2326, k2⟩)
    (lt : i1 < i2) (cnt : ((X.tr g).take i2).countP (Execution.isBarId 0) =
      ((X.tr g).take i1).countP (Execution.isBarId 0) + 1) : False := by
  have clean (j) (e) (h : X.get (g, j) = some e) : ∀ f, e.kind ≠ .ub f := nu.kind h
  obtain ⟨a1, a2, a3⟩ := after_visit hp hX hf g1 (clean i1 _ g1)
    (fun e h => clean _ e h) (fun e h => clean _ e h) (fun e h => clean _ e h)
  have bz : ∀ j e, X.get (g, j) = some e → (e.pc = 999 ∨ e.pc = 2326) →
      Execution.isBarId 0 e = true := by
    intro j e h pc
    rw [Lib.zero_event hX hp.block h (clean j e h)]
    rcases pc with pc | pc <;> rw [pc] <;> decide +kernel
  have back (a b : Nat) (hab : a ≤ b) (e) (h : X.get (g, b) = some e) :
      ∃ e', X.get (g, a) = some e' := by
    have h' : (X.tr g)[b]? = some e := h
    obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.mp h'
    exact ⟨_, List.getElem?_eq_getElem (show a < (X.tr g).length by omega)⟩
  have one : c0 X g (i1 + 1) = c0 X g i1 + 1 := by
    have := c0_succ (X := X) (g := g) (k := i1) (e := ⟨2326, k1⟩) g1
    rw [bz i1 _ g1 (.inr rfl)] at this
    simpa using this
  change c0 X g i2 = c0 X g i1 + 1 at cnt
  rcases Nat.lt_or_ge (i1 + 3) i2 with far | near
  · obtain ⟨e3, g3⟩ := back (i1 + 3) i2 (by omega) _ g2
    have s3 := c0_succ (X := X) (g := g) (k := i1 + 3) (e := e3) g3
    rw [bz _ e3 g3 (.inl (a3 e3 g3))] at s3
    have m1 := c0_mono (X := X) (g := g) (show i1 + 1 ≤ i1 + 3 by omega)
    have m2 := c0_mono (X := X) (g := g) (show i1 + 4 ≤ i2 by omega)
    have m3 : c0 X g (i1 + 4) = c0 X g (i1 + 3 + 1) := rfl
    simp only [ite_true] at s3
    omega
  · have : i2 = i1 + 1 ∨ i2 = i1 + 2 ∨ i2 = i1 + 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact absurd (a1 _ g2) (by simp)
    · exact absurd (a2 _ g2) (by simp)
    · exact absurd (a3 _ g2) (by simp)

end PTX.Kernels.InklingRelDecode.Proof.Export
