-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PlaceWalk
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd

@[expose] public section

/-! # One LSE store per lane

A lane of warpgroup 0 makes its LSE store (pc 1178) once: the machine's place at the site `lse`
is fixed by the launch's length words, and grows strictly along the lane at an event that counts
(`place_lt`), so two events at pc 1178 of one lane are one event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **The state at the LSE store**: site `lse`, the launch's length words. -/
private theorem lse_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) {i : Nat} {a : Acc}
    {bs : List Byte} (h : X.get (y, i) = some ⟨1178, .wr a bs⟩) :
    ∃ (d : Wg0.Control.D) (n : Cls → Nat),
      Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d⟩, n)) ∧
      d.site = .lse ∧ d.l0 = lenWA P L (y / L.block) ∧ d.l1 = lenWB P L (y / L.block) := by
  have hy : y < L.threads := Frame.lt_of_get hX h
  have hub : ∀ f, (⟨1178, .wr a bs⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw h hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc
    ⟨by show 103 ≤ 1178; omega, by show 1178 < 1842; omega⟩
  have hpc' : 1178 = d.site.pc := hpc
  have hsite : d.site = .lse := Wg0.Data.site_pc_1178 hpc'.symm
  have hL := w0_bst hFw hnu hw hy hσ
  rcases hL with ⟨d0, n0, h0, -⟩ | ⟨d0, n0, h0, -, hL, -⟩
  · simp at h0
  · simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h0
    obtain ⟨rfl, -⟩ := h0
    obtain ⟨-, -, h1, h2⟩ := hL
    have hn : 2 ≤ d.site.lens := by rw [hsite]; simp [Wg0.Site.lens]
    exact ⟨d, n, hσ, hsite, h1 (by omega), h2 hn⟩

/-- **A lane's LSE store is one event**: two events of a lane at pc 1178 are the same event. -/
theorem w0_lse_once (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hw : warp L y < 4) {i i' : Nat} {a a' : Acc}
    {bs bs' : List Byte} (h : X.get (y, i) = some ⟨1178, .wr a bs⟩)
    (h' : X.get (y, i') = some ⟨1178, .wr a' bs'⟩) : i = i' := by
  have hy : y < L.threads := Frame.lt_of_get hX h
  obtain ⟨d, n, hσ, hs, hl0, hl1⟩ := lse_state hp hX hFw hnu hw h
  obtain ⟨d', n', hσ', hs', hl0', hl1'⟩ := lse_state hp hX hFw hnu hw h'
  have hpl : Wg0.place d = Wg0.place d' := by
    simp only [Wg0.place, hs, hs', Wg0.regPlace, Wg0.Site.reg, Wg0.elOff, hl0, hl0', hl1, hl1']
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · have := place_lt hFw hw hy (noUbBefore_of_get hX h') h (by simp [Event.counts]) hlt hσ hσ'
    omega
  · exact heq
  · have := place_lt hFw hw hy (noUbBefore_of_get hX h) h' (by simp [Event.counts]) hgt hσ' hσ
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
