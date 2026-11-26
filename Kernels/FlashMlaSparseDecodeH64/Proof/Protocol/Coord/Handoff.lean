-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Coord.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ring

@[expose] public section

/-! # The index ring's handoffs

Slot `s` of the index ring of CTA `c` as two unit handoffs (`Protocol/Shared/Ring.lean`), from
the observation lemmas of `Protocol/Coord/Observe.lean`: the index lanes to the consumers on
`coordReady s` (offset 0, `coordReady_handoff`), the consumers to the index lanes on
`coordFree s` (offset 1, `coordFree_handoff`). Producers and consumers are taken among the
launch's threads, so they are threads of CTA `c`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The index lanes of CTA `c` among the launch's threads. -/
def IdxOf (L : Launch) (c g : Nat) : Prop := g < L.threads ∧ ∃ a, g = idxLane L c a

/-- The consumers of the index ring of CTA `c` among the launch's threads. -/
def ConsOf (L : Launch) (X : Execution) (c h : Nat) : Prop :=
  h < L.threads ∧ ∃ b, h = coordCons L X c b

/-- A consumer of the index ring of CTA `c` is a thread of CTA `c`. -/
theorem coordCons_cta (hp : Pre P L m) (c : Nat) (b : Fin 129) :
    coordCons L X c b / L.block = c := by
  have ht := tmaThread_mod (X := X) hp c
  have hb := b.isLt
  simp only [coordCons, hp.block]
  split <;> omega

/-- The index lanes and the consumers of one CTA are threads of one CTA. -/
theorem idx_cons_cta (hp : Pre P L m) {c g h : Nat} (hg : IdxOf L c g) (hh : ConsOf L X c h) :
    SameCta L g h := by
  obtain ⟨hgl, a, rfl⟩ := hg
  obtain ⟨hhl, b, rfl⟩ := hh
  have ha := a.isLt
  have hc : idxLane L c a / L.block = c := by simp only [idxLane, hp.block]; omega
  exact ⟨hgl, hhl, by rw [hc, coordCons_cta hp c b]⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **The full handoff of the index ring**: a consumer's successful poll of `coordReady s` with
`q` earlier ones synchronizes with every index lane's arrival of use `q`. -/
theorem coordReady_handoff (c : Nat) (s : Fin 4) :
    UnitHandoff L X (mbarLoc L c (.coordReady s)) (IdxOf L c) (ConsOf L X c) 0 :=
  handoff_of_observes hX hR (fun _ _ hg hh => idx_cons_cta hp hg hh) fun _ he hq g hg => by
    obtain ⟨-, a, rfl⟩ := hg
    obtain ⟨-, hall⟩ := coordReady_observes hp hX hFw hR hI hB hN he
    obtain ⟨i, pc', sc', ha, hi, hob⟩ := hall a
    exact ⟨i, pc', sc', ha, hi.trans hq, hob⟩

/-- **The empty handoff of the index ring**: an index lane's successful poll of `coordFree s`
with `q + 1` earlier ones synchronizes with every consumer's arrival of use `q`. -/
theorem coordFree_handoff (c : Nat) (s : Fin 4) :
    UnitHandoff L X (mbarLoc L c (.coordFree s)) (ConsOf L X c) (IdxOf L c) 1 :=
  handoff_of_observes hX hR (fun _ _ hg hh => by
    obtain ⟨h1, h2, h3⟩ := idx_cons_cta hp hh hg
    exact ⟨h2, h1, h3.symm⟩) fun _ he hq g hg => by
    obtain ⟨-, b, rfl⟩ := hg
    obtain ⟨-, hall⟩ := coordFree_observes hp hX hFw hR hI hB hN he hq
    exact hall b

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
