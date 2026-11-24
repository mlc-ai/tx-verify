-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Final
public import Lemmas.Protocol.PairTmaRing.Blocker

@[expose] public section

/-! # Who blocks a loader at an empty slot

A loader stopped at a failed poll of a slot's empty barrier that is not ready has one production
outstanding, and one of the two MMA consumers has delivered exactly as many notifications to that
barrier as its phase (`loader_blocker`, by `PairTmaRing.producer_blocker` for the slot's loader of
the CTA). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow MBarrier AsyncCopy

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem emptyLoc_eq_inputEmpty (L : Launch) (cta : Nat) (s : Fin 4) :
    emptyLoc L cta s = inputEmpty L cta s := by
  simp only [emptyLoc, inputEmpty, Bar.loc, Bar.off]
  congr 1
  omega

/-- A loader stopped at a failed poll of slot `s`'s empty barrier, with its own next poll's parity
`q` (`hparity`) that the barrier's phase does not make ready, is blocked by an MMA consumer whose
notifications to the barrier number its phase. -/
theorem slot_blocker (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads) {l : Loader.D} {s : Fin 4} {q : Nat}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
    {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩)
    (hm : m = emptyLoc L (g / L.block) s)
    (hparity : q % 2 = (okPolls (emptyLoc L (g / L.block) s) (X.tr g) + 1) % 2) {before : State}
    (hstate : stateBefore (X.objects (emptyLoc L (g / L.block) s))
      (X.objects (emptyLoc L (g / L.block) s)).length = some before)
    (hpar : before.phase % 2 = q % 2) :
    before.phase + 1 = okPolls (emptyLoc L (g / L.block) s) (X.tr g) ∧
    ∃ b' : Fin 2, (X.objects (emptyLoc L (g / L.block) s)).countP
      (notification L (g / L.block / 2) ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ b') =
        before.phase := by
  have hblock := hpre.block
  set cta := g / L.block
  set c := cta / 2
  let a : Fin 2 := ⟨cta % 2, Nat.mod_lt _ (by decide)⟩
  have hE : (slot L c s).empty a = emptyLoc L cta s := by
    rw [emptyLoc_bar]
    simp only [slot, a]
    congr 1
    omega
  have hprod : producerThread L c a g = true :=
    loader_producer ht (le_refl _) hg hσ rfl
  have hgl : X.get (g, (X.tr g).length - 1) = some ⟨pc, .wait m p false acq sc⟩ := by
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hN := producer_okPolls hpre hX ht hprod hgl (by rw [hm, hE])
  rw [← hE] at hstate hparity ⊢
  rw [hN] at hparity ⊢
  obtain ⟨hout, b', hb'⟩ := PairTmaRing.producer_blocker hX (hyp hpre hX ht c s) hstate
    (show before.phase % 2 = (okPolls ((slot L c s).empty a) (X.tr (producerOf L X c s a)) + 1) % 2
      by omega)
  refine ⟨hout, b', ?_⟩
  have hc : ∀ x ∈ X.objects ((slot L c s).empty a),
      notification L c a b' x = PairTmaRing.notifies (pslot L X c s) a b' x :=
    fun x hx => notification_iff hpre hX ht hx
  rw [List.countP_congr (fun x hx => by rw [hc x hx])]
  exact hb'

/-- A loader stopped at a failed poll of a slot's empty barrier whose phase is not ready for its
parity is blocked by an MMA consumer whose notifications to the barrier number its phase. -/
theorem loader_blocker (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads) {l : Loader.D} {b : Fin 8}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
    (hs : l.site = .wait b)
    {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩) {before : State}
    (hstate : stateBefore (X.objects (emptyLoc L (g / L.block) (slotOf b)))
      (X.objects (emptyLoc L (g / L.block) (slotOf b))).length = some before)
    (hpar : before.phase % 2 = producerParity b % 2) :
    before.phase + 1 = okPolls (emptyLoc L (g / L.block) (slotOf b)) (X.tr g) ∧
    ∃ b' : Fin 2, (X.objects (emptyLoc L (g / L.block) (slotOf b))).countP
      (notification L (g / L.block / 2) ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ b') =
        before.phase := by
  obtain ⟨hm, hparity⟩ := ht.loader_wait hg hσ hs hlast
  exact slot_blocker hpre hX ht hg hσ hlast hm hparity hstate hpar

/-- A loader stopped at a failed poll of its tail drain of slot `i` (parity 1) whose phase is not
ready for it is blocked by an MMA consumer whose notifications to the barrier number its phase. The
loader's polls of the slot are even in number there (`hev`). -/
theorem drain_blocker (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {g : Nat} (hg : g < L.threads) {l : Loader.D} {i : Fin 4}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.loader l))))
    (hs : l.site = .drain i)
    {pc : Nat} {m : Loc} {p : Nat} {acq : Bool} {sc : MbarScope}
    (hlast : (X.tr g).getLast? = some ⟨pc, .wait m p false acq sc⟩)
    (hm : m = emptyLoc L (g / L.block) i)
    {before : State}
    (hstate : stateBefore (X.objects (emptyLoc L (g / L.block) i))
      (X.objects (emptyLoc L (g / L.block) i)).length = some before)
    (hpar : before.phase % 2 = 1) :
    before.phase + 1 = okPolls (emptyLoc L (g / L.block) i) (X.tr g) ∧
    ∃ b' : Fin 2, (X.objects (emptyLoc L (g / L.block) i)).countP
      (notification L (g / L.block / 2) ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ b') =
        before.phase := by
  obtain ⟨hrk, -⟩ := ht.loader_rank hg hσ
  have hcount := ht.loader_site_count hg hσ
  rw [hs] at hcount
  simp only at hcount
  have hr : okPolls (emptyLoc L (g / L.block) i) (X.tr g) =
      (loaderCount L g (X.tr g) + 3 - i.val) / 4 := by
    rw [emptyLoc_eq_inputEmpty]
    exact hrk i
  have hi := i.isLt
  refine slot_blocker hpre hX ht hg hσ hlast hm (q := 1) ?_ hstate hpar
  rw [hr]
  omega

/-- **The input ring's blocked loader.** -/
theorem inputBlocked (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : InputBlocked L X :=
  fun _ _ _ _ _ _ _ _ _ hg hσ hs hlast hstate hpar =>
    loader_blocker hpre hX ht hg hσ hs hlast hstate hpar

/-- **The input ring's blocked draining loader.** -/
theorem drainBlocked (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : DrainBlocked L X :=
  fun _ _ _ _ _ _ _ _ _ hg hσ hs hlast hm hstate hpar =>
    drain_blocker hpre hX ht hg hσ hs hlast hm hstate hpar

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
