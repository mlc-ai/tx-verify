-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.ShFrame
public import Lemmas.Protocol.RegionOrder
import Kernels.TmlFa4Fwd.Proof.Mma.Export.MemAlloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Lemmas.Tmem.AllocResultDependency

@[expose] public section

/-! # The allocation word is ordered

The word at `sb + 312` is written once per CTA, by lane 0 of warp 12 after its allocation, and read
by the lanes of the warp after theirs: Core's allocation-result order (`alloc_word_order`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of a CTA's allocation word. -/
def InAlloc (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 312 ≤ l.addr ∧ l.addr < L.sharedBase + 316

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- The stores of one CTA's allocation word are one. -/
theorem alloc_wr_unique {g h i j pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte}
    (hw : Prologue.warpIndex L g = 12) (hw' : Prologue.warpIndex L h = 12)
    (hc : g / L.block = h / L.block) (he : X.get (g, i) = some ⟨pc, .wr a bs⟩)
    (he' : X.get (h, j) = some ⟨pc', .wr a' bs'⟩) : g = h ∧ i = j := by
  obtain ⟨hl, k, rfl, hk⟩ := mma_alloc_wr hp hX hFw hw he
  obtain ⟨hl', k', rfl, hk'⟩ := mma_alloc_wr hp hX hFw hw' he'
  have hg := Frame.lt_of_get hX he
  have hh := Frame.lt_of_get hX he'
  obtain rfl : g = h := Tmem.Pair.sameWarp_leader_eq ⟨⟨hg, hh, hc⟩, hw.trans hw'.symm⟩ hl hl'
  have ht := tmem1Ops hp hX hFw
  have h0 := (alloc_ops0 ht hg hk.1).1
  have h0' := (alloc_ops0 ht hg hk'.1).1
  exact ⟨rfl, by rw [res_unique hk.1 hk'.1 rfl rfl (by rw [h0, h0'])]⟩

/-- The store is before every read of its CTA. -/
theorem alloc_wr_rd {g h i j pc pc' : Nat} {a a' : Acc} {bs : List Byte} {bs' : List (Option Byte)}
    (hw : Prologue.warpIndex L h = 12) (hw' : Prologue.warpIndex L g = 12)
    (hc : h / L.block = g / L.block) (he : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (he' : X.get (g, j) = some ⟨pc', .rd a' bs'⟩) {l : Loc} (ha : AllocAcc L g a')
    (hl : a'.Covers l) : modelCausality L X l (.thread (h, i)) (.thread (g, j)) := by
  obtain ⟨k', hk', hall, hst⟩ := mma_alloc_rd hp hX hFw hw' he'
  have hg := Frame.lt_of_get hX he'
  obtain ⟨w, dst, hAR⟩ := alloc_writer hX hg hall hst hk' (List.getElem?_eq_some_iff.mp he').1
  have hAR' := hAR
  obtain ⟨⟨⟨hw1, -, hcw⟩, hww⟩, hl0, -, -, j0, site, grp, nn, kk, bytes, hw2, hget0, hgetr, -, -,
    hgetw⟩ := hAR'
  rw [hall.1] at hgetr
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq,
    Tmem.Request.alloc.injEq] at hgetr
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hgetr
  obtain ⟨w1, w2⟩ := w
  simp only at hw2 hw1 hcw hww hl0 hget0
  obtain ⟨rfl, rfl⟩ := alloc_wr_unique hp hX hFw hw (hww.trans hw') (hc.trans hcw.symm) he hgetw
  refine modelCausality.of_allocResultBefore L ⟨k', _, a', _, hAR, hk', ?_, ⟨pc', he'⟩, hl⟩
  obtain ⟨hz, hloc⟩ := ha
  rw [Acc.Covers, hloc, hz] at hl
  exact hl

/-- **The allocation words are ordered.** -/
theorem alloc_ordered : ConflictsOrdered L X (InAlloc L) := by
  intro e f a b l hcon ha hb hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have hsa : a.loc.space = .shared := ha.1.symm.trans hl.1
  have hsb : b.loc.space = .shared := hb.1.symm.trans hl.1
  have key : ∀ {r : Ref} {c : Acc} {w : Bool}, X.Intent r c w → c.loc.space = .shared →
      c.Covers l → (∃ g k pc bs, r = .thread (g, k) ∧ Prologue.warpIndex L g = 12 ∧
        AllocAcc L g c ∧ w = true ∧ X.get (g, k) = some ⟨pc, .wr c bs⟩) ∨
      ∃ g k pc bs, r = .thread (g, k) ∧ Prologue.warpIndex L g = 12 ∧ AllocAcc L g c ∧
        w = false ∧ X.get (g, k) = some ⟨pc, .rd c bs⟩ := by
    intro r c w hi hs hc
    obtain ⟨g, k, rfl, hw, h⟩ | hge := (sh_intent hp hX hFw hi hs).low
    swap
    · have h1 := hc.2.2.1
      have h2 := hl.2.2
      omega
    rcases hi with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
    · exact .inr ⟨_, _, pc, bs, rfl, hw, h, rfl, he⟩
    · exact .inl ⟨_, _, pc, bs, rfl, hw, h, rfl, he⟩
    · exact (no_rmw hX he).elim
  have hcta : ∀ {g : Nat} {c : Acc}, AllocAcc L g c → c.Covers l → l.cta = g / L.block :=
    fun h hc => by rw [hc.2.1, h.2]
  rcases key he hsa ha with ⟨g, k, pc, bs, rfl, hw1, h1, rfl, hg⟩ |
    ⟨g, k, pc, bs, rfl, hw1, h1, rfl, hg⟩ <;>
    rcases key hf hsb hb with ⟨g', k', pc', bs', rfl, hw2, h2, rfl, hg'⟩ |
      ⟨g', k', pc', bs', rfl, hw2, h2, rfl, hg'⟩
  · obtain ⟨rfl, rfl⟩ := alloc_wr_unique hp hX hFw hw1 hw2
      ((hcta h1 ha).symm.trans (hcta h2 hb)) hg hg'
    exact (hne rfl).elim
  · exact .inl (alloc_wr_rd hp hX hFw hw1 hw2 ((hcta h1 ha).symm.trans (hcta h2 hb)) hg hg' h2 hb)
  · exact .inr (alloc_wr_rd hp hX hFw hw2 hw1 ((hcta h2 hb).symm.trans (hcta h1 ha)) hg' hg h1 ha)
  · rcases hw with h | h <;> cases h

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
