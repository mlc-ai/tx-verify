-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotOrder
public import Kernels.FlashAttn4Fwd.Proof.Protocol.QRingSlotBox
public import Lemmas.Protocol.PairTmaRing.CopyExists
public import Lemmas.Order.Order

@[expose] public section

/-! # The bytes an MMA reads from a ring slot

An MMA read of a byte of a Q or KV slot's region in CTA `cta`, in use `r` of the slot (its
thread's earlier commits to the slot, `readUse`), reads the write of the copy of use `r` by the
loader of `cta` (`read_source`):

* **The copy exists.** The MMA lane's successful full poll for use `r` observed every copy of
  use `r` (`PairTmaRing.copy_exists`); the byte lies in box `j` of the region at element
  `(x, y)`, byte `z` (`region_box`), and copy `j` of use `r` is the copy with `copies · r + j`
  earlier ones. Its map and coordinates are `copySpec` of its count (`RingCopies.copy`): the Q
  half of the use's item, or the K or V block of the use's item and block (`useItem`,
  `useBlock`).
* **It precedes the read** (`bytes_ordered`, its use is the read's).
* **Every other write of the byte is ordered** around them: it is a copy of the same loader
  (`RingFacts.only_copies`, `RingFacts.write`); of an earlier use it precedes the copy
  (`copies_ordered`), of a later one it follows the read (`bytes_ordered`), and in the same use
  it is the same copy writing the same element (its box and element are those of the byte,
  `copy_box`, `TensorCopy.box_offset_inj`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

namespace Rings

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two threads of the pair of a ring byte's CTA access it as a `cta_group::2` pair. -/
theorem pairAsync_ring (hpre : Pre P L mem0) {b : FBar} {cta g1 g2 : Nat} {l : Loc}
    (hl : InRegion L cta b l) (hg1 : g1 < L.threads) (hg2 : g2 < L.threads)
    (hc1 : ctaOf L g1 / 2 = cta / 2) (hc2 : ctaOf L g2 / 2 = cta / 2) : PairAsync L l g1 g2 := by
  have hgr := hpre.grid
  have hcg1 := cta_lt hg1
  have hcg2 := cta_lt hg2
  have hsc : ∀ {u v : Nat}, u < L.grid → v < L.grid → u / 2 = v / 2 →
      SameCtaGroup L .two u v := by
    intro u v hu hv huv
    rw [sameCtaGroup_iff]
    refine ⟨⟨hu, hv, ?_⟩, ?_⟩
    · simp [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster, huv]
    · simp only [Launch.oneDim_rankOfCta hpre.oneDimLaunch.1, hpre.cluster, CtaGroup.size]
      omega
  have hlc : l.cta < L.grid := by rw [hl.2.1]; omega
  exact ⟨hl.1, hsc hcg1 hcg2 (by simp only [ctaOf] at hc1 hc2; omega),
    hsc hcg1 hlc (by rw [hl.2.1]; simp only [ctaOf] at hc1; omega)⟩

/-- The written element of a copy covering a ring byte: its slot and the byte's box. -/
theorem copy_elem (hcp : RingCopies P L X) (ht : RingFacts L X)
    (hX : Consistent L kernel asms mem0 X) {b : FBar} (hb : b.isFull) {cta g k x y z : Nat}
    {l : Loc} (hl : InRegion L cta b l) (hw : AsyncCovers X (g, k) (.write (.load x y z)) l) :
    ∃ pc al, X.get (g, k) = some ⟨pc, .tensorIssue al
        (copySpec P L g b (((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2))))))⟩ ∧
      ctaOf L g = cta ∧
      TensorCopy.writeLoc (copySpec P L g b
        (((X.tr g).take k).countP (issuesTo (b.loc L (2 * (cta / 2)))))) x y z = some l := by
  obtain ⟨pc, al, sp, he, hm, hc⟩ := write_slot ht hb hl hw
  have hsp := hcp.copy (Frame.lt_of_get hX he) he hm hb
  obtain ⟨acc, wf, ⟨-, s, addr, ⟨pc2, hTI⟩, hwl, hsz⟩, hcov⟩ := hw
  rw [he] at hTI
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hTI
  obtain ⟨-, -, rfl⟩ := hTI
  rw [covers_one hcov hsz, hsp] at hwl
  rw [hsp] at he
  exact ⟨pc, al, he, hc, hwl⟩

/-- Two boxes of one region meeting at one byte are one box at one offset. -/
theorem box_eq {b : FBar} (hb : b.isFull) {j j' o o' : Nat} (hj : j < b.copies)
    (hj' : j' < b.copies) (ho : o < b.copyBytes) (ho' : o' < b.copyBytes)
    (h : boxBase L b j + o = boxBase L b j' + o') : j = j' ∧ o = o' := by
  have hc : b.copies ≤ 2 := by
    cases b <;> simp_all [FBar.isFull, FBar.copies]
    split_ifs <;> omega
  simp only [boxBase] at h
  have hj2 : j = 0 ∨ j = 1 := by omega
  have hj2' : j' = 0 ∨ j' = 1 := by omega
  rcases hj2 with rfl | rfl <;> rcases hj2' with rfl | rfl <;> simp at h ⊢ <;> omega

/-- **The source of a ring byte an MMA reads.** An MMA read of a byte of slot `b`'s region in
CTA `cta` reads the write of element `(x, y)`, byte `z`, of the copy of its use by `cta`'s
loader: the copy's map and coordinates are `copySpec` of its count, and every other write of
the byte is ordered before that write or after the read. -/
theorem read_source (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (hinit : RingInit L X)
    (hcp : RingCopies P L X) {b : FBar} (hb : b.isFull) {cta gm km idx : Nat} {isB : Bool}
    {l : Loc} (hl : InRegion L cta b l) (hr : AsyncCovers X (gm, km) (.mmaRead isB idx) l) :
    ∃ gl kl pc al x y z,
      X.get (gl, kl) = some ⟨pc, .tensorIssue al
        (copySpec P L gl b (((X.tr gl).take kl).countP (issuesTo (b.loc L (2 * (cta / 2))))))⟩ ∧
      ctaOf L gl = cta ∧ copyUse L X (cta / 2) b (gl, kl) = readUse L X (cta / 2) b (gm, km) ∧
      TensorCopy.writeLoc (copySpec P L gl b
        (((X.tr gl).take kl).countP (issuesTo (b.loc L (2 * (cta / 2)))))) x y z = some l ∧
      modelCausality L X l (.async (gl, kl) (.write (.load x y z)))
          (.async (gm, km) (.mmaRead isB idx)) ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers l →
        w = .async (gl, kl) (.write (.load x y z)) ∨
          modelCausality L X l w (.async (gl, kl) (.write (.load x y z))) ∨
          modelCausality L X l (.async (gm, km) (.mmaRead isB idx)) w := by
  have H := hyp hpre hX ht htm hinit hb (cta / 2)
  set S := slot L X (cta / 2) b with hS
  obtain ⟨hT, hgm, hpol⟩ := read_slot hX ht hb hl hr
  set r := readUse L X (cta / 2) b (gm, km) with hrdef
  have hr' : r < okPolls S.full (X.tr (S.cons 0)) := by
    have := PairTmaRing.okPolls_take_le S.full (X.tr (S.cons 0)) km
    rw [← hgm]
    exact lt_of_lt_of_le (by exact hpol) (by rw [hgm]; exact this)
  obtain ⟨j, x, y, z, hj, hx, hy, hz, hleq⟩ := region_box hb hl
  set a : Fin 2 := ⟨cta % 2, Nat.mod_lt _ (by decide)⟩ with ha
  obtain ⟨kl, pc, al, sp, he, hm, hcnt⟩ := PairTmaRing.copy_exists hX H (b := 0) hr' a
    (j := j) hj
  have hgl := Frame.lt_of_get hX he
  have hcl : ctaOf L (S.prod a) = cta := by rw [ctaOf_lead hpre a]; simp only [ha]; omega
  have hsp := hcp.copy hgl he hm hb
  have hcnt' : ((X.tr (S.prod a)).take kl).countP (issuesTo (b.loc L (2 * (cta / 2)))) =
      b.copies * r + j := hcnt
  have hmod : (b.copies * r + j) % b.copies = j := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
  have hdiv : (b.copies * r + j) / b.copies = r := by
    have := copies_pos hb
    rw [Nat.mul_add_div this, Nat.div_eq_of_lt hj]; rfl
  have hwl : TensorCopy.writeLoc (copySpec P L (S.prod a) b (b.copies * r + j)) x y z = some l := by
    rw [copy_writeLoc hb _ hx hy hz, hmod, hleq, hcl]
  rw [hcnt'] at hsp
  rw [hsp] at he
  have hcw : AsyncCovers X (S.prod a, kl) (.write (.load x y z)) l :=
    ⟨{ loc := l, size := 1 }, true, ⟨rfl, _, al, ⟨pc, he⟩, hwl, rfl⟩,
      ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩
  have huse : copyUse L X (cta / 2) b (S.prod a, kl) = r := by
    simp only [copyUse]
    rw [show 2 * (cta / 2) = 2 * (cta / 2) from rfl]
    exact hcnt'.symm ▸ hdiv
  have hgm' : gm < L.threads := lt_of_pairTc hX hT
  have hcm : ctaOf L gm = 2 * (cta / 2) := by rw [hgm]; exact ctaOf_cons hpre 0
  obtain ⟨hWR, -⟩ := bytes_ordered hpre hX ht htm hinit hb hl hcw hr
  refine ⟨S.prod a, kl, pc, al, x, y, z, by rw [hcnt']; exact he, hcl, huse,
    by rw [hcnt']; exact hwl,
    modelCausality_pair_direct
      (pairAsync_ring (g1 := S.prod a) (g2 := gm) hpre hl hgl hgm' (by omega) (by omega))
      (.inr hT) (hWR huse.le), ?_⟩
  intro w acc bs hwr hcov
  obtain ⟨i', x', y', z', rfl⟩ := ht.only_copies hwr hcov hb hl
  have hcw' : AsyncCovers X i' (.write (.load x' y' z')) l :=
    ⟨acc, true, Execution.MemWrites.intent hwr, hcov⟩
  obtain ⟨g', k'⟩ := i'
  obtain ⟨pc', al', he', hc', hwl'⟩ := copy_elem hcp ht hX hb hl hcw'
  obtain ⟨pc0, al0, sp0, he0, hm0, -⟩ := write_slot ht hb hl hcw'
  obtain ⟨a2, rfl, hca2, -, -⟩ := full_issue hX ht hb he0 hm0
  have ha2 : a2 = a := Fin.ext (by simp only [ha]; omega)
  subst ha2
  have hg' := Frame.lt_of_get hX he'
  rcases Nat.lt_trichotomy (copyUse L X (cta / 2) b (S.prod a, k')) r with hlt | heq | hgt
  · obtain ⟨-, hch⟩ := copies_ordered hpre hX ht htm hinit hb hl hcw' hcw (by rw [huse]; exact hlt)
    exact .inr (.inl ⟨.inl ⟨hg', hgl, rfl⟩, hch⟩)
  · -- The same use: the same copy and element.
    set cnt' := ((X.tr (S.prod a)).take k').countP (issuesTo (b.loc L (2 * (cta / 2))))
      with hcnt'd
    obtain ⟨hx', hy', hz', hl'⟩ := copy_box hb hwl'
    rw [hc'] at hl'
    have hl0 : l = ⟨.shared, cta, boxBase L b j +
        TensorSwizzle.offset .b128 (boxBase L b j) (128 * y + 2 * x + z)⟩ := hleq
    rw [hl0] at hl'
    simp only [Loc.mk.injEq, true_and] at hl'
    obtain ⟨hjj, hoo⟩ := box_eq hb hj (Nat.mod_lt _ (copies_pos hb))
      (box_offset_lt' hb _ hx hy hz) (box_offset_lt' hb _ hx' hy' hz') hl'
    rw [← hjj] at hoo
    obtain ⟨rfl, rfl, rfl⟩ := TensorCopy.box_offset_inj (base := boxBase L b j) hx hz hx' hz' hoo
    have hu' : cnt' / b.copies = r := heq
    have hcc : cnt' = b.copies * r + j := by
      have := Nat.div_add_mod cnt' b.copies
      rw [hu', ← hjj] at this
      omega
    have hmb : ∀ c, (copySpec P L (S.prod a) b c).mbar = b.loc L (2 * (cta / 2)) := by
      intro c; simp only [copySpec, pairBase, hcl]
    have hkk : k' = kl := PairTmaRing.issue_index_unique he' (hmb _) he (hmb _) (by
      rw [← hcnt'd, hcc, hcnt'])
    subst hkk
    exact .inl rfl
  · have hrc : readUse L X (cta / 2) b (gm, km) < copyUse L X (cta / 2) b (S.prod a, k') := hgt
    obtain ⟨-, hRW⟩ := bytes_ordered hpre hX ht htm hinit hb hl hcw' hr
    exact .inr (.inr (modelCausality_pair_direct
      (pairAsync_ring (g1 := gm) (g2 := S.prod a) hpre hl hgm' hg' (by omega) (by omega))
      (.inl hT) (hRW hrc)))

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
