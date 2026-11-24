-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.MmShfl
public import Lemmas.Protocol.SingleTmaRing.Ordered

@[expose] public section

/-! # The KV ring's asynchronous accesses: a copy and a read

A byte of the rings `[sharedBase, sharedBase + 196608)` is accessed asynchronously by the tensor
copies' write stages and the MMAs' B operand reads (`async_shared`). Both name the slot of the
byte (`InSlot`): a copy on `kv_ready s` writes in slot `s` (`copy_ring_ev`), a QK MMA of iteration
`i` reads the K tile of slot `i % 3`, a PV MMA the V tile of slot `(i - 1) % 3` (`mma_b_slot`).

* `mma_read_info`: an MMA read of a ring byte is the MMA lane's (`leadT … 7`, the elected lane
  of warp 7), a tensor-core issue, and its successful polls of the slot's `kv_ready` exceed its
  commits to the slot's `kv_empty` (`MmCnt`);
* `copy_read_ordered`: a copy's write and an MMA read of one byte are ordered, by
  `SingleTmaRing.copy_read_order` on the byte's slot of the declared ring (`kv_hyp`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame AsyncCopy

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The footprint of a tensor copy's write stage at a byte. -/
theorem copy_write_at {i : EvId} {x y z : Nat} {l : Loc}
    (h : AsyncCovers X i (.write (.load x y z)) l) :
    ∃ pc a sp, X.get i = some ⟨pc, .tensorIssue a sp⟩ ∧
      TensorCopy.writeLoc sp x y z = some l := by
  obtain ⟨ac, w, ⟨-, sp, a, ⟨pc, he⟩, hloc, hsz⟩, hc⟩ := h
  obtain ⟨hs, hc2, hlo, hhi⟩ := hc
  rw [hsz] at hhi
  have hl : l = ac.loc := by
    rcases l with ⟨s1, c1, a1⟩
    rcases hac : ac.loc with ⟨s2, c2, a2⟩
    rw [hac] at hs hc2 hlo hhi
    simp only at hs hc2 hlo hhi ⊢
    simp only [Loc.mk.injEq]
    exact ⟨hs, hc2, by omega⟩
  exact ⟨pc, a, sp, he, hl ▸ hloc⟩

/-- The footprint of an MMA operand read at a byte. -/
theorem mma_read_at (hX : Consistent L kernel Assumptions.all m X) {mi : EvId} {isB : Bool}
    {idx : Nat} {l : Loc} (h : AsyncCovers X mi (.mmaRead isB idx) l) :
    ∃ pc c spec acc mask, X.get mi = some ⟨pc, .tc (.mma c spec acc mask)⟩ ∧
      spec.byteLoc (if isB then .b else .a) idx = some l := by
  obtain ⟨ac, w, ⟨-, hsz, hmf⟩, hc⟩ := h
  rcases hmf with ⟨d, spec, acc, mask, ⟨pc, he⟩, hb⟩ | ⟨c, k, cta, hcp, -⟩
  · obtain ⟨hs, hc2, hlo, hhi⟩ := hc
    rw [hsz] at hhi
    have hl : l = ac.loc := by
      rcases l with ⟨s1, c1, a1⟩
      rcases hac : ac.loc with ⟨s2, c2, a2⟩
      rw [hac] at hs hc2 hlo hhi
      simp only at hs hc2 hlo hhi ⊢
      simp only [Loc.mk.injEq]
      exact ⟨hs, hc2, by omega⟩
    exact ⟨pc, d, spec, acc, mask, he, hl ▸ hb⟩
  · exact absurd hcp (no_cp hX _ _)

theorem inSlot_unique {s s' a : Nat} (hs : s < 3) (hs' : s' < 3) (h : InSlot L s a)
    (h' : InSlot L s' a) : s = s' := by
  unfold InSlot at h h'
  omega

theorem cnt0_mono {i i' s : Nat} (h : i ≤ i') : cnt0 i s ≤ cnt0 i' s := by
  unfold cnt0; omega

/-- **An MMA read of a ring byte**: the MMA lane's, a tensor-core issue, in the byte's slot, after
more successful polls of the slot's `kv_ready` than commits to its `kv_empty`. -/
theorem mma_read_info (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {km : Nat} {isB : Bool} {idx : Nat} {l : Loc}
    (hcb : AsyncCovers X (g, km) (.mmaRead isB idx) l) (hsp : l.space = .shared)
    (hhi : l.addr < L.sharedBase + 196608) :
    ∃ s < 3, g < L.threads ∧ g = leadT L X (g / L.block) 7 ∧ l.cta = g / L.block ∧
      InSlot L s l.addr ∧ X.TcAsync (g, km) ∧
      ((X.tr g).take km).countP (commitsTo (Proof.EvW.kvEmpty L (g / L.block) s)) + 1 ≤
        okPolls (Proof.EvW.kvReady L (g / L.block) s) ((X.tr g).take km) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨ac, w, hI, hcv⟩ := hcb
  obtain ⟨hg, hcta, -, hcase⟩ := async_shared hp hX hI hcv hsp
  rcases hcase with ⟨isB', idx', hpart, -, hlen, ⟨tm, d, P, n, hσ⟩, hA, -⟩ | ⟨x, y, z, hpart, -⟩
  · simp only [AsyncCopy.Part.mmaRead.injEq] at hpart
    obtain ⟨rfl, rfl⟩ := hpart
    obtain ⟨pc, c, spec, acc, mask, he, hbl⟩ := mma_read_at hX ⟨ac, w, hI, hcv⟩
    have hisB : isB = true := by
      cases isB
      · have := hA rfl
        unfold PTX.Kernels.InklingRelDecode.Proof.Safety.InQ at this
        omega
      · rfl
    subst hisB
    simp only [ite_true] at hbl
    obtain ⟨σ, t, ins, o, hσ', hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
    rw [hσ] at hσ'
    obtain rfl := Option.some.inj (Option.some.inj hσ')
    cases o with
    | none => exact absurd (fires_none_ends hf) (by simp [Ends])
    | some u =>
    have hsh : Proof.EvW.MmShape L g d ⟨pc, .tc (.mma c spec acc mask)⟩ :=
      frag_ev hp hg hJ hat hi hc hf
    have hK : MmCnt L g d ((X.tr g).take km) := kc_inv hp hX hg km hlen _ hσ
    obtain ⟨-, hL, -⟩ := (sh_inv hp hX hg km hlen _ hσ : _ = 1 + mmSh d ∧ MmLoop d ∧ _)
    have hTc : X.TcAsync (g, km) := .inl ⟨c, spec, acc, mask, pc, he⟩
    have hlead : g = leadT L X (g / L.block) 7 := by
      have h7 : g % L.block / 32 = 7 := role_warp hp hX hg km hlen _ hσ
      have hel := mm_pv_elected hp hX hg km hlen.le _ hσ (by
        show isPvS d.site = true
        rcases Proof.Safety.mma_b_slot hp hsh with ⟨⟨j, hj⟩, -⟩ | ⟨⟨j, hj⟩, -⟩ <;> rw [hj] <;> rfl)
      have := leadT_eq hX hg hel
      rw [h7] at this
      exact this.symm
    rcases Proof.Safety.mma_b_slot hp hsh with ⟨⟨j, hj⟩, hB⟩ | ⟨⟨j, hj⟩, hB⟩
    · obtain ⟨-, -, h3, h4⟩ := hB idx l hbl
      have hm3 : d.i % 3 < 3 := Nat.mod_lt _ (by omega)
      have hin : iterS d.site = true := by rw [hj]; rfl
      have hF := hK.F hin _ hm3
      have hM := hK.M hin _ hm3
      simp only [qkDoneS, hj, true_and, ite_true, reduceCtorEq, false_and, ite_false,
        Nat.add_zero] at hF hM
      have := cnt0_mono (s := d.i % 3) (show d.i - 1 ≤ d.i by omega)
      exact ⟨d.i % 3, hm3, hg, hlead, hcta, .inl ⟨h3, h4⟩, hTc, by omega⟩
    · obtain ⟨-, -, h3, h4⟩ := hB idx l hbl
      have hm3 : (d.i - 1) % 3 < 3 := Nat.mod_lt _ (by omega)
      have hin : iterS d.site = true := by rw [hj]; rfl
      have hi1 : 1 ≤ d.i := by simp only [MmLoop, hj] at hL; omega
      have hF := hK.F hin _ hm3
      have hM := hK.M hin _ hm3
      have hne : ¬ d.i % 3 = (d.i - 1) % 3 := by omega
      simp only [qkDoneS, hj, hne, and_false, ite_false, reduceCtorEq, false_and,
        Nat.add_zero] at hF hM
      have hcs := cnt0_succ (i := d.i - 1) hm3
      rw [show d.i - 1 + 1 = d.i by omega] at hcs
      simp only [ite_true] at hcs
      exact ⟨(d.i - 1) % 3, hm3, hg, hlead, hcta, .inr ⟨h3, h4⟩, hTc, by omega⟩
  · cases hpart

theorem kv_fits (c : Nat) (s : Fin 3) : ((kvDecl Q L X c).slot s).Fits := by
  refine ⟨by simp [SingleTmaRing.Decl.slot, kvDecl], by simp [SingleTmaRing.Decl.slot, kvDecl], ?_⟩
  simp [SingleTmaRing.Decl.slot, kvDecl, SingleTmaRing.Slot.tx, MBarrier.limit]

/-- **A copy's write and an MMA read of one ring byte are ordered.** -/
theorem copy_read_ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {i mi : EvId} {x y z : Nat} {isB : Bool} {idx : Nat} {l : Loc}
    (hca : AsyncCovers X i (.write (.load x y z)) l)
    (hcb : AsyncCovers X mi (.mmaRead isB idx) l) (hsp : l.space = .shared)
    (hhi : l.addr < L.sharedBase + 196608) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async mi (.mmaRead isB idx)) ∨
      modelCausality L X l (.async mi (.mmaRead isB idx)) (.async i (.write (.load x y z))) := by
  obtain ⟨g1, k1⟩ := i
  obtain ⟨g2, km⟩ := mi
  obtain ⟨pc1, a1, sp1, he1, hl1⟩ := copy_write_at hca
  obtain ⟨⟨-, s1, hs1, hm1, hreg, -⟩, -⟩ := copy_ring_ev hp hX he1
  obtain ⟨-, hc1, hsl1⟩ := hreg x y z l hl1
  obtain ⟨s2, hs2, hg2, hlead, hc2, hsl2, hTc, hpol⟩ := mma_read_info hp hX hcb hsp hhi
  obtain rfl := inSlot_unique hs1 hs2 hsl1 hsl2
  have hg1 := Frame.lt_of_get hX he1
  obtain ⟨c, hcdef⟩ : ∃ c, g2 / L.block = c := ⟨_, rfl⟩
  have hc12 : g1 / L.block = c := by rw [← hc1, hc2, hcdef]
  rw [hcdef] at hlead hpol
  rw [hc12] at hm1
  have hcg : c < L.grid := by
    rw [← hcdef]; exact NamedBar.cta_lt hg2
  set S := (kvDecl Q L X c).slot ⟨s1, hs1⟩ with hS
  have H := kv_hyp hp hX hcg ⟨s1, hs1⟩
  have hsame : SameCta L g1 g2 := ⟨hg1, hg2, by rw [hc12, hcdef]⟩
  subst hlead
  have hR : X.TcAsync (S.cm, km) := hTc
  have hcR : SingleTmaRing.readUse X S (S.cm, km) + 1 ≤ okPolls S.full ((X.tr S.cm).take km) :=
    hpol
  have hord := SingleTmaRing.copy_read_order hX (kv_fits c ⟨s1, hs1⟩) H hR hcR he1 hm1 hca hcb
  rcases Nat.lt_or_ge (SingleTmaRing.readUse X S (S.cm, km))
    (SingleTmaRing.copyUse X S (g1, k1)) with h | h
  · exact .inr ⟨.inl ⟨hsame.2.1, hsame.1, hsame.2.2.symm⟩, .direct (hord.2 h)⟩
  · exact .inl ⟨.inl hsame, .direct (hord.1 h)⟩

end
end PTX.Kernels.InklingRelDecode.Proof2
