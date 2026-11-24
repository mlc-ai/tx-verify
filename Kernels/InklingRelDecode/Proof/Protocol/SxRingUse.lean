-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SxRingChain
public import Kernels.InklingRelDecode.Proof.Protocol.SxAsync
public import Kernels.InklingRelDecode.Proof.Protocol.LpObs
public import Kernels.InklingRelDecode.Proof.Interface.RdElect
public import Kernels.InklingRelDecode.Proof.Interface.RdPvBack

@[expose] public section

/-!
# The slot and the use of a tensor copy and of an MMA operand read

* `copy_box`: a tensor copy of the execution completes on `kv_ready t` of its CTA and writes only
  the 8192 bytes of one box `(isV, slab, hh)` of slot `t`
  (`boxBase L t isV slab hh = sharedBase + 32768 t + 98304 isV + 8192 slab + 16384 hh`): the
  prologue's copy site `i` is the box `(i % 2, i % 4 / 2, warp)` of slot `i / 4`
  (`ProA.copyDst_form`), the loader's copy the box of its site (`EvW.ldDst`) of slot `i % 3`.
* `mma_b_slot`: a byte the B operand of an MMA reads is in the K slot (QK) or the V slot (PV)
  `s`, and the MMA lane's commits to `kv_empty s` before the MMA are fewer than its successful
  polls of `kv_ready s` (`Ring.mma_issue_exec`, with the anchor `Lp.mma_anchor_full` and the
  lane's lead elections `lead_of_qk`, `lead_of_pv`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady kvEmpty MmShape QkIssue PvIssue)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The first byte of box `(isV, slab, hh)` of ring slot `t`. -/
def boxBase (L : Launch) (t isV slab hh : Nat) : Nat :=
  L.sharedBase + 32768 * t + 98304 * isV + 8192 * slab + 16384 * hh

/-- **A tensor copy's slot and box.** -/
theorem copy_box (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) :
    ∃ t < 3, ∃ isV slab hh, isV ≤ 1 ∧ slab ≤ 1 ∧ hh ≤ 1 ∧
      sp.mbar = kvReady L (g / L.block) t ∧
      ∀ x y z l, TensorCopy.writeLoc sp x y z = some l → l.space = .shared ∧
        l.cta = g / L.block ∧ boxBase L t isV slab hh ≤ l.addr ∧
        l.addr < boxBase L t isV slab hh + 8192 := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hTT : TT Q L X (g, k) := fun h => hf.tracked g (k + 1) hg h
  obtain ⟨col, row, dst, bar, hk, -, -, -⟩ :=
    Interface.copy_spec_at hpre hX hf.sound hf.ldRng hg he ⟨a, sp, rfl⟩ hTT
  simp only [Kind.tensorIssue.injEq] at hk
  obtain ⟨-, hspec⟩ := hk
  have hfoot : ∀ x y z l, TensorCopy.writeLoc sp x y z = some l → l.space = .shared ∧
      l.cta = g / L.block ∧ dst ≤ l.addr ∧ l.addr < dst + 8192 := by
    intro x y z l hl
    rw [hspec] at hl
    exact Ring.Foot.copy_foot Q (g / L.block) col row dst bar hl
  have hsb : ProA.SbRoom L := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    unfold ProA.SbRoom
    omega
  rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, i, hi, hs', a', s', hev, -, -, h3, hsb', -⟩ | ⟨d, P, hσ, hsh⟩
  · simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    have hdst : dst = ProA.copyDst L g d.dt i := by
      have := hsb'
      rw [hspec] at this
      simp only [EvW.kvCopySpec, Loc.mk.injEq] at this
      exact this.2.2
    rw [ProA.copyDst_form L g d.dt hsb hi] at hdst
    have := ProA.half_lt d.dt (i / 4)
    refine ⟨i / 4, by omega, i % 2, i % 4 / 2, ProA.half d.dt (i / 4), by omega, by omega,
      by omega, ?_, fun x y z l hl => ?_⟩
    · rw [h3]
      simp only [EvD.kvReadyOf, EvD.Bar.loc, EvD.Bar.off, kvReady, EvW.barLoc, EvW.kvReadyOff]
      congr 1
      omega
    · obtain ⟨h1, h2, h4, h5⟩ := hfoot x y z l hl
      refine ⟨h1, h2, ?_, ?_⟩ <;> unfold boxBase <;> omega
  · have hcp : Ring.Ld.isCp d.site = true := by
      unfold EvW.LdShape at hsh
      cases hst : d.site <;> rw [hst] at hsh <;> simp at hsh <;> rfl
    obtain ⟨b, hb, hev⟩ := Ring.ldShape_cp hsh hcp
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
    obtain ⟨-, -, rfl⟩ := hev
    have hb' : (b.2.1 = 0 ∨ b.2.1 = 1) ∧ (b.2.2 = 0 ∨ b.2.2 = 1) := by
      revert hb
      cases hs : d.site <;> simp [EvW.ldBox] <;> intro h <;> subst h <;> simp
    refine ⟨d.i % 3, Nat.mod_lt _ (by omega), if b.1 then 1 else 0, b.2.1, b.2.2,
      by split <;> omega, by omega, by omega, rfl, fun x y z l hl => ?_⟩
    have hl' := hl
    unfold EvW.ldCopy at hl'
    obtain ⟨h1, h2, h4, h5⟩ := Ring.Foot.copy_foot Q (g / L.block) _ _ _ _ hl'
    unfold EvW.ldDst at h4 h5
    obtain ⟨v, sl, hh⟩ := b
    simp only at h4 h5 hb' ⊢
    refine ⟨h1, h2, ?_, ?_⟩ <;> unfold boxBase <;> cases v <;>
      simp only [Bool.false_eq_true, ite_true, ite_false] at h4 h5 ⊢ <;> omega

/-- **The slot of a B operand byte of an MMA, and the MMA lane's counts on it.** -/
theorem mma_b_slot (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hMB : Mma.MmaBcast L X) {k pc c : Nat}
    {spec : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get (g, k) = some ⟨pc, .tc (.mma c spec acc mask)⟩) {idx : Nat} {l : Loc}
    (hl : spec.byteLoc .b idx = some l) :
    ∃ s < 3, l.space = .shared ∧ l.cta = g / L.block ∧
      ((X.tr g).take k).countP (commitsTo (kvEmpty L (g / L.block) s)) + 1 ≤
        okPolls (kvReady L (g / L.block) s) ((X.tr g).take k) ∧
      ((L.sharedBase + 32768 * s ≤ l.addr ∧ l.addr < L.sharedBase + 32768 * s + 32768) ∨
        (L.sharedBase + 98304 + 32768 * s ≤ l.addr ∧
          l.addr < L.sharedBase + 98304 + 32768 * s + 32768)) := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hk : k < (X.tr g).length := len_of_get he
  obtain ⟨d, P, hσ, hsh⟩ := mma_event_state hpre hX hf.sound hf.tracked hg he
    (.inl ⟨c, spec, acc, mask, rfl⟩)
  have hsite : (∃ j : Fin 8, d.site = .qk j) ∨ (∃ j : Fin 8, d.site = .pv j) := by
    obtain ⟨site, i, n, tm, pro⟩ := d
    cases site <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩ | simp [MmShape] at hsh
  have hlead : ElectLead L g (X.tr g) := by
    rcases hsite with ⟨j, hs⟩ | ⟨j, hs⟩
    · exact lead_of_qk hX j.val rfl hk hσ hs
    · exact lead_of_pv hX j.val rfl hk hσ hs
  obtain ⟨hw4, k0, d0, hk0, h0, hd, hs0, hin, hC, hPl⟩ := Lp.mma_anchor_full hpre hX hf hR hk hσ
  have hp0 : Ring.Mm.polled d0 = 0 := by simp [Ring.Mm.polled, hs0]
  have hdn0 : Ring.Mm.done d0 = 0 := by simp [Ring.Mm.done, hs0]
  rcases Ring.mma_issue_exec hpre hw4 hg hX hk0 h0 hd hin hp0 hdn0 (hlead.take k)
      ((bcast_of_mma hf.roleWarp hMB hg hk.le hσ).take k) (fun s _ => hPl _) (fun s _ => hC _)
      he with
    ⟨i, s, rfl, h1, h2, hB, -⟩ | ⟨b, s, rfl, h1, h2, hB, -⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB idx l hl
    exact ⟨i % 3, Nat.mod_lt _ (by omega), b1, b2, by omega, .inl ⟨b3, b4⟩⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB idx l hl
    exact ⟨b % 3, Nat.mod_lt _ (by omega), b1, b2, by omega, .inr ⟨b3, b4⟩⟩

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
theorem mma_read_at (hX : Consistent L kernel asms mem0 X) {m : EvId} {isB : Bool} {idx : Nat}
    {l : Loc} (h : AsyncCovers X m (.mmaRead isB idx) l) :
    ∃ pc c spec acc mask, X.get m = some ⟨pc, .tc (.mma c spec acc mask)⟩ ∧
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
  · exact absurd hcp (Tmem1.no_cp hX _ _)

/-- **A tensor copy and an MMA's B operand read of one byte are ordered**, through the slot of
the KV ring the byte is in (`Ring.Kv.copy_read_order` under `Lp.slot_hyp`). -/
theorem copy_read_ordered (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hR : RoleReads L X) (hp : NumPreRead Q L X)
    (G : Sr.SrPkg L kernel asms mem0 X) (hMB : Mma.MmaBcast L X)
    (hpr : Lp.PreRing Q L X) {i m : EvId}
    {x y z idx : Nat} {l : Loc} (hca : AsyncCovers X i (.write (.load x y z)) l)
    (hcb : AsyncCovers X m (.mmaRead true idx) l) :
    modelCausality L X l (.async i (.write (.load x y z))) (.async m (.mmaRead true idx)) ∨
      modelCausality L X l (.async m (.mmaRead true idx)) (.async i (.write (.load x y z))) := by
  obtain ⟨pc1, a1, sp1, he1, hw1⟩ := copy_write_at hca
  obtain ⟨pc2, c2, spec, acc, mask, he2, hb2⟩ := mma_read_at hX hcb
  simp only [ite_true] at hb2
  obtain ⟨gi, ki⟩ := i
  obtain ⟨gm, km⟩ := m
  obtain ⟨t, ht, isV, slab, hh, hv, hsl, hhh, hm1, hbox⟩ := copy_box hpre hX hf he1
  obtain ⟨bs1, bc1, blo, bhi⟩ := hbox x y z l hw1
  obtain ⟨s, hs, ms1, mc2, hcnt, hreg⟩ := mma_b_slot hpre hX hf hR hMB he2 hb2
  have hgi : gi < L.threads := Frame.lt_of_get hX he1
  have hgm : gm < L.threads := Frame.lt_of_get hX he2
  have hc : gi / L.block < L.grid := ProA.grid_lt hgi
  have hcm : gm / L.block = gi / L.block := mc2.symm.trans bc1
  have hst : s = t := by unfold boxBase at blo bhi; omega
  subst hst
  rw [hcm] at hcnt
  obtain ⟨pArr, pCp, hP⟩ := hpr (gi / L.block) hc s hs
  have H := Lp.slot_hyp hpre hX hf hR hp G hc hs hP
  have hmt : gm = G.cm (gi / L.block) :=
    (G.lane (gi / L.block) hc).mma_thread (x := (gm, km)) ⟨c2, spec, acc, mask, pc2, he2⟩ hcm
  subst hmt
  have hR' : X.TcAsync (G.cm (gi / L.block), km) := .inl ⟨c2, spec, acc, mask, pc2, he2⟩
  have hcR : Ring.Kv.readUse X (Lp.slotOf Q L X (gi / L.block) s (G.cm (gi / L.block)) pArr pCp)
      (G.cm (gi / L.block), km) + 1 ≤
      okPolls (Lp.slotOf Q L X (gi / L.block) s (G.cm (gi / L.block)) pArr pCp).full
        ((X.tr (Lp.slotOf Q L X (gi / L.block) s (G.cm (gi / L.block)) pArr pCp).cm).take km) := by
    exact hcnt
  have hsame : SameCta L gi (G.cm (gi / L.block)) := ⟨hgi, hgm, hcm.symm⟩
  obtain ⟨h1, h2⟩ := Ring.Kv.copy_read_order hX H hR' hcR he1 hm1 hca hcb
  by_cases hle : Ring.Kv.copyUse X (Lp.slotOf Q L X (gi / L.block) s (G.cm (gi / L.block)) pArr pCp)
      (gi, ki) ≤ Ring.Kv.readUse X (Lp.slotOf Q L X (gi / L.block) s (G.cm (gi / L.block)) pArr pCp)
      (G.cm (gi / L.block), km)
  · exact .inl ⟨.inl hsame, .direct (h1 hle)⟩
  · exact .inr ⟨.inl ⟨hsame.2.1, hsame.1, hsame.2.2.symm⟩, .direct (h2 (Nat.lt_of_not_le hle))⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sx
