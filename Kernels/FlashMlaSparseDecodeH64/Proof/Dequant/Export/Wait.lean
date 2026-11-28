-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Kernel.Progress.NextEv
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.SitePc

@[expose] public section

/-! # Warpgroup 2's time at the waits of its blocks

A dequant lane whose next event is its wait on `rawReady j` (pc 2677) or on `svDone j` (pc 2684)
of CTA `c` is a lane of warps 8–11 of the CTA, waits for a use below the CTA's uses of the slot
(`ringUses 2 j (blocksOf P L c)`), and is no earlier than the wait's slot (`rrWait`, `svWaitD` of
`Lib/Slots.lean`) of that use's block `2 u + j`, `u` its successful polls of the slot
(`deq_rrWait`, `deq_svWait`).

From one view of the lane's state (`deq_wait_end`): the wait of block `i` below the CTA's block
count with the block's slot counts (`Dequant/Ref.lean`), at `frame i + deqOff + idx`; on the trace
(`deq_poll`) the wait is on slot `i % 2` after `i / 2` successful polls. The lemma table of the
role is in `Dequant/Export/Time.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A state's counts on the role's classes at prefix `i`. -/
private def pc' (X : Execution) (g i : Nat) : Dequant.Cnt → Nat :=
  fun c => ((X.tr g).take i).countP (Dequant.cls c)

section
variable {g : Nat}

/-- An object named by the lane's own name is its CTA's, of the same family. -/
private theorem loc_fam {c : Nat} {f f' : MbarFam} (h : mbarLoc L c f = MbarRow.loc L g f') :
    c = g / L.block ∧ f = f' := by
  simp only [MbarRow.loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff, true_and] at h
  exact ⟨h.1, MbarFam.off_inj h.2⟩

variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw


/-- **A dequant lane whose next event is a wait of its block** (pcs 2677, 2684): its state is
the wait of block `i` below the CTA's block count, with the block's slot counts, at time
`frame i + deqOff + idx`. -/
private theorem deq_wait_end {e : Event} (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 2677 ∨ e.pc = 2684) :
    ∃ d : Dequant.Control.D, ∃ i, Dequant.Ev L g d e ∧ (d.site = .wraw ∨ d.site = .wsv) ∧
      (8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) ∧ i < blocksOf P L (g / L.block) ∧
      Dequant.slotF d.sb = MbarRow.slot2 i ∧
      (∀ b, Dequant.SlotCounts L g (pc' X g (X.tr g).length) b
        (Dequant.uses b (i + Dequant.incR d.site)) (Dequant.uses b i) (Dequant.uses b i)
        (Dequant.uses b i)) ∧
      Sched.threadTime (timed P L) X g = frame i + deqOff + d.site.idx := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := next_state hp hFw hn hub
  obtain ⟨d, n, rfl, hR, hE, hw⟩ := dequant_state hp hJ hi hev hpc' (by omega)
  have hs : d.site = .wraw ∨ d.site = .wsv := by
    have h1 := hE.1
    rcases Dequant.small_site (s := d.site) (by omega) with h | h | h | h | h | h <;>
      rw [h] at h1 ⊢ <;> simp [Dequant.Site.pc] at h1 ⊢ <;> omega
  have hc : (fun c => n (.dequant c)) = pc' X g (X.tr g).length :=
    funext fun c => state_count hσ (.dequant c)
  have h0 : pc' X g (X.tr g).length .ub = 0 := by
    obtain ⟨Y, hY, hpre, he⟩ := id hn
    have := wg2_take_noUb hY he
    unfold pc'
    rw [List.take_length]
    rwa [hpre] at this
  have hR0 := hR (next_ub hn hσ)
  rw [hc] at hR0
  have hR' := deq_rounds hp hX hσ (by rcases hs with h | h <;> rw [h] <;> rfl)
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  simp only at hs
  have hlp : site.inLoop = true := by rcases hs with rfl | rfl <;> rfl
  have hel : Dequant.elOff ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ = 0 := by
    rcases hs with rfl | rfl <;> rfl
  have hRl := hR0 h0
  obtain ⟨i, hwd, hsb, -, hcnt⟩ : ∃ i, Dequant.LoopWords ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ i ∧
      Dequant.LoopCounts L g ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ (pc' X g (X.tr g).length) i := by
    rcases hs with rfl | rfl <;> exact hRl
  refine ⟨_, i, hE, hs, hw, ?_, ?_, fun b => ?_, ?_⟩
  · rw [← hR']; exact hwd.1
  · simp only at hsb
    rw [hsb, Dequant.slotF_slot2]
  · obtain ⟨h1, h2, h3, h4⟩ := hcnt b
    rcases hs with rfl | rfl <;> exact ⟨h1, h2, h3, h4⟩
  · rw [timed_eq, Sched.threadTime_of hσ]
    show idleBase + 29 + Dequant.place _ = _
    rw [Dequant.place_loop hlp, Dequant.blk_eq hwd, hel]
    simp only [frame, idleBase, roleBase, deqBlk0, loopBase, deqOff, deqOrg, stride]
    omega

/-- The ring a block's wait site polls. -/
private def waitFam : Dequant.Site → Fin 2 → MbarFam
  | .wraw => .rawReady
  | _ => .svDone

/-- **A dequant lane whose next event is a wait of its block**, on the trace: the wait is on slot
`i % 2` of the site's ring, after `i / 2` successful polls of it, at `frame i + deqOff + idx`. -/
private theorem deq_poll {e : Event} {l : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (he : e.kind = .wait l q ok acq sc)
    (hpc : e.pc = 2677 ∨ e.pc = 2684) :
    ∃ (s : Dequant.Site) (i : Nat), e.pc = s.pc ∧ (8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) ∧
      i < blocksOf P L (g / L.block) ∧ l = MbarRow.loc L g (waitFam s (MbarRow.slot2 i)) ∧
      okPolls l (X.tr g) = i / 2 ∧
      Sched.threadTime (timed P L) X g = frame i + deqOff + s.idx := by
  obtain ⟨d, i, hE, hs, hw, hi, hsb, hcnt, ht⟩ :=
    deq_wait_end hp hX hFw hn (fun _ h => by rw [he] at h; cases h) hpc
  have hk := hE.2
  unfold Dequant.EvK at hk
  have hP := wg2_okPolls hp hX hFw hw (X.tr g).length l
  obtain ⟨h1, h2, -, -⟩ := hcnt (MbarRow.slot2 i)
  simp only [pc', List.take_length] at h1 h2 hP
  have hl : l = MbarRow.loc L g (waitFam d.site (MbarRow.slot2 i)) := by
    rcases hs with h | h <;> rw [h] at hk ⊢
    · obtain ⟨_, hk⟩ | ⟨_, hk⟩ := hk <;> rw [he] at hk
      · obtain ⟨h3, -⟩ := Kind.wait.inj hk
        rw [h3, Dequant.raw_loc hp, hsb]
        rfl
      · cases hk
    · obtain ⟨_, hk⟩ | ⟨_, hk⟩ := hk <;> rw [he] at hk
      · obtain ⟨h3, -⟩ := Kind.wait.inj hk
        rw [h3, Dequant.sv_loc hp, hsb]
        rfl
      · cases hk
  refine ⟨d.site, i, hE.1, hw, hi, hl, ?_, ht⟩
  rw [hP, hl]
  rcases hs with h | h <;> rw [h]
  · rw [h] at h1
    exact h1.trans (Dequant.uses_slot i)
  · exact h2.trans (Dequant.uses_slot i)

/-- **A dequant lane at a wait of its block on slot `j` of ring `F`** (site at offset `o`): it is a
lane of warps 8–11 of the CTA, waits for a use below the CTA's uses of the slot and is no earlier
than the wait's slot of that use's block. -/
private theorem ring_wait {pc o c p : Nat} {F : Fin 2 → MbarFam} {j : Fin 2} {ok acq : Bool}
    {sc : MbarScope} (hpc : pc = 2677 ∨ pc = 2684) (hinj : ∀ a b, F a = F b → a = b)
    (hF : ∀ s : Dequant.Site, s.pc = pc → waitFam s = F ∧ s.idx = o)
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨pc, .wait (mbarLoc L c (F j)) p ok acq sc⟩) :
    (g / L.block = c ∧ 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) ∧
    okPolls (mbarLoc L c (F j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    frame (2 * okPolls (mbarLoc L c (F j)) (X.tr g) + j.val) + deqOff + o ≤
      Sched.threadTime (timed P L) X g := by
  obtain ⟨s, i, hpc', hw, hi, hl, hP, ht⟩ := deq_poll hp hX hFw hn rfl hpc
  obtain ⟨hFs, ho⟩ := hF s hpc'.symm
  rw [hFs] at hl
  obtain ⟨rfl, hj⟩ := loc_fam hl
  cases hinj _ _ hj
  rw [hP, ht, ho]
  refine ⟨⟨rfl, hw⟩, ?_, ?_⟩ <;> simp only [ringUses, MbarRow.slot2, frame, loopBase, stride] <;>
    omega

/-- **A dequant lane at its wait on `rawReady j`** (pc 2677): a lane of warps 8–11 of CTA `c`, it
waits for a use below the CTA's uses of the slot and is no earlier than `rrWait` of that use's
block. -/
theorem deq_rrWait {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2677, .wait (mbarLoc L c (.rawReady j)) p ok acq sc⟩) :
    (g / L.block = c ∧ 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) ∧
    okPolls (mbarLoc L c (.rawReady j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    rrWait (2 * okPolls (mbarLoc L c (.rawReady j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g :=
  ring_wait hp hX hFw (.inl rfl) (fun _ _ h => MbarFam.rawReady.inj h) (fun s h => by
    rcases Dequant.small_site (s := s) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Dequant.Site.pc, waitFam, Dequant.Site.idx, deqWraw] at h ⊢) hn

/-- **A dequant lane at its wait on `svDone j`** (pc 2684): a lane of warps 8–11 of CTA `c`, it
waits for a use below the CTA's uses of the slot and is no earlier than `svWaitD` of that use's
block. -/
theorem deq_svWait {c p : Nat} {j : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g
      ⟨2684, .wait (mbarLoc L c (.svDone j)) p ok acq sc⟩) :
    (g / L.block = c ∧ 8 ≤ MbarRow.warp L g ∧ MbarRow.warp L g < 12) ∧
    okPolls (mbarLoc L c (.svDone j)) (X.tr g) < ringUses 2 j.val (blocksOf P L c) ∧
    svWaitD (2 * okPolls (mbarLoc L c (.svDone j)) (X.tr g) + j.val) ≤
      Sched.threadTime (timed P L) X g :=
  ring_wait hp hX hFw (.inr rfl) (fun _ _ h => MbarFam.svDone.inj h) (fun s h => by
    rcases Dequant.small_site (s := s) (by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Dequant.Site.pc, waitFam, Dequant.Site.idx, deqWsv] at h ⊢) hn

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
