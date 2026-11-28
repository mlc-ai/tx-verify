-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Flow.Regs
import Kernels.InklingRelDecode.Proof.Common.Staged.Alloc
import Kernels.InklingRelDecode.Proof.Common.Export.AllocBefore
import Kernels.InklingRelDecode.Proof.Common.Export.BaseWord
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The allocation's store exists once a thread is past the first barrier 0

The CTA's lane 0 of warp 0 allocates as its first event; its second event is the store of the
result word, which is not an undefined behaviour: the thread's first barrier-0 event follows the
allocation, so the store is not the thread's last event. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The allocation's store writes the word zero at the CTA's shared base.** -/
public theorem base_value {g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k) = some ⟨11,.wr a bs⟩) :
    a.loc = ⟨.shared,g/L.block,L.sharedBase⟩ ∧ a.size = 4 ∧ bs = (b32 0).toBytes := by
  obtain ⟨-,-,zero⟩ := base_store hp hX he
  have c1 : c0 X g k ≤ 1 := by
    have := c0_mono (X := X) (g := g) (Nat.le_add_right k 1)
    unfold c0 at this ⊢
    omega
  obtain ⟨-,-,rfl,rfl⟩ := early_write hp hX he c1
  exact ⟨rfl,rfl,rfl⟩

/-- **The allocation's store of the base word is the second event of the CTA's thread 0.** -/
public theorem base_stored {h f : Nat} {ev : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (h,f) = some ev) (late : 1 ≤ ((X.tr h).take f).countP (Execution.isBarId 0)) :
    ∃ a bs, X.get ((h/L.block)*L.block + 0*32, 1) = some ⟨11,.wr a bs⟩ := by
  obtain ⟨j,pc,grp,dst,n,hget,hlen,-,hc1,i,e',hji,hie,hnu⟩ := alloc_before hp hX hf he late
  set z := (h/L.block)*L.block + 0*32 with hz
  have hb : L.block = 256 := hp.block
  obtain ⟨s0,n0,hσ0,hs0,-,hE0⟩ := early_at (Q := Q) hp hX hget (by simp)
    (le_trans (c0_mono (Nat.le_succ j)) hc1)
  have hsite : s0.site = .alloc := by
    obtain ⟨site,tm,xx,bw⟩ := s0
    simp only at hs0 ⊢
    rcases hs0 with rfl|rfl|rfl|rfl|rfl <;> simp only [Startup.Ev] at hE0
    · rfl
    all_goals first | (obtain ⟨_,_,h,_⟩ := hE0; cases h) | (obtain ⟨_,_,h⟩ := hE0; cases h) |
      cases hE0
  obtain ⟨rfl,-⟩ := alloc_at (by omega) hsite hσ0
  obtain ⟨e1,he1⟩ : ∃ e1, X.get (z,1) = some e1 :=
    ⟨_,List.getElem?_eq_getElem (show 1 < (X.tr z).length by omega)⟩
  have nu1 : ∀ f, e1.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc1,k1⟩ := e1
    simp only at hk
    subst hk
    have := ub_last hX he1 hie
    obtain rfl : i = 1 := by omega
    rw [he1] at hie
    cases hie
    exact hnu f rfl
  obtain ⟨s1,n1,hσ1,-,-,hE1⟩ := early_at (Q := Q) hp hX he1 nu1 hc1
  obtain ⟨s0',n0',e0,h0',-,hsu⟩ := prev_start (k := 0) (by omega) hσ1
  obtain ⟨rfl,rfl⟩ : s0' = s0 ∧ n0' = n0 := by
    have := Option.some.inj (Option.some.inj (hσ0.symm.trans h0'))
    simpa using this.symm
  have lane : PTX.laneOf L z = 0 := by
    simp only [PTX.laneOf, hz, hb]
    omega
  simp only [Startup.succ, hsite, lane, ↓reduceIte, Option.some.injEq] at hsu
  subst hsu
  simp only [Startup.Ev] at hE1
  obtain ⟨col,-,hE1⟩ := hE1
  rw [hE1] at he1
  exact ⟨_,_,he1⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
