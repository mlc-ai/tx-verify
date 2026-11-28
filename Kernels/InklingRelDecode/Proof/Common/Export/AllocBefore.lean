-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.InklingRelDecode.Proof.Common.Staged.Bar0
import Kernels.InklingRelDecode.Proof.Common.ResourceCount
import Kernels.InklingRelDecode.Proof.Common.Export.Tmem
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.NamedBarEarlyMember

@[expose] public section

/-! # An event past the first barrier 0 follows its CTA's allocation

The first `bar.sync 0` is the CTA's, so lane 0 of warp 0 made its first arrival, and before it the
lane's allocation (its first paired operation, of 512 columns). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Proof PTX.Flow PTX.Frame PTX.Tmem.Pair

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem get_of_take {g n j : Nat} {x : Event} (h : ((X.tr g).take n)[j]? = some x) :
    j < n ∧ X.get (g, j) = some x := by
  have hj : j < n := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp only [List.length_take] at this
    omega
  refine ⟨hj, ?_⟩
  change (X.tr g)[j]? = _
  rw [← h, List.getElem?_take, ite_eq_left hj]

/-- **An MMA, load or store has crossed its thread's first barrier 0.** -/
public theorem tc_after_start {g j pc : Nat} {k : TcKind} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,j) = some ⟨pc,.tc k⟩)
    (hk : (∃ d s a mk, k = .mma d s a mk) ∨ (∃ a v s, k = .ld a v s) ∨ ∃ a v s, k = .st a v s) :
    1 ≤ ((X.tr g).take j).countP (Execution.isBarId 0) := by
  by_contra lt
  obtain ⟨s,n,-,hs,-,hE⟩ := early_at (Q := Q) hp hX he (by simp) (by unfold c0; omega)
  obtain ⟨site,tm,x,bw⟩ := s
  simp only at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl <;> simp only [Startup.Ev] at hE
  all_goals rcases hk with ⟨d,s,a,mk,rfl⟩|⟨a,v,s,rfl⟩|⟨a,v,s,rfl⟩
  all_goals simp at hE

public theorem alloc_before {h f : Nat} {ev : Event} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (h,f) = some ev) (late : 1 ≤ ((X.tr h).take f).countP (Execution.isBarId 0)) :
    ∃ j pc grp dst n, X.get ((h/L.block)*L.block + 0*32, j) =
        some ⟨pc,.tc (.resource grp dst (.alloc n))⟩ ∧
      j+1 < (X.tr ((h/L.block)*L.block + 0*32)).length ∧
      baseCausality L X ((h/L.block)*L.block + 0*32, j) (h,f) ∧
      ((X.tr ((h/L.block)*L.block + 0*32)).take (j+1)).countP (Execution.isBarId 0) ≤ 1 ∧
      ∃ i e', j < i ∧ X.get ((h/L.block)*L.block + 0*32, i) = some e' ∧ ∀ f, e'.kind ≠ .ub f := by
  have hb : L.block = 256 := hp.block
  have hg := Frame.lt_of_get hX he
  have hflen : f < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨b,evb,hbget,hbid,hbc⟩ :=
    MbarRing.Slot.exists_nth_countP (Execution.isBarId 0) (show 0 + 1 ≤ _ from late)
  obtain ⟨hbf,hgb⟩ := get_of_take hbget
  rw [List.take_take,Nat.min_eq_left hbf.le] at hbc
  obtain ⟨pcb,kb⟩ := evb
  obtain ⟨cntb,mb,rfl⟩ : ∃ cnt mode, kb = .bar 0 cnt mode := by
    cases kb <;> simp [Execution.isBarId] at hbid
    rename_i id c md
    cases id <;> simp at hbid
    exact ⟨c,md,rfl⟩
  obtain ⟨hw,hcnt⟩ := bar0_sources (Q := Q) hp hX (h,b) pcb cntb ⟨mb,hgb⟩ hg
    (by dsimp only; omega)
  subst hcnt
  have hfb : X.IsBarrier (h,b) 0 none pcb :=
    Consistent.isBarrier_of_arrival (Fact.out) hX ⟨mb,hgb⟩
  set z := (h/L.block)*L.block + 0*32 with hzdef
  have hcta : z/L.block = h/L.block := by rw [hzdef,hb]; omega
  have hz : z < L.threads := by
    show (h/L.block)*L.block + 0*32 < L.grid*L.block
    have hg' : h < L.grid*L.block := hg
    rw [hb] at hg' ⊢
    omega
  obtain ⟨i,pci,hzi,hci⟩ := NamedBar.early_member_arrival (f := (h,b)) hX
    (n := CtaBarrier.warps L.block) (by simp [CtaBarrier.warps,hb]) rfl (Finset.card_range _)
    (fun w hw => by simp only [Finset.mem_range,CtaBarrier.warps,hb] at hw ⊢; omega) (by decide)
    (bar0_sources (Q := Q) hp hX) hfb (by dsimp only; omega) (by dsimp only; omega) hcta
    (by simp only [Finset.mem_range,CtaBarrier.warps,hzdef,hb]; omega)
    (fun ⟨jx,pcx,hx⟩ => by
      have h1 := bar0_exit (Q := Q) hp hX hx
      obtain ⟨i,ev',hi,hbi,hci⟩ :=
        MbarRing.Slot.exists_nth_countP (Execution.isBarId 0)
          (show 0 + 1 ≤ ((X.tr z).take jx).countP (Execution.isBarId 0) by unfold c0 at h1; omega)
      obtain ⟨hij,hgi⟩ := get_of_take hi
      rw [List.take_take,Nat.min_eq_left hij.le] at hci
      obtain ⟨pc',k'⟩ := ev'
      obtain ⟨c',m',rfl⟩ : ∃ cnt mode, k' = .bar 0 cnt mode := by
        cases k' <;> simp [Execution.isBarId] at hbi
        rename_i id c md
        cases id <;> simp at hbi
        exact ⟨c,md,rfl⟩
      obtain ⟨-,rfl⟩ := bar0_sources (Q := Q) hp hX (z,i) pc' c' ⟨m',hgi⟩ hz
        (by dsimp only; omega)
      exact ⟨i,pc',Consistent.isBarrier_of_arrival (Fact.out) hX ⟨m',hgi⟩,hci.trans hbc.symm⟩)
  have hzlen : i < (X.tr z).length := (List.getElem?_eq_some_iff.mp hzi).1
  have hc0 : c0 X z i = 0 := hci.trans hbc
  have hzlow : z % L.block < 32 := by rw [hzdef,hb]; omega
  obtain ⟨s,n,hσ,hs,-,hE⟩ := early_at (Q := Q) hp hX hzi (by simp) (by omega)
  have ops : tmemOps ((X.tr z).take i) = 1 := by
    rw [resource_prefix hp hX hf hz hzlow hzlen.le (noUbBefore_of_get hX hzi) hσ]
    obtain ⟨site,tm,x,bw⟩ := s
    simp only at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl <;> simp only [Startup.Ev] at hE
    · cases hE
    · obtain ⟨_,_,h⟩ := hE
      cases h
    · simp [resourcePhase,Startup.resourceCount,Nat.not_le_of_lt hzlow]
    · obtain ⟨_,_,h,_⟩ := hE
      cases h
    · simp [resourcePhase,Startup.resourceCount,Nat.not_le_of_lt hzlow]
  obtain ⟨j,x,hxget,hxop,hxc⟩ := MbarRing.Slot.exists_nth_countP isTmemOp
    (show 0 + 1 ≤ ((X.tr z).take i).countP isTmemOp by
      have : tmemOps ((X.tr z).take i) = 1 := ops
      unfold tmemOps at this
      omega)
  obtain ⟨hji,hgj⟩ := get_of_take hxget
  rw [List.take_take,Nat.min_eq_left hji.le] at hxc
  obtain ⟨pcx,kx⟩ := x
  obtain ⟨grp,dst,act,rfl⟩ : ∃ grp dst act, kx = .tc (.resource grp dst act) := by
    cases kx <;> simp [isTmemOp] at hxop
    rename_i c
    cases c <;> simp at hxop
    exact ⟨_,_,_,rfl⟩
  obtain ⟨-,-,hsh⟩ := (tmem_ops hp hX hf).event hz hgj
  have h0 : tmemOps ((X.tr z).take j) = 0 := hxc
  rw [h0] at hsh
  simp only [TmemShape] at hsh
  subst hsh
  have hle : c0 X z (j+1) ≤ c0 X z i := c0_mono (by omega)
  exact ⟨j,pcx,grp,dst,512,hgj,by omega,
    bar0_before (Q := Q) hp hX ⟨hz,hg,hcta⟩ hflen (by unfold c0 at *; omega) (by omega),
    by unfold c0 at *; omega,i,_,hji,hzi,by simp⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
