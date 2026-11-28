-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchRound
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

/-- Ordinal of the next barrier zero, in the prefix before the event at k. -/
abbrev barOrdinal (X : Execution) (g k : Nat) :=
  ((X.tr g).take k).countP (Execution.isBarId 0)

/-- A counted barrier that a data lane has passed supplies an actual arrival by
each data peer that did not exit before this ordinal. -/
theorem data_arrival {Q L m X g h j pc cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (sync : X.IsBarrier (g,j) 0 cnt pc)
    (passed : j+1<(X.tr g).length) (lg : g%L.block<128) (lh : h%L.block<128)
    (cta : h/L.block=g/L.block)
    (ex : ∀ k p, X.get (h,k)=some ⟨p,.exit⟩ → barOrdinal X g j < barOrdinal X h k) :
    ∃ i p c, X.IsBarrier (h,i) 0 c p ∧ barOrdinal X h i=barOrdinal X g j := by
  apply NamedBar.D_member_arrival (f := (g,j)) hX (Export.barZeroSources hp hX)
    (by simp [CtaBarrier.warps,hp.block]) (Finset.card_range _)
    (by simp [CtaBarrier.warps,hp.block]) (by simp [CtaBarrier.target]) sync passed
    (Finset.mem_range.mpr (by dsimp; omega)) cta (Finset.mem_range.mpr (by omega))
  rintro ⟨k,p,get⟩
  obtain ⟨i,p,c,mode,_,ev,ord⟩ := nth_bar (Nat.succ_le_of_lt (ex k p get))
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block ev
  exact ⟨i,p,c,ev,ord⟩

/-- Read one byte of the word exchanged at a given publishing generation. The
per-generation induction only has to identify the publishing pc in the selected
warp and place that warp's exits. The reads-from and causality witnesses follow. -/
theorem published_scratch_byte {Q L m X g h k ac bs byte} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (read : X.get (g,k)=some ⟨2252,.rd ac bs⟩)
    (within : byte < ac.size) (lg : g%L.block<128) (lh : h%L.block<128)
    (cta : h/L.block=g/L.block) (warp : h%L.block/32=g%L.block%4)
    (atGen : ∀ i p c, X.IsBarrier (h,i) 0 c p → barOrdinal X h i+1=barOrdinal X g k → p=2251)
    (ex : ∀ v p, X.get (h,v)=some ⟨p,.exit⟩ → barOrdinal X g k≤barOrdinal X h v) :
    ∃ v dst ys t u acc data, X.get (h,v)=some ⟨2250,.wr dst ys⟩ ∧
      X.rf (.thread (g,k)) byte=some (.thread (t,u)) ∧ X.get (t,u)=some ⟨2250,.wr acc data⟩ ∧
      t/L.block=g/L.block ∧ t%L.block/32%4=g%L.block%4 ∧ bs[byte]?=some data[byte]? ∧
      ¬baseCausality L X (t,u) (h,v) ∧ ¬baseCausality L X (g,k) (t,u) := by
  obtain ⟨j,rfl,sync⟩ := Softmax.Export.read_sync hp hX read
  have count : barOrdinal X g (j+1)=barOrdinal X g j+1 := by
    unfold barOrdinal
    rw [List.take_add_one,show (X.tr g)[j]? = _ from sync,List.countP_append]
    rfl
  obtain ⟨i,p,c,bar,ord⟩ := data_arrival hp hX sync (List.getElem?_eq_some_iff.mp read).1
    lg lh cta (fun v p get => by have := ex v p get; omega)
  obtain rfl := atGen i p c bar (by omega)
  obtain ⟨v,dst,ys,left,store⟩ := Softmax.Export.sync_store hp hX bar
  have ⟨addr,size⟩ := Softmax.Export.scratch_store hp hX store
  have ⟨whereRead,width⟩ := Softmax.Export.scratch_read hp hX read
  have cov : dst.Covers (ac.loc.at byte) := by
    unfold Acc.Covers
    rw [addr,whereRead,cta,warp,Nat.mod_mod,size]
    refine ⟨rfl,rfl,Nat.le_add_right ..,Nat.add_lt_add_left (by omega) _⟩
  obtain ⟨t,u,a,data,rf,get,ct,idx,val,old,later⟩ :=
    scratch_byte hp hX read store bar sync lg lh cta ord (by omega) (by omega) within cov
  exact ⟨v,dst,ys,t,u,a,data,store,rf,get,ct,idx,val,old,later⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
