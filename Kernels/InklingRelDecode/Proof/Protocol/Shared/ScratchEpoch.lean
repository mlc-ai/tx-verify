-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchPublish
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchExit
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased
import Lemmas.Flow.NthEv
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mem
import Kernels.InklingRelDecode.Proof.Softmax.Export.Scratch

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

/-- An actual reads-from edge cannot cross a later data-barrier generation backwards.
The final full rendezvous supplies the exit bound for every reader. -/
theorem scratch_epoch_upper {Q L m X g h k u a bs dst ys b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩)
    (write : X.get (h,u)=some ⟨2250,.wr dst ys⟩)
    (rf : X.rf (.thread (g,k)) b=some (.thread (h,u))) (byte : b<a.size)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : h/L.block=g/L.block) :
    barOrdinal X h u ≤ barOrdinal X g k := by
  by_contra! late
  obtain ⟨i,p,c,mode,iu,bar,ord⟩ := nth_bar (Nat.succ_le_of_lt late)
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block bar
  change barOrdinal X h i=barOrdinal X g k at ord
  obtain ⟨j,q,d,peer,eq⟩ := data_arrival hp hX bar (by
    have len : u<(X.tr h).length := (List.getElem?_eq_some_iff.mp write).1
    omega) lh lg cta.symm (fun v q he => by
      rw [ord]
      exact scratch_exit_ordinal hp hX read he lg lg rfl)
  have after : k<j := by
    rcases Nat.lt_trichotomy j k with lt|rfl|gt
    · have mono := Flow.countP_take_mono (Execution.isBarId 0) (X.tr g) (Nat.succ_le_of_lt lt)
      rw [List.take_add_one,show (X.tr g)[j]?=_ from peer,List.countP_append] at mono
      change barOrdinal X g j+1≤barOrdinal X g k at mono
      omega
    · change X.get (g,j)=some ⟨q,.bar 0 d .sync⟩ at peer
      rw [read] at peer
      cases peer
    · exact gt
  have future := scratch_handoff hp hX peer bar cta.symm lg lh eq after iu
    (List.getElem?_eq_some_iff.mp write).1
  have rd : X.MemReads (.thread (g,k)) a bs := .inl ⟨_,read⟩
  exact hX.noFuture _ _ _ b _ rd byte rf (.direct (.inl future))

/-- The actual source cannot precede its own lane's store at the matching
publishing barrier. This removes all earlier writes, including older writes by
other lanes of the same warp, by choosing the reads-from lane itself. -/
theorem scratch_epoch_source {Q L m X g h k u a bs dst ys b} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,k)=some ⟨2252,.rd a bs⟩)
    (write : X.get (h,u)=some ⟨2250,.wr dst ys⟩)
    (rf : X.rf (.thread (g,k)) b=some (.thread (h,u))) (byte : b<a.size)
    (lg : g%L.block<128) (lh : h%L.block<128) (cta : h/L.block=g/L.block)
    (atGen : ∀ i p c, X.IsBarrier (h,i) 0 c p → barOrdinal X h i+1=barOrdinal X g k → p=2251) :
    X.IsBarrier (h,u+1) 0 (some 128) 2251 ∧ barOrdinal X h (u+1)+1=barOrdinal X g k := by
  have upper := scratch_epoch_upper hp hX read write rf byte lg lh cta
  obtain ⟨j,rfl,sync⟩ := Softmax.Export.read_sync hp hX read
  have count : barOrdinal X g (j+1)=barOrdinal X g j+1 := by
    unfold barOrdinal
    rw [List.take_add_one,show (X.tr g)[j]? = _ from sync,List.countP_append]
    rfl
  obtain ⟨i,p,c,bar,ord⟩ := data_arrival hp hX sync (List.getElem?_eq_some_iff.mp read).1
    lg lh cta (fun v p get => by
      have := scratch_exit_ordinal hp hX read get lg lh cta.symm
      omega)
  obtain rfl := atGen i p c bar (by omega)
  obtain ⟨v,acc,data,rfl,later⟩ := Softmax.Export.sync_store hp hX bar
  have vw : barOrdinal X h (v+1)=barOrdinal X h v := by
    unfold barOrdinal
    rw [List.take_add_one,show (X.tr h)[v]? = _ from later,List.countP_append]
    rfl
  have vu : v≤u := by
    by_contra! uv
    have rd : X.MemReads (.thread (g,j+1)) a bs := .inl ⟨_,read⟩
    have wr : X.MemWrites (.thread (h,v)) acc data := .inl ⟨_,later⟩
    have src := (hX.rf _ _ _ rd).2 b byte
    rw [rf] at src
    obtain ⟨other,_,mw,cov,_⟩ := src
    have same : other=dst := by
      rcases mw with ⟨_,get⟩|⟨_,_,get⟩
      all_goals rw [write] at get; cases get
      rfl
    subst other
    have one := Softmax.Export.scratch_store hp hX write
    have two := Softmax.Export.scratch_store hp hX later
    have covers : acc.Covers (a.loc.at b) := by
      simpa only [Acc.Covers,one.1,two.1,one.2,two.2] using cov
    have edge := scratch_handoff hp hX bar sync cta lh lg ord (Nat.lt_succ_self v)
      (Nat.lt_succ_self j) (List.getElem?_eq_some_iff.mp read).1
    have hidden := hX.hidden _ _ _ b (.thread (h,v)) acc data rd byte wr covers
      (.direct (.inl edge))
    rw [rf] at hidden
    exact hidden (.direct (.inl (.single (.inl (po_of_overlap (X := X) (a := dst) (b := acc)
      (.inr (.inl ⟨ys,⟨_,write⟩,rfl⟩)) (.inr (.inl ⟨data,⟨_,later⟩,rfl⟩))
        rfl uv ⟨_,cov,covers⟩)))))
  have uv : u≤v := by
    by_contra! after
    have diff : u≠v+1 := by
      rintro rfl
      change X.get _=_ at bar
      rw [write] at bar
      cases bar
    obtain ⟨z,vz,zu,mid⟩ := Softmax.Export.scratch_separated hp hX bar (by omega : v+1<u) write
    have bump {t p cnt} (ev : X.IsBarrier (h,t) 0 cnt p) :
        barOrdinal X h (t+1)=barOrdinal X h t+1 := by
      unfold barOrdinal
      rw [List.take_add_one,show (X.tr h)[t]?=_ from ev,List.countP_append]
      rfl
    have mono (a b : Nat) (le : a≤b) : barOrdinal X h a≤barOrdinal X h b :=
      Flow.countP_take_mono _ _ le
    have left := mono (v+2) z vz
    have right := mono (z+1) u zu
    have first := bump bar
    change barOrdinal X h (v+2)=barOrdinal X h (v+1)+1 at first
    have second := bump mid
    omega
  obtain rfl : u=v := Nat.le_antisymm uv vu
  obtain ⟨_,kind⟩ := Lib.recorded_bar hX hp.block bar
  have cnt : c=some 128 := by
    rcases kind with ⟨bad,_⟩|⟨_,_,bad⟩|⟨_,eq,_⟩
    · cases bad
    · exact (by decide : 2251 ∉ BarRow.fullZeroSites) bad |>.elim
    · simpa [BarRow.recCnt,hp.block] using eq
  exact ⟨cnt ▸ bar,by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
