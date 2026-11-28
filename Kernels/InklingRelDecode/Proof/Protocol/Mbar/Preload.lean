-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Users
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Half
import Kernels.InklingRelDecode.Proof.Prologue.Export.PreloadSync
import Kernels.InklingRelDecode.Proof.Prologue.Export.Init
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Common.Export.Publisher
import Kernels.InklingRelDecode.Proof.Protocol.Warp.Leader
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
open PTX PTX.Frame MbarRow

private theorem third_position {Q L m X g k pc cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.bar 0 cnt .sync⟩)
    (ord : ((X.tr g).take k).countP (Execution.isBarId 0)=2) (low : g%L.block<32) :
    ∃ u e, X.get (g,u)=some e ∧ 180≤e.pc ∧ e.pc<574 ∧ ∀ f, e.kind≠.ub f := by
  have later : (180≤pc ∧ pc<574) ∨
      1≤((X.tr g).take k).countP (Execution.isBarId 1) := by
    obtain ⟨_,one|full|half⟩ := Lib.recorded_bar hX hp.block he
    · cases one.1
    · obtain ⟨_,rfl,_⟩ := full
      have hit := (Export.final_late hp hX he).mpr (by omega)
      change (pc==2850 || pc==2853)=true at hit
      simp only [Bool.or_eq_true,beq_iff_eq] at hit
      rcases hit with rfl|rfl
      · exact .inr (by have h := Export.after_initialization hp hX he (by simp) (by decide); omega)
      · exact .inr (Export.exit_sync_publication hp hX he)
    · have h : ∀ p ∈ BarRow.halfZeroSites, (180≤p ∧ p<574) ∨ Export.afterInit p := by
        simp [BarRow.halfZeroSites,Export.afterInit]
      rcases h pc half.2.2 with r|post
      · exact .inl r
      · exact .inr (by have h := Export.after_initialization hp hX he (by simp) post; omega)
  rcases later with ⟨lo,hi⟩|phase
  · exact ⟨k,_,he,lo,hi,by simp⟩
  · obtain ⟨u,p,c,mode,_,bar,zero⟩ := nth_bar (q := 0) phase
    obtain ⟨rfl,rfl⟩ := Lib.publication_kind hX hp.block bar
    obtain rfl := Export.first_data_sync hp hX bar (by omega) zero
    exact ⟨u,_,bar,by decide,by decide,by simp⟩

private theorem init_epoch {Q L X g k pc l} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨pc,.mbInit l 1⟩) :
    ((X.tr g).take (k+1)).countP (Execution.isBarId 0)=2 := by
  obtain ⟨j,pos,_,_,low,_⟩ := init_info rows hg he
  have range := (by decide : ∀ j : Fin 12, 27≤134+4*j.val ∧ 134+4*j.val<574) j
  have use := rows.prologue.2 hg he (by
    change PrologueAt L g pc; exact ⟨by omega,pos ▸ range⟩) (l := l) rfl
  cases use with
  | init _ _ _ _ _ _ _ count _ =>
    rw [List.take_add_one,show (X.tr g)[k]?=_ from he,List.countP_append,count]
    rfl
  | preloadArrive _ _ _ kind => cases kind
  | preloadCopy _ _ _ kind => obtain ⟨_,_,bad,_⟩ := kind; cases bad

theorem preload_published {Q L m X g k e l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (rows : MbarRows Q L X)
    (he : X.get (g,k)=some e) (hm : Frame.MbarOf e l) (early : e.pc<574)
    (ordinary : ∀ n, e.kind≠.mbInit l n) :
    ∃ v n, X.MbInit v l n ∧ InitPublished L X v (g,k) l := by
  have hg := lt_of_get hX he
  have layout : g%L.block<128 ∧ 180<e.pc ∧ ∃ j, l=loc L g (initOffset j) := by
    cases mbar_use rows hg he hm with
    | startup _ h | dispatch _ h => cases h
    | prologue atPc h =>
      have warp := atPc.1
      refine ⟨by omega,?_⟩
      cases h with
      | init _ _ _ kind _ _ _ _ _ => exact (ordinary 1 kind).elim
      | preloadArrive s pc addr _ =>
        have b := (by decide : ∀ s : Fin 3, 180<([193,237,279] : List Nat)[s.val]!) s
        refine ⟨by omega,⟨2*s.val,by omega⟩,?_⟩
        rw [addr]; fin_cases s <;> rfl
      | preloadCopy s pc addr _ =>
        have b := (by decide : ∀ s, (preloadCopies s).all (180<·)) s
        exact ⟨of_decide_eq_true (List.all_eq_true.mp b _ pc),⟨2*s.val,by omega⟩,by
          rw [addr]; fin_cases s <;> rfl⟩
    | epilogue h _ | softmax h _ | mma h _ | loader h _ =>
      simp only [EpilogueAt,SoftmaxAt,MmaAt,LoaderAt] at h
      omega
  obtain ⟨low,lo,j,rfl⟩ := layout
  have nu (f : Fault) : e.kind≠.ub f := by obtain ⟨p,kd⟩ := e; rintro rfl; cases hm
  have phase := Prologue.Export.preload_phase hp hX he nu lo early
  obtain ⟨a,pc,cnt,mode,ak,bar,ord⟩ := nth_bar (q := 2) phase
  obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block bar
  have len : k<(X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hc : g/L.block<L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cta,warp⟩ := KV.leader_warp (X := X) hp hc (by decide : 0<8)
  obtain ⟨i,p,c,sync,idx⟩ := half_member hp hX bar ord (by omega) cta low (by omega)
  obtain ⟨v,ev,get,lo,hi,clear⟩ := third_position hp hX sync idx (by omega)
  obtain ⟨u,_,init⟩ := Prologue.Export.initialized hp hX get clear lo hi (by omega)
    (Warp.leader_wins hp hX hc (by decide)) j
  have hb := init_epoch rows hy init
  simp only [loc,cta] at init ⊢
  exact ⟨_,1,⟨_,init⟩,.inl (half_handoff hp hX ⟨hy,hg,cta⟩ len (by omega) low hb phase)⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
