-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Export.CommitOrder
public import Lemmas.Kernel.CommitNextExit
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Common.Successor

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Frame PTX.Flow

private def middle (s : Site) := s = .pvBar ∨ s = .qkBar ∨ s = .finBar
private def lastMiddle (s : Site) := s = .pWait ∨ s = .kvWait ∨ s = .finElect

private theorem after_done {L g d s e} (h : d.site = .pvCommit2)
    (hz : next L g d e = some (some s)) : middle s.site := by
  obtain ⟨site,i,v⟩ := d
  subst_vars
  simp only [next,Option.some.injEq] at hz
  subst s
  unfold iterNext
  split <;> first | exact .inr (.inr rfl) | split <;> first | exact .inr (.inl rfl) | exact .inl rfl

private theorem after_mid {L g d s e} (h : middle d.site)
    (hz : next L g d e = some (some s)) : lastMiddle s.site := by
  obtain ⟨site,i,v⟩ := d
  rcases h with h | h | h <;> change site = _ at h <;> subst site <;>
    simp only [next,Option.some.injEq] at hz <;> subst s
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

private theorem middle_free : ∀ s, middle s ∨ lastMiddle s →
    s.pc ∉ ([2499,2546,2548,2553] : List Nat) := by
  rintro s ((rfl | rfl | rfl) | (rfl | rfl | rfl)) <;> decide

/-- The last PV pair: the two intervening events precede the final notification
and neither is a commit. The observed final notification carries the dependency to exit. -/
public theorem final_pair {Q L m X g k sp sf wait finish c r} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hw : g % L.block / 32 = 7)
    (he : X.get (g,k) = some ⟨2548,.tc (.commit sp)⟩)
    (last : X.get (g,k+3) = some ⟨2553,.tc (.commit sf)⟩)
    (obs : Witness L X (.async (g,k+3) (.tcNotify r)) wait)
    (path : Relation.TransGen (DepStep L kernel X) (.thread wait,true) (.thread finish,false))
    (ex : OwnerExit L X c finish) :
    SharedFinished L kernel Assumptions.all X (.async (g,k) (.tcNotify r)) c := by
  obtain ⟨w,x,round,d,n,hs,pc⟩ := mma_state hp hX hf he (fun _ => nofun)
    (by change 2422 < 2548; decide) (by change 2548 < 2557; decide)
  change 2548 = d.site.pc at pc
  have site : d.site = .pvCommit2 := by
    have : ∀ s : Site, 2548 = s.pc → s = .pvCommit2 := by
      intro s
      cases s <;> first | decide | (rename_i i; fin_cases i <;> decide)
    exact this _ pc
  have hl : k+3 < (X.tr g).length := (List.getElem?_eq_some_iff.mp last).1
  obtain ⟨a,ha⟩ : ∃ e, X.get (g,k+1) = some e :=
    ⟨_,List.getElem?_eq_getElem (by omega : k+1 < (X.tr g).length)⟩
  obtain ⟨b,hb⟩ : ∃ e, X.get (g,k+2) = some e :=
    ⟨_,List.getElem?_eq_getElem (by omega : k+2 < (X.tr g).length)⟩
  have ua := noUbBefore_of_get hX last _ (by omega) _ ha
  have ub := noUbBefore_of_get hX last _ (by omega) _ hb
  obtain ⟨d1,z1,st1⟩ := mma_successor hp hX hf hs he ha ua
  have ma := after_done site z1
  have ha1 := st1 (by rcases ma with h | h | h <;> rw [h] <;> decide)
  obtain ⟨d2,z2,st2⟩ := mma_successor hp hX hf ha1 ha hb ub
  have mb := after_mid ma z2
  have hb2 := st2 (by rcases mb with h | h | h <;> rw [h] <;> decide)
  have ca := event_pcU (fun g hg => thread_sound hp hg) hX ha ha1 ua
  have cb := event_pcU (fun g hg => thread_sound hp hg) hX hb hb2 ub
  change a.pc = d1.site.pc at ca
  change b.pc = d2.site.pc at cb
  have nearest : ∀ j, k < j → j < k+3 → ¬ ∃ s, X.Commit (g,j) s := by
    rintro j hj hj' ⟨s,p,h⟩
    obtain ⟨_,_,cases⟩ := commit hp hX hf hw h
    have mem : p ∈ ([2499,2546,2548,2553] : List Nat) := by
      rcases cases with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
    rcases (by omega : j = k+1 ∨ j = k+2) with rfl | rfl
    · obtain rfl := Option.some.inj (ha.symm.trans h)
      exact middle_free _ (.inl ma) (ca ▸ mem)
    · obtain rfl := Option.some.inj (hb.symm.trans h)
      exact middle_free _ (.inr mb) (cb ▸ mem)
  have present := obs.choose_spec.2.1
  have finalCommit : ∃ s, X.Commit (g,k+3) s := ⟨_,_,last⟩
  have asm := hX.asm Assumptions.commitOrder (by simp [Assumptions.all])
  have first := asm g k (k+3) 2548 sp r he (by decide) (by omega) finalCommit nearest present
  exact SharedFinished.of_commitNext (j := (g,k+3)) first
    ⟨rfl,rfl,by omega,first,present,⟨_,_,he,by decide +kernel⟩,finalCommit,nearest⟩ obs path ex

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
