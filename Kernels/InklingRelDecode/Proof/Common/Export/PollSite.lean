-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows
import Kernels.InklingRelDecode.Proof.Common.Export.Place
public import Kernels.InklingRelDecode.Proof.Common.Export.Publication
import Kernels.InklingRelDecode.Proof.Softmax.Export.Mbar
import Kernels.InklingRelDecode.Proof.Loader.Export.Mbar
import Kernels.InklingRelDecode.Proof.Mma.Export.Mbar
import Kernels.InklingRelDecode.Proof.Epilogue.Export.Mbar

@[expose] public section

/-! # The object of a poll at one of the code's six poll sites

A lane at a poll (the Softmax S-ready and O-done polls, the loader's empty poll, the MMA's
K-ready and P-ready polls, the epilogue's final poll), whether the poll is in its trace or is its
next event, polls one of the twelve objects its CTA's prologue initializes, and has passed the two
publication barriers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow MbarRow

/-- The pcs of the polls. -/
def pollSite (pc : Nat) : Prop :=
  pc = 1257 ∨ pc = 2239 ∨ pc = 2374 ∨ pc = 2462 ∨ pc = 2510 ∨ pc = 2565

private theorem init_of (off : Nat)
    (h : (∃ s : Fin 3, off = Iface.kvReady s) ∨ (∃ s : Fin 3, off = Iface.kvEmpty s) ∨
      (∃ s : Fin 2, off = Iface.sReady s) ∨ (∃ s : Fin 2, off = Iface.pReady s) ∨
      off = Iface.oDone ∨ off = Iface.oFinal) : ∃ j : Fin 12, initOffset j = off := by
  rcases h with ⟨s,rfl⟩ | ⟨s,rfl⟩ | ⟨s,rfl⟩ | ⟨s,rfl⟩ | rfl | rfl
  · fin_cases s <;> decide
  · fin_cases s <;> decide
  · fin_cases s <;> decide
  · fin_cases s <;> decide
  · exact ⟨10, by decide⟩
  · exact ⟨11, by decide⟩

/-- **The poll that occurs is of an initialized object**, after the publication barriers. -/
public theorem poll_site {Q L m X g k pc l q ok acq sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc, .wait l q ok acq sc⟩) (site : pollSite pc) :
    (∃ j : Fin 12, l = loc L g (initOffset j)) ∧ afterInit pc := by
  have nu : ∀ f, (Event.mk pc (.wait l q ok acq sc)).kind ≠ .ub f := fun _ => nofun
  have hm : Frame.MbarOf ⟨pc, .wait l q ok acq sc⟩ l := rfl
  have place := place_occ hp hX hf he hm
  refine ⟨?_, by rcases site with rfl | rfl | rfl | rfl | rfl | rfl <;> decide⟩
  simp only [StartupAt, PrologueAt, SoftmaxAt, EpilogueAt, DispatchAt, LoaderAt, MmaAt] at place
  unfold pollSite at site
  have fin : ∀ off, ((∃ s : Fin 3, off = Iface.kvReady s) ∨ (∃ s : Fin 3, off = Iface.kvEmpty s) ∨
      (∃ s : Fin 2, off = Iface.sReady s) ∨ (∃ s : Fin 2, off = Iface.pReady s) ∨
      off = Iface.oDone ∨ off = Iface.oFinal) → l = loc L g off →
      ∃ j : Fin 12, l = loc L g (initOffset j) := fun off h hl => by
    obtain ⟨j,hj⟩ := init_of off h
    exact ⟨j, by rw [hj]; exact hl⟩
  rcases site with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases Softmax.Export.wait_occ hp hX hf he nu (.inl rfl) with ⟨-,ok',hk⟩ | ⟨h',-⟩
    · obtain ⟨rfl,-⟩ := Kind.wait.inj (show Kind.wait l q ok acq sc = _ from hk)
      exact fin _ (.inr (.inr (.inl ⟨_,rfl⟩))) rfl
    · exact absurd (show (1257:Nat) = 2239 from h') (by decide)
  · rcases Softmax.Export.wait_occ hp hX hf he nu (.inr rfl) with ⟨h',-⟩ | ⟨-,ok',hk⟩
    · exact absurd (show (2239:Nat) = 1257 from h') (by decide)
    · obtain ⟨rfl,-⟩ := Kind.wait.inj (show Kind.wait l q ok acq sc = _ from hk)
      exact fin _ (.inr (.inr (.inr (.inr (.inl rfl))))) rfl
  · have hw : g % L.block / 32 = 6 := by
      rcases place with h | h | h | h | h | h | h <;> omega
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Loader.Export.poll hp hX hf hw he
    exact fin _ (.inr (.inl ⟨_,rfl⟩)) rfl
  · have hw : g % L.block / 32 = 7 := by
      rcases place with h | h | h | h | h | h | h <;> omega
    obtain ⟨-,-,⟨-,rfl,rfl⟩ | ⟨h',-⟩⟩ := Mma.Export.poll hp hX hf hw (.inl rfl) he
    · exact fin _ (.inl ⟨_,rfl⟩) rfl
    · omega
  · have hw : g % L.block / 32 = 7 := by
      rcases place with h | h | h | h | h | h | h <;> omega
    obtain ⟨-,-,⟨h',-⟩ | ⟨-,rfl,rfl⟩⟩ := Mma.Export.poll hp hX hf hw (.inr rfl) he
    · omega
    · exact fin _ (.inr (.inr (.inr (.inl ⟨_,rfl⟩)))) rfl
  · obtain ⟨ok',hk⟩ := Epilogue.Export.wait_occ hp hX hf he nu rfl
    obtain ⟨rfl,-⟩ := Kind.wait.inj (show Kind.wait l q ok acq sc = _ from hk)
    exact fin _ (.inr (.inr (.inr (.inr (.inr rfl))))) rfl

end PTX.Kernels.InklingRelDecode.Proof.Export
