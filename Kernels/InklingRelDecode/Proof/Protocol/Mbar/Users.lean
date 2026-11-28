-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
open PTX MbarRow

private abbrev HasOffset (n : Nat) := ∃ j, n=initOffset j

private theorem ready : ∀ s, HasOffset (Iface.kvReady s) := by decide
private theorem empty : ∀ s, HasOffset (Iface.kvEmpty s) := by decide
private theorem score : ∀ s, HasOffset (Iface.sReady s) := by decide
private theorem prob : ∀ s, HasOffset (Iface.pReady s) := by decide

private theorem post {Q L X g k e l} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some e) (hm : Frame.MbarOf e l) (late : 574≤e.pc) :
    Export.afterInit e.pc ∧ ∃ j, l=loc L g (initOffset j) := by
  have pick {n} (addr : l=loc L g n) (h : HasOffset n) : ∃ j, l=loc L g (initOffset j) := by
    obtain ⟨j,rfl⟩ := h
    exact ⟨_,addr⟩
  have cp : ∀ p ∈ ([2389,2391,2394,2396,2404,2406,2410,2412] : List Nat),
      Export.afterInit p := by simp [Export.afterInit]
  cases mbar_use rows hg he hm with
  | startup _ h | dispatch _ h => cases h
  | prologue span _ => exact (Nat.not_lt_of_ge late span.2.2).elim
  | loader _ h =>
    cases h with
    | emptyWait pc addr _ => exact ⟨pc ▸ (by decide),pick addr (empty _)⟩
    | readyArrive pc _ addr _ => exact ⟨pc ▸ (by decide),pick addr (ready _)⟩
    | readyCopy pc _ addr _ => exact ⟨cp _ pc,pick addr (ready _)⟩
  | mma _ h =>
    cases h with
    | readyWait pc addr _ => exact ⟨pc ▸ (by decide),pick addr (ready _)⟩
    | pWait pc addr _ => exact ⟨pc ▸ (by decide),pick addr (prob _)⟩
    | sCommit pc addr _ => exact ⟨pc ▸ (by decide),pick addr (score _)⟩
    | emptyCommit pc addr _ => exact ⟨pc ▸ (by decide),pick addr (empty _)⟩
    | doneCommit pc addr _ => exact ⟨pc ▸ (by decide),⟨10,addr⟩⟩
    | finalCommit pc addr _ => exact ⟨pc ▸ (by decide),⟨11,addr⟩⟩
  | softmax _ h =>
    cases h with
    | pArrive pc _ addr _ => exact ⟨pc ▸ (by decide),pick addr (prob _)⟩
    | sWait pc addr _ => exact ⟨pc ▸ (by decide),pick addr (score _)⟩
    | oWait pc addr _ => exact ⟨pc ▸ (by decide),⟨10,addr⟩⟩
  | epilogue _ h =>
    cases h with
    | finalWait pc addr _ => exact ⟨pc ▸ (by decide),⟨11,addr⟩⟩

theorem post_publication {Q L m X g k e l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (rows : MbarRows Q L X)
    (he : X.get (g,k)=some e) (hm : Frame.MbarOf e l) (late : 574≤e.pc) :
    ∃ v n, X.MbInit v l n ∧ InitPublished L X v (g,k) l := by
  obtain ⟨site,j,rfl⟩ := post rows (Frame.lt_of_get hX he) he hm late
  have nu (f : Fault) : e.kind≠.ub f := by
    obtain ⟨p,kd⟩ := e
    rintro rfl
    cases hm
  obtain ⟨v,hv,ord⟩ := published_at hp hX he nu site j
  exact ⟨v,1,hv,.inl ord⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
