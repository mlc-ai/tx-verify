-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.PacketBudget
import Kernels.InklingRelDecode.Proof.Loader.Export.PacketIndex

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow MbarRow

private theorem worker_use {Q L X g j v l} (rows : MbarRows Q L X) (lt : g<L.threads)
    (warp : g%L.block/32=6) (get : X.get (g,j)=some v) (obj : Frame.MbarOf v l) :
    LoaderUse Q L X g j v l := by
  cases mbar_use rows lt get obj with
  | startup _ h | dispatch _ h => cases h
  | prologue h _ | softmax h _ | epilogue h _ | mma h _ => have := h.1; omega
  | loader _ h => exact h

private theorem slot {L g j c s} (addr : Ring.ready.obj L c s=loc L g (Iface.kvReady (slot3 j))) :
    j%3=s.val := by
  obtain ⟨_,_,h⟩ := Loc.mk.inj addr
  change L.sharedBase+Iface.kvReady s=L.sharedBase+Iface.kvReady (slot3 j) at h
  simp only [Iface.kvReady,slot3,Nat.add_left_cancel_iff] at h
  omega

private theorem issuer {Q L X g k c s n tx rel sc} (rows : MbarRows Q L X)
    (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨2378,.arrive (Ring.ready.obj L c s) tx n rel sc⟩) :
    g%L.block/32=6 := by
  cases mbar_use rows hg he (l := Ring.ready.obj L c s) rfl with
  | startup _ h | dispatch _ h => cases h
  | prologue h _ | softmax h _ | epilogue h _ | mma h _ =>
    have bounds := h.2; dsimp only at bounds; omega
  | loader h _ => exact h.1

theorem arrival_budget {Q L m X g k c s tx n rel sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (words : RoleBytes L X)
    (he : X.get (g,k)=some ⟨2378,.arrive (Ring.ready.obj L c s) tx n rel sc⟩) :
    g=c*L.block+192 ∧ arrivals (Ring.ready.obj L c s) ((X.tr g).take k)+1≤
      okPolls (Ring.empty.obj L c s) ((X.tr g).take k) := by
  have lt := Frame.lt_of_get hX he
  have warp := issuer rows lt he
  have cta := use_cta rows lt he (r := .ready) rfl
  have lane := Loader.Export.announce_lane hp hX hf warp he
  change g%L.block%32=0 at lane
  refine ⟨?_,?_⟩
  · have sum := Nat.div_add_mod g L.block
    rw [cta,Nat.mul_comm] at sum
    omega
  · let l := Ring.ready.obj L c s
    have budget := packet_budget (s := s) hp hX hf rows words warp he (arrivesOn l)
      (by simp [l,arrivesOn,sourceArrive]) [2378] (by decide) (by
        intro j v get use
        obtain ⟨p,kind⟩ := v
        cases kind <;> simp [arrivesOn,sourceArrive] at use
        cases worker_use rows lt warp get (l := l) (use ▸ rfl) with
        | emptyWait _ _ h => obtain ⟨_,h⟩ := h; cases h
        | readyCopy _ _ _ h => obtain ⟨_,_,h,_⟩ := h; cases h
        | readyArrive pc pos addr _ => exact ⟨List.mem_singleton.mpr pc,by simp,rfl,pos,slot addr⟩)
    rw [cta] at budget
    simpa [arrivals,l] using budget

private def copies := [2389,2391,2394,2396,2404,2406,2410,2412]

theorem issue_budget {Q L m X g k p a sp c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : MbarRows Q L X) (words : RoleBytes L X) (warp : g%L.block/32=6)
    (he : X.get (g,k)=some ⟨p,.tensorIssue a sp⟩) (obj : sp.mbar=Ring.ready.obj L c s) :
    ((X.tr g).take k).countP (issuesTo sp.mbar)+1≤
      8*okPolls (Ring.empty.obj L c s) ((X.tr g).take k) := by
  have lt := Frame.lt_of_get hX he
  have cta := use_cta rows lt he obj
  have budget := packet_budget (s := s) hp hX hf rows words warp he (issuesTo sp.mbar)
    (by simp [issuesTo]) copies (by decide) (by
      intro j v get use
      obtain ⟨p,kind⟩ := v
      cases kind <;> simp [issuesTo] at use
      cases worker_use rows lt warp get (use.trans obj) with
      | emptyWait _ _ h => obtain ⟨_,h⟩ := h; cases h
      | readyArrive _ _ _ h => cases h
      | readyCopy pc pos addr _ => exact ⟨pc,by simp,rfl,pos,slot addr⟩)
  rw [cta] at budget
  exact budget

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
