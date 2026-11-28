-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Export.Count
public import Kernels.InklingRelDecode.Proof.Mma.Export.Count
public import Kernels.InklingRelDecode.Proof.Mma.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Loader.Export.Mbar

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow

def emptyLoc (L : Launch) (c : Nat) (s : Fin 3) : Loc :=
  ⟨.shared,c,L.sharedBase + Iface.kvEmpty s⟩

private theorem target_one {c off : Nat} {rank : Fin 16} {obj : Loc}
    (ht : TcCommit.target ⟨.one, ⟨.shared,c,off⟩, 1, c, 1⟩ rank = some obj) :
    rank = 0 ∧ obj = ⟨.shared,c,off⟩ := by
  unfold TcCommit.target at ht
  split at ht <;> try contradiction
  rename_i h
  obtain rfl : rank = 0 := Fin.ext (by have : rank.val < 1 := h.1; omega)
  exact ⟨rfl, (Option.some.inj ht).symm⟩

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k pc c : Nat}
  {sp : TcCommit.Spec} {s : Fin 3} {rank : Fin 16}

/-- The empty slot's notification is the PV commit of its own CTA, at rank zero.
Its ordinal is the ordinal of the P block that the producer just consumed. -/
theorem empty_commit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hw : g % L.block / 32 = 7)
    (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩)
    (ht : TcCommit.target sp rank = some (emptyLoc L c s)) :
    pc = 2546 ∧ g / L.block = c ∧ rank = 0 ∧ sp.mbar = emptyLoc L c s ∧
      s.val = (pollRound 2510 ((X.tr g).take k) - 1) % 3 := by
  obtain ⟨off,rfl,hp'⟩ := Mma.Export.commit hp hX hF hw he
  obtain ⟨hr,ho⟩ := target_one ht
  obtain ⟨_,hc,ha⟩ := Loc.mk.inj ho
  change c = g / L.block at hc
  change L.sharedBase + (213248 + 8*s.val) = L.sharedBase + off at ha
  have hs := s.isLt
  rcases hp' with ⟨_,rfl⟩ | ⟨hpc,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · unfold Iface.sReady at ha
    omega
  · exact ⟨hpc,hc.symm,hr,ho.symm,by dsimp [Iface.kvEmpty] at ha; omega⟩
  · unfold Iface.oDone at ha
    omega
  · unfold Iface.oFinal at ha
    omega

theorem no_ready_commit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hF : Follow Q L X) (hw : g % L.block / 32 = 7)
    (he : X.get (g,k) = some ⟨pc,.tc (.commit sp)⟩) :
    TcCommit.target sp rank ≠ some (Iface.kvReadyLoc L c s) := by
  intro ht
  obtain ⟨off,rfl,hp'⟩ := Mma.Export.commit hp hX hF hw he
  obtain ⟨_,ho⟩ := target_one ht
  obtain ⟨_,_,ha⟩ := Loc.mk.inj ho
  change L.sharedBase + (213216 + 8*s.val) = L.sharedBase + off at ha
  have hs := s.isLt
  rcases hp' with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp only [Iface.sReady, Iface.kvEmpty, Iface.oDone, Iface.oFinal] at ha <;> omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
