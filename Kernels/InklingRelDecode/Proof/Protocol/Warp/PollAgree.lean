-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.WorkerPoll
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollSynced
import Kernels.InklingRelDecode.Proof.Lib.PollMeetExit
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Kernels.InklingRelDecode.Proof.Loader.Export.Coll
import Kernels.InklingRelDecode.Proof.Loader.Export.Mbar
import Kernels.InklingRelDecode.Proof.Mma.Export.Coll
import Kernels.InklingRelDecode.Proof.Mma.Export.Mbar

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g h k j pc p p' : Nat}
  {l l' : Loc} {ok a ok' a' : Bool} {sc sc' : MbarScope}

private theorem ordered (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : SameWarp L g h) (high : 6≤g%L.block/32)
    (ge : X.get (g,k)=some ⟨pc,.wait l p ok a sc⟩)
    (hh : X.get (h,j)=some ⟨pc,.wait l' p' ok' a' sc'⟩)
    (lt : pollRound pc ((X.tr g).take k)<pollRound pc ((X.tr h).take j)) :
    PollBefore L kernel X (g,k) (h,j) := by
  have len : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hh).1
  rcases Export.worker_poll_pc hp hX hf high ge with ⟨ld,rfl⟩|⟨mma,pcs⟩
  · have x := Loader.Export.poll_elections hp hX hf ld ge
    have y := Loader.Export.poll_elections hp hX hf (hw.2 ▸ ld) hh
    exact meet_elect hX (electOrdinal hX (ElectMutual.of_full (fun he => Lib.elect_full hX he)))
      hw ge rfl rfl (by omega) len (fun he => Lib.elect_full hX he)
  · have x := Mma.Export.poll_shuffles hp hX hf mma ge (fun _ => nofun) pcs
    have y := Mma.Export.poll_shuffles hp hX hf (hw.2 ▸ mma) hh (fun _ => nofun) pcs
    apply Lib.meet_poll_shfl hX hw ge _ len
    dsimp only at x y
    rw [hw.1.2.2] at x
    rcases pcs with rfl|rfl <;> simp at x y <;> omega

/-- The worker restriction of PollSynced. A selected branch needs ordering only
when the two lanes observe different objects. -/
public theorem pollAgree (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : SameWarp L g h) (high : 6≤g%L.block/32)
    (ge : X.get (g,k)=some ⟨pc,.wait l p ok a sc⟩)
    (hh : X.get (h,j)=some ⟨pc,.wait l' p' ok' a' sc'⟩)
    (diff : l≠l' ∨ Assumptions.all.any (·.uniPoll (pc+1))=false) :
    PollBefore L kernel X (g,k) (h,j) ∨ PollBefore L kernel X (h,j) (g,k) := by
  rcases Nat.lt_trichotomy (pollRound pc ((X.tr g).take k))
      (pollRound pc ((X.tr h).take j)) with lt|eq|gt
  · exact .inl (ordered hp hX hf hw high ge hh lt)
  · exfalso
    rcases Export.worker_poll_pc hp hX hf high ge with ⟨ld,rfl⟩|⟨mma,pcs⟩
    · have selected : Assumptions.all.any (·.uniPoll (2374+1))=true := by decide +kernel
      have x := (Loader.Export.poll hp hX hf ld (.inl ge)).1
      have y := (Loader.Export.poll hp hX hf (hw.2 ▸ ld) (.inl hh)).1
      simp only [Iface.kvEmpty,hw.1.2.2,eq] at x
      simp only [Iface.kvEmpty] at y
      exact diff.elim (fun ne => ne (x.trans y.symm)) (fun no => by simp [selected] at no)
    · obtain ⟨_,_,x⟩ := Mma.Export.poll hp hX hf mma pcs (.inl ge)
      obtain ⟨_,_,y⟩ := Mma.Export.poll hp hX hf (hw.2 ▸ mma) pcs (.inl hh)
      simp only [Iface.kvReadyLoc,Iface.kvReady,Iface.pReady,hw.1.2.2,eq] at x
      simp only [Iface.kvReadyLoc,Iface.kvReady,Iface.pReady] at y
      have eqObj : l=l' := by
        rcases x with ⟨a,b,_⟩|⟨a,b,_⟩ <;> rcases y with ⟨c,d,_⟩|⟨c,d,_⟩ <;>
          first | exact b.trans d.symm | omega
      have selected : Assumptions.all.any (·.uniPoll (pc+1))=true := by
        rcases pcs with rfl|rfl <;> decide +kernel
      exact diff.elim (fun ne => ne eqObj) (fun no => by simp [selected] at no)
  · exact .inr (ordered hp hX hf hw.symm (hw.2 ▸ high) hh ge gt)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
