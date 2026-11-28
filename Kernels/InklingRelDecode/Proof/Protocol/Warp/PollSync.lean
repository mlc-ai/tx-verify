-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Export.Mbar
public import Kernels.InklingRelDecode.Proof.Protocol.Warp.PollAgree
public import Kernels.InklingRelDecode.Proof.Protocol.Warp.ScoreOrder
import Kernels.InklingRelDecode.Proof.Lib.StaticPoll

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
open PTX PTX.Flow MbarRow

private theorem poll_object {Q L X g k pc l q ok a sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨pc,.wait l q ok a sc⟩) :
    (pc=1257 → l=loc L g (Iface.sReady (slot2 (roundAt X g k 1257)))) ∧
    (pc=2239 → l=loc L g Iface.oDone) ∧ (pc=2565 → l=loc L g Iface.oFinal) := by
  have use := mbar_use rows hg he (show Frame.MbarOf ⟨pc,.wait l q ok a sc⟩ l from rfl)
  refine ⟨fun h => ?_,fun h => ?_,fun h => ?_⟩ <;> subst h <;>
    rcases use with ⟨_,u⟩|⟨_,u⟩|⟨_,u⟩|⟨_,u⟩|⟨_,u⟩|⟨_,u⟩|⟨_,u⟩ <;> cases u <;>
    first | assumption | omega | (exfalso; simp_all [Arrive,Issue])

/-- **Every pair of polls of two lanes of a warp is ordered when it needs to be**: the worker
warps by `pollAgree`, the Softmax warps' score poll by the shuffles between rounds, and the
done and final polls name one object, which the poll-agree assumption exempts. -/
public theorem poll_synced {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X) :
    PollSynced L kernel Assumptions.all X := by
  intro g h k k' pc l l' p p' ok ok' acq acq' sc sc' hg hh hgh hw he he' hpb hd
  have cta : g/L.block=h/L.block := hw.1.2.2
  have sites := (Lib.poll_site hX he).1
  simp only [Lib.pollSites,List.mem_cons,List.not_mem_nil,or_false] at sites
  have place := rows.place hg he (show Frame.MbarOf ⟨pc,.wait l p ok acq sc⟩ l from rfl)
  by_cases wk : pc=2374 ∨ pc=2462 ∨ pc=2510
  · have high : 6≤g%L.block/32 := by
      rcases place with a|a|a|a|a|a|a <;>
        simp only [StartupAt,PrologueAt,SoftmaxAt,EpilogueAt,DispatchAt,LoaderAt,MmaAt] at a <;>
        omega
    exact pollAgree hp hX hf hw high he he' hd
  have pcs : pc=1257 ∨ pc=2239 ∨ pc=2565 := by omega
  have same {n : Nat} (h1 : l=loc L g n) (h2 : l'=loc L h n) : l=l' := by
    rw [h1,h2]; simp only [loc,cta]
  have selected : Assumptions.all.any (·.uniPoll (pc+1))=true := by
    rcases pcs with rfl|rfl|rfl <;> decide +kernel
  have close (eq : l=l') : PollBefore L kernel X (g,k) (h,k') ∨
      PollBefore L kernel X (h,k') (g,k) := by
    rcases hd with ne|no
    · exact (ne eq).elim
    · rw [selected] at no; cases no
  rcases pcs with rfl|rfl|rfl
  · rcases Nat.lt_trichotomy (pollRound 1257 ((X.tr g).take k))
        (pollRound 1257 ((X.tr h).take k')) with lt|eq|gt
    · exact .inl (score_ordered hp hX hf hw he he' lt)
    · have o1 := (poll_object rows hg he).1 rfl
      have o2 := (poll_object rows hh he').1 rfl
      have r : roundAt X g k 1257=roundAt X h k' 1257 := eq
      rw [r] at o1
      exact close (same o1 o2)
    · exact .inr (score_ordered hp hX hf hw.symm he' he gt)
  · exact close (same ((poll_object rows hg he).2.1 rfl) ((poll_object rows hh he').2.1 rfl))
  · exact close (same ((poll_object rows hg he).2.2 rfl) ((poll_object rows hh he').2.2 rfl))

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
