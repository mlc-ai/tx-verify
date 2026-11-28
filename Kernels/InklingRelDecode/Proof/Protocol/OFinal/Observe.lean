-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Lag
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Lemmas.Protocol.NotifyBlocker
import Lemmas.Protocol.UnitReachBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
open PTX PTX.Flow PTX.Sched PTX.MbarRing MbarRow

theorem final_wait {Q L X g k l q ok ac sc} (rows : MbarRows Q L X) (hg : g<L.threads)
    (he : X.get (g,k)=some ⟨2565,.wait l q ok ac sc⟩) :
    l=obj L (g/L.block) ∧ q=0 ∧ ac=true ∧ sc=.cta := by
  have region := rows.place hg he (l := l) rfl
  have epi : EpilogueAt L g 2565 := by
    simpa [StartupAt,PrologueAt,SoftmaxAt,DispatchAt,LoaderAt,MmaAt] using region
  cases rows.epilogue hg he epi (l := l) rfl with
  | finalWait _ addr wait =>
    obtain ⟨_,kind⟩ := wait
    obtain ⟨-,hq,-,hac,hsc⟩ := Kind.wait.inj kind
    exact ⟨addr,hq,hac,hsc⟩

/-- The final commit has no earlier commit, so no poll precedes it in the dependency order. -/
theorem final_reach {Q L m X c h} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) :
    Notify.Reach L kernel Assumptions.all X (obj L c) (KV.leader L X c 7) (obj L c) 0 h := by
  have o := history (c := c) hp hX hf rows init
  intro x hx j lt
  obtain ⟨_,_,_,he,addr,_,ord⟩ := o.S_rec hx
  have z := commit_zero hp hX hf rows he addr
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.OFinal
