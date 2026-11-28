-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.Publish
import Kernels.InklingRelDecode.Proof.Protocol.Shared.FinalWitness
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Lemmas.Kernel.Frame
public import Lemmas.Kernel.Safety.HandoffExits
import Lemmas.Step.ExitLast
import Lemmas.Order.WaitOrderEnables
import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Frame

private theorem exclude_exit {Q L m X g h v u pc pc'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (exit : X.get (g,v)=some ⟨pc,.exit⟩)
    (bar : X.get (h,u)=some ⟨pc',.bar 1 none .sync⟩) (exitW : Witness L X (.thread (g,v)) (h,u))
    (cta : g/L.block=h/L.block) : False := by
  obtain ⟨w,pw,wv,last,ord⟩ := Export.exit_final_bar hp hX exit
  have vlen : v<(X.tr g).length := (List.getElem?_eq_some_iff.mp exit).1
  obtain ⟨⟨z,l⟩,eq,wit,ev⟩ := final_witness hp hX last (by omega) ord (h := h) cta.symm
  change z=h at eq
  subst z
  have before : TraceBefore X (h,u) (h,l) := by
    refine ⟨rfl,?_,?_⟩
    · rcases ev with ⟨lastpc,ex⟩|⟨lastpc,mode,sync,hord⟩
      · have length := Execution.exit_last hX (Frame.lt_of_get hX ex) ex
        have lo : u<(X.tr h).length := (List.getElem?_eq_some_iff.mp bar).1
        have ne : u≠l := by rintro rfl; rw [ex] at bar; cases bar
        omega
      · obtain ⟨md,_⟩ := Lib.recorded_bar hX hp.block sync
        subst mode
        exact Export.final_after_b1 hp hX sync hord bar
    · rcases ev with ⟨_,ex⟩|⟨_,_,sync,_⟩
      · exact (List.getElem?_eq_some_iff.mp ex).1
      · exact (List.getElem?_eq_some_iff.mp sync).1
  exact hX.no_exit_cycle exitW ⟨_,false,bar,rfl⟩ before wit ⟨_,false,last,rfl⟩
    ⟨rfl,wv,vlen⟩

/-- Every passed publication barrier counts the corresponding arrival of every
lane in its CTA. An exit counted instead would cycle through the final rendezvous. -/
theorem member_sync {Q L m X g h j pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (sync : X.get (h,j)=some ⟨pc,.bar 1 none .sync⟩)
    (pass : j+1<(X.tr h).length) (cta : g/L.block=h/L.block) :
    ∃ u p, X.get (g,u)=some ⟨p,.bar 1 none .sync⟩ ∧
      ((X.tr g).take u).countP (Execution.isBarId 1) =
        ((X.tr h).take j).countP (Execution.isBarId 1) := by
  rcases (sources hp hX).arrival_or_exit hX (shape hp) (f := (h,j)) sync pass cta
    (participant hp g) with ⟨u,p,md,ev,ord⟩|⟨⟨_,v⟩,_,rfl,ex,wit⟩
  · obtain ⟨_,rfl⟩ := Lib.publication_kind hX hp.block ev
    exact ⟨u,p,ev,ord⟩
  · exact (exclude_exit hp hX ex sync wit cta).elim

/-- Barrier 1 orders every publication generation, including the Epilogue's
exit word before the workers' second dispatch read. -/
theorem publication_handoff {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) :
    Handoff L X (SameCta L)
      (fun i => ((X.tr i.1).take (i.2+1)).countP (Execution.isBarId 1))
      (fun i => ((X.tr i.1).take i.2).countP (Execution.isBarId 1)) := by
  have hand := Handoff.of_bar_exits hX (sources hp hX) (shape hp) (syncs := fun _ => True)
    (fun _ _ _ _ _ _ ev => (Lib.publication_kind hX hp.block ev).2) (by
      rintro ⟨h,j⟩ pc cnt g sync pass cta _ _
      have eq := (Lib.publication_kind hX hp.block sync).1
      subst cnt
      obtain ⟨u,p,get,ord⟩ := member_sync hp hX sync pass cta
      exact ⟨u,p,.sync,get,ord⟩)
  exact fun g h u j same => hand g h u j ⟨same,participant hp g,trivial⟩

/-- A first-round worker read precedes both possible reuses in its CTA. -/
theorem first_read_before_reuse {Q L m X g h j k p r a b bs data}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (read : X.get (g,j)=some ⟨r,.rd a data⟩)
    (first : ((X.tr g).take j).countP (Execution.isBarId 1)=1)
    (store : X.get (h,k)=some ⟨p,.wr b bs⟩) (reuse : p=2250 ∨ p=2848)
    (cta : g/L.block=h/L.block) : baseCausality L X (g,j) (h,k) := by
  obtain done|⟨_,_,_,_,_,exit,bar,_,wit⟩ :=
    read_before_reuse_or_exit hp hX read first store reuse cta
  · exact done
  · exact (exclude_exit hp hX exit bar wit cta).elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
