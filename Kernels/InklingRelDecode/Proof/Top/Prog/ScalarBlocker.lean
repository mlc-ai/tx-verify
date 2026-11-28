-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.ScalarLag
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.CreditDef
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarHistory
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Protocol.OFinal.Obj
import Lemmas.Protocol.NotifyBlocker

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.Sched PTX.MbarRing MbarRow

private theorem init_slot (o : Object) :
    ∃ j : Fin 12, initOffset j=o.offset := by
  cases o with
  | score s => fin_cases s <;> first | exact ⟨6,rfl⟩ | exact ⟨8,rfl⟩
  | prob s => fin_cases s <;> first | exact ⟨7,rfl⟩ | exact ⟨9,rfl⟩
  | done => exact ⟨10,rfl⟩

/-- Once per-slot credit is known, a failed score or done poll is blocked by
the issuing lane or by an undelivered commit. No causal path premise is needed. -/
theorem notify_blocker {Q L m X c g q sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : ¬HasUb X) (rows : ∀ Y, Consistent L kernel Assumptions.all m Y →
      MbarRows Q L Y) (init : Mbar.InitRows L X) (words : RoleBytes L X) (o : Object)
    (cm : (∃ s,o=.score s) ∨ o=.done) (credit : Credit L m X o)
    (free : ∀ r ∈ X.objects (o.loc L c), r.fault=none)
    (hn : NextEv L kernel Assumptions.all m X g ⟨o.pc,.wait (o.loc L c) q false true sc⟩) :
    WaitBlk (schedule Q L) X g (o.loc L c) q := by
  have hg := hn.lt
  obtain ⟨Y,hY,pre,get⟩ := id hn
  have cta := (wait_obj (rows Y hY) hg get).1
  have hc : c<L.grid := cta ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have after : Export.afterInit o.pc := by
    rcases cm with ⟨s,rfl⟩|rfl <;> simp only [Object.pc] <;> decide
  obtain ⟨idx,off⟩ := init_slot o
  have live := Mbar.next_published hp hX hn after idx
  simp only [MbarRow.loc,cta,off] at live
  have obj := notification hp hX hf (rows X hX) init (c := c) cm
  obtain ⟨st,state⟩ := Unit.final_of_init hX obj.init obj.noInval live
  refine ⟨st,state,fun blocked => ?_⟩
  let y := KV.leader L X c 7
  let l := o.loc L c
  have wait : Waiting L m X o c g := ⟨q,sc,hn⟩
  have cap := credit c g wait
  have par := parity (rows Y hY) hg get
  rw [pre] at par
  have phases := obj.phase_le_commit_count hX state
  change st.phase≤(X.tr y).countP (commitsTo l) at phases
  change st.phase%2=q%2 at blocked
  change q=okPolls l (X.tr g)%2 at par
  change (X.tr y).countP (commitsTo l)≤okPolls l (X.tr g)+1 at cap
  have le : st.phase≤okPolls l (X.tr g) := by omega
  classical
  by_cases all : ∀ i s rank loc, X.Commit i s → TcCommit.target s rank=some loc →
      rank ∈ X.tcNotified i
  · have lower := Notify.Obj.phase_ge_of_records hX obj state le_rfl (fun _ ht =>
      Notify.Obj.notified_rec hX free (fun he a => ⟨0,OFinal.target_zero hp hX hf he a⟩) all ht)
    obtain ⟨τ,clock⟩ := lag hp hX hf words hu hc rows o
    obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
    have who : y=o.producer L X c := by rcases cm with ⟨s,rfl⟩|rfl <;> rfl
    have early : 1199 < o.pc := by rcases cm with ⟨s,rfl⟩|rfl <;> simp only [Object.pc] <;> decide
    apply clock.blk hX hu hg wait (poll_floor hp hf (by omega) hn).1 who hy
      (congrArg L.clusterOfCta (cy.trans cta.symm))
    have equal : o.issue l=commitsTo l := by rcases cm with ⟨s,rfl⟩|rfl <;> rfl
    rw [equal]
    exact (Nat.add_zero _).le.trans (lower.trans le)
  · exact .inl ⟨.commit,.inl rfl,all⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
