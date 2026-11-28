-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
public import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
public import Lemmas.Protocol.NotifyBlocker
public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.SingleTmaRing.Faults
import Kernels.InklingRelDecode.Proof.Protocol.KV.Reuse
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched PTX.MbarRing
open PTX.MBarrier hiding okPolls

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A nonzero phase requires a counted notification. Its reuse path implies a prior wait
even when the very first empty poll of a fresh slot has parity one. -/
private theorem first_empty {l y g δ} (hX : Consistent L kernel Assumptions.all m X)
    (o : Notify.Obj X l y l δ) {st : State} (hs : stateBefore (X.objects l)
      (X.objects l).length = some st) (hpos : 0 < st.phase)
    (reach : ∀ x ∈ Notify.S X l y l,
      Relation.TransGen (DepStep L kernel X) (.thread (g,Poll.nth X l g 0),true)
        (Notify.it X l y l x.2,false)) : 0 < okPolls l (X.tr g) := by
  have hc := o.units_eq_phase hX hs
  rw [o.units_eq_card] at hc
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (hc.symm ▸ hpos)
  obtain ⟨_,hk'⟩ := Finset.mem_filter.mp hk
  cases hr : (X.objects l)[k]? with
  | none => rw [hr] at hk'; cases hk'
  | some r =>
    rw [hr,Option.any_some] at hk'
    obtain ⟨hf,_,_,ha⟩ := countedArrive_iff.mp hk'
    obtain ⟨x,hx,_⟩ := o.rec_S hr hf ha
    exact Poll.nth_present.mp (Unit.present_of_path (reach x hx))

theorem empty_blk (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hu : ¬ HasUb X) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (hi : Mbar.InitRows L X) (_won : WonCommit L X)
    (words : RoleBytes L X) {g l q sc}
    (hn : NextEv L kernel Assumptions.all m X g ⟨2374,.wait l q false true sc⟩) :
    WaitBlk (schedule Q L) X g l q := by
  obtain ⟨s,rfl,hq⟩ := next_slot (r := .empty) rows hn
  let c := g / L.block
  let l := Ring.empty.obj L c s
  have hg := hn.lt
  have hc : c < L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  have hw : Waiting L m X .empty c s g := ⟨rfl,q,sc,hn⟩
  have o := empty_obj hp hX hf (rows X hX) hi c s
  have ring := ready_slot hp hX hf (rows X hX) hi hc s
  obtain ⟨st,hst⟩ := Unit.final_of_init hX ring.empty_init ring.empty_noInval
    (wait_published hp hX hw)
  refine ⟨st,hst,fun hpar => ?_⟩
  have hδ := ring.δ_le
  change preload Q L c s ≤ 1 at hδ
  obtain ⟨Y,hY,_,next⟩ := id hn
  obtain ⟨_,_,_,warp,_,_⟩ := wait_info (r := .empty) (rows Y hY) hg next
  have path := empty_reuse hp hX hf (rows X hX) hc hg rfl warp ring slot_fits o
  change ∀ x ∈ Notify.S X l (leader L X c 7) l, ∀ j, j+preload Q L c s≤x.2 → _ at path
  have hy := leader_warp (X := X) hp hc (by decide : 7 < 8)
  have htgt : ∀ {k pc sp}, X.get (leader L X c 7,k) = some ⟨pc,.tc (.commit sp)⟩ →
      sp.mbar = l → ∃ rank, TcCommit.target sp rank = some l := by
    intro k pc sp he hl
    obtain ⟨off,rfl,_⟩ := Mma.Export.commit hp hX hf hy.2.2 he
    refine ⟨0,?_⟩
    rw [← hl]
    simp [TcCommit.target]
  change q%2 = (okPolls l (X.tr g) + (1-preload Q L c s))%2 at hq
  have hpar' := hpar.trans hq
  by_cases hle : 1 - preload Q L c s ≤ okPolls l (X.tr g)
  · have hreach : Notify.Reach L kernel Assumptions.all X l (leader L X c 7) l
        (1-preload Q L c s) g := by
      intro x hx j hj
      apply path x hx
      omega
    obtain ⟨hph,hshort | hmissing⟩ := o.blocker hX hreach
      (fun _ hr => SingleTmaRing.fault_free hX ring slot_fits (.inr rfl) hr) htgt hst hpar' hle
    · change st.phase ≤ okPolls l (X.tr g) - (1-preload Q L c s) at hph
      change (X.tr _).countP (commitsTo l) ≤ st.phase at hshort
      obtain ⟨_,_,lag⟩ := empty_lag hp hX hf words (.of_noUb hu) hc rows s
      exact lag.blk hX hu hg hw (poll_floor hp hf (by decide) hn).1 rfl hy.1
        (congrArg L.clusterOfCta hy.2.1) (by
          change (X.tr _).countP (commitsTo l) + _ ≤ okPolls l _; omega)
    · exact .inl ⟨.commit,.inl rfl,hmissing⟩
  · have hp0 : preload Q L c s = 0 := by omega
    have hpos : 0 < st.phase := by omega
    exact False.elim (by
      have := first_empty hX o hst hpos (g := g) fun x hx => path x hx 0 (by omega)
      change 0 < okPolls l (X.tr g) at this
      omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
