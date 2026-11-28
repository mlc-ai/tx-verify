-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Order.ElectOrdinal
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Lib.Elect
import Kernels.InklingRelDecode.Proof.Common.WorkerBalance

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow

/-- At every observed loader election, all lanes have an election at the same PC
with the same leader, instance and number of preceding elections. -/
theorem electionPeers {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g k pc mask inst leader : Nat} (_hp : Pre Q L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (_hf : Follow Q L X)
    (_hw : g % L.block / 32 = 6)
    (he : X.get (g,k) = some ⟨pc, .elect mask inst leader⟩) :
    mask = 4294967295 ∧ ∀ h, SameWarp L g h → ∃ j,
      X.get (h,j) = some ⟨pc, .elect mask inst leader⟩ ∧
      ((X.tr h).take j).countP isElectEv = ((X.tr g).take k).countP isElectEv := by
  have hm := Lib.elect_full hX he
  refine ⟨hm, ?_⟩
  intro h hsame
  have hmem : electMember mask (laneOf L h) := by
    rw [hm]
    have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
    revert hl
    generalize laneOf L h = lane
    revert lane
    decide
  obtain ⟨j, p, p', m, m', label, l, l', hg, hpeer⟩ := ElectOrd.partner hX hsame he hmem
  obtain rfl : p = pc := (Event.mk.inj (Option.some.inj (hg.symm.trans he))).1
  obtain ⟨rfl,rfl,rfl⟩ := Kind.elect.inj (Event.mk.inj (Option.some.inj (hg.symm.trans he))).2
  obtain ⟨rfl,rfl,rfl,_⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hg hpeer hsame
  exact ⟨j, hpeer, (electOrdinal hX (ElectMutual.of_full (fun h => Lib.elect_full hX h))
    hsame hg hpeer).symm⟩

/-- Four full-mask elections separate successful empty-ring polls. -/
theorem poll_elections {Q L m X g k l p ok a sc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hw : g%L.block/32=6)
    (he : X.get (g,k)=some ⟨2374,.wait l p ok a sc⟩) :
    elections X g k = 4*pollRound 2374 ((X.tr g).take k) := by
  obtain ⟨w,x,t,d,n,hs,pc⟩ := loader_state hp hX hf he (fun _ => nofun)
      (by decide : 2344<2374) (by decide : 2374<2422)
  have bal := loader_balance hp hX hf (Frame.lt_of_get hX he) hw (Frame.noUbBefore_of_get hX he) hs
  have only (s : Site) : s.pc=2374 → s=.poll := by
    cases s <;> first | decide | (rename_i j; fin_cases j <;> decide) |
      (rename_i j b; fin_cases j <;> cases b <;> decide)
  rw [only _ pc.symm] at bal
  have ce : n .elect=elections X g k := fcount hs _
  have cr : n (.poll 2374)=pollRound 2374 ((X.tr g).take k) := fcount hs _
  change n .elect+0=_ at bal
  omega

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
