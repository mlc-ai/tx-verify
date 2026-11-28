-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Loader.Shape
import Kernels.InklingRelDecode.Proof.Lib.IterRange
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.NotBulk
import Lemmas.Flow.Ledger

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow

/-- Every observed loader arrival supplies the full eight-copy byte credit at CTA scope. -/
theorem arriveCredit {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g k tx count : Nat} {obj : Loc} {release : Bool} {scope : MbarScope}
    (_hp : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hf : Follow Q L X) (_hw : g % L.block / 32 = 6)
    (he : X.get (g,k) = some ⟨2378, .arrive obj tx count release scope⟩) :
    tx = 65536 ∧ count = 1 ∧ release = true ∧ scope = .cta := by
  obtain ⟨_, bad⟩ | ⟨t, ins, o, _, hc, fire⟩ := get_source hX he
  · contradiction
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2378)
  cases hm : mbarLoc L g t 580 0 with
  | error f =>
    change Fires 2378 (eventTmpl _ L g t (.mbarArrive 580 0 (.imm 65536) (.imm 1)
      false true .cta none)) _ o at fire
    simp [eventTmpl, tmaTmpl, hm, widenMbarScope, ofExec, Fires, bind, Except.bind] at fire
  | ok m =>
    have hk := fires_arrive_exact (by rfl) hm (by rfl) (by rfl) fire
    obtain ⟨_, ht, hn, hr, hs⟩ := Kind.arrive.inj hk
    exact ⟨ht, hn, hr, hs⟩

private theorem barrier_pc (s : Site) :
    (s.pc = 2374 → s = .poll) ∧ (s.pc = 2378 → s = .arrive) := by
  cases s <;> first | decide | (rename_i p; fin_cases p <;> decide) |
    (rename_i p b; fin_cases p <;> cases b <;> decide)

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The first empty poll starts at the first block that the prologue did not preload.
Each subsequent successful poll advances the slot and every third poll toggles the parity. -/
theorem poll (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : g % L.block / 32 = 6) {l : Loc} {q : Nat} {ok acq : Bool}
    {sc : MbarScope} (he : Occurs L X g k ⟨2374, .wait l q ok acq sc⟩) :
    let j := Iface.preloadCount Q L (g / L.block) + pollRound 2374 ((X.tr g).take k)
    l = ⟨.shared, g / L.block, L.sharedBase + Iface.kvEmpty ⟨j % 3, by omega⟩⟩ ∧
      q = 1 - j / 3 % 2 ∧ acq = true ∧ sc = .cta := by
  obtain ⟨w,x,⟨s,i,n,a,b⟩,t,ins,o,hat,hpc,hc,fire,hr,hcount,_⟩ :=
    loader_occ hp hX hf hw he (fun _ => nofun) (by change 2344 < 2374; decide)
      (by change 2374 < 2422; decide)
  obtain rfl := (barrier_pc s).1 hpc.symm
  have hn := Lib.iter_range hp (he.lt hX)
  obtain ⟨j,hlo,hhi,rfl,_⟩ := (ref_loop hr (by rfl))
  change j < iterCount Q L (g / L.block) at hhi
  change iterCount Q L (g / L.block) < 2^31 at hn
  have hj : (bits (PTX.Proof.b32 j)).toNat = j := by
    rw [bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨_,hk⟩ := poll_slot hp (by rw [hj]; omega) hat hc fire
  obtain ⟨hl,hq,_,ha,hsc⟩ := Kind.wait.inj hk
  change pollRound 2374 _ = (bits (PTX.Proof.b32 j)).toNat - _ at hcount
  simp only [Iface.kvEmpty, hj] at hcount hl hq
  dsimp only
  simp only [Iface.kvEmpty, hcount, Nat.add_sub_of_le hlo]
  exact ⟨hl,hq,ha,hsc⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
