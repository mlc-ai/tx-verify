-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringKeyCopyLength
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringKeyCopyLength

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmKeyMaskPc (group : Fin 16) : Nat :=
  warmKShufflePc group - if group.val = 0 ∨ group.val = 8 then 2 else 1

private theorem warmKeyMaskPc_eq (group : Fin 16) :
    warmKeyMaskPc group = keyComparePc false group := by fin_cases group <;> decide

def warmKeyPairPredicate (group : Fin 16) : Nat × Value := (169+group.val,.pred true)

set_option maxRecDepth 4096 in
/-- The live warm K row uses the decoded signed predicate for this vector pair. -/
theorem warmKeyMaskOfReached {l : Launch} {X : Execution} {g shuffles votes : Nat}
    (group : Fin 16) (res : Nat → Nat) (hLive : ∀ lane < 32, 8*group.val < res lane)
    (hWidth : ∀ lane < 32, res lane < 2^31)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hKeep : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ 169+group.val)
    (cur : SchedulerWarpReached l X g (warmKeyMaskPc group)
      (fun lane => (1997,b32 (res lane))::F lane) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmKeyMaskPc group+1)
        (fun lane => warmKeyPairPredicate group :: (1997,b32 (res lane))::F lane)
        shuffles votes ends, done.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let pc := warmKeyMaskPc group
  let carry := (1997,b32 (res lane))::F lane
  have he : kernel.code[pc]? = some ⟨none,
      signedCompareOp .gt (169+group.val) 1997 (8*group.val)⟩ := by
    change kernel.code[warmKeyMaskPc group]? = _
    rw [warmKeyMaskPc_eq]
    exact compareCode false group
  have hCore : Seg kernel [] l t 1 pc [(1997,b32 (res lane))]
      (pc+1) [warmKeyPairPredicate group] :=
    liveKeyCompareCore he (hLive lane hl) (hWidth lane hl)
  have hLo : 174 ≤ pc := by fin_cases group <;> decide
  have hHi : pc+1 ≤ 1906 := by fin_cases group <;> decide
  have hAudit : ((kernel.code.drop pc).take 1).all
      (fun i => (carry.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hCode : (kernel.code.drop pc)[0]? = some ⟨none,
        signedCompareOp .gt (169+group.val) 1997 (8*group.val)⟩ := by
      rw [List.getElem?_drop,Nat.add_zero]
      exact he
    have hAs : ins = ⟨none,signedCompareOp .gt (169+group.val) 1997 (8*group.val)⟩ := by
      obtain ⟨i,hi,hiGet⟩ := List.mem_iff_getElem.mp hm
      have hIdx : i < 1 := by
        rw [List.length_take] at hi
        omega
      have hi0 : i = 0 := by omega
      subst i
      have h := List.getElem?_eq_getElem hi
      rw [List.getElem?_take_of_lt (by decide),hCode,hiGet] at h
      exact (Option.some.inj h).symm
    rw [hAs]
    apply List.all_eq_true.mpr
    intro r hm
    obtain ⟨pair,hPair,hr⟩ := List.mem_map.mp hm
    have hp : pair.1 ≠ 169+group.val := by
      rcases List.mem_cons.mp hPair with rfl | hPair
      · have hPair := group.isLt
        simp only
        omega
      · exact hKeep lane hl pair hPair
    simp [signedCompareOp,writesRegs,← hr,hp]
  have hs := cur.checkpoint lane hl
  have hAt : At (cur.state lane) pc ([(1997,b32 (res lane))]++carry) :=
    hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2⟩
  obtain ⟨v,hv,hV⟩ := straightFrame hLo hHi hAudit rfl hCore hAt
  exact ⟨v,run_rtg hv,hV⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
