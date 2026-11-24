-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedPublicationPositions
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow Thread.Scores

noncomputable section

private theorem countOutside {X : Execution} {g j : Nat} (mark : Event → Bool) {length : Nat}
    (hAt : ∀ k < length, ∃ e, X.get (g,j+k) = some e ∧ mark e = false) :
    ((X.tr g).take (j+length)).countP mark = ((X.tr g).take j).countP mark := by
  induction length with
  | zero => rfl
  | succ n ih =>
    obtain ⟨e,hGet,hNo⟩ := hAt n (Nat.lt_succ_self _)
    exact (countP_take_succ_false hGet hNo).trans (ih (fun k hk => hAt k (Nat.lt_succ_of_lt hk)))

variable {l : Launch} {X : Execution} {g start : Nat} (stage : Fin 2) (weights : Nat → ℝ)
    (hLoads : ∀ q : Fin 4, ∃ values, X.get (g,start+2*q.val) =
      some ⟨scorePc .unbiased q,.tc (.ld (scoreAddress l g stage q) values .s32x32b)⟩)
    (hWaits : ∀ q : Fin 4, X.get (g,start+2*q.val+1) = some ⟨scorePc .unbiased q,.tc .waitLd⟩)
    {loc : Acc} {data : List Byte} {wid : Nat}
    (hStats : X.get (g,start+8) = some ⟨6890,.wr loc data⟩)
    (hNotice : X.get (g,start+9) = some ⟨6891,.bar wid (some 64) .arrive⟩)
    (hProb : ∀ k : Fin (Repeated.probabilityEvents .unbiased l g stage weights).length,
      X.get (g,start+10+k.val) = (Repeated.probabilityEvents .unbiased l g stage weights)[k.val]?)
include stage weights hLoads hWaits hStats hNotice hProb

/-- The next early probability credit belongs to the same visit as the actual
score loads, because the intervening trace contains only loads, statistics writes,
probability stores, and their local completion waits. -/
theorem plainPublicationCountsWithStatistics :
    (probabilityOrdinal l X (g/l.block) stage 0 (g,start+14) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,start)) ∧
    (∀ q : Fin 4,
      okPolls (scoreReadyObject l (g/l.block) stage)
        ((X.tr g).take (start+10+Repeated.unbiased.probabilityStoreOffset q)) =
      okPolls (scoreReadyObject l (g/l.block) stage) ((X.tr g).take start)) ∧
    probabilityOrdinal l X (g/l.block) stage 0 (g,start+8) =
      probabilityOrdinal l X (g/l.block) stage 0 (g,start) := by
  let target := probabilityObject l (g/l.block) stage 0
  let ready := scoreReadyObject l (g/l.block) stage
  have hLoad (q : Fin 4) : ∃ e, X.get (g,start+(2*q.val)) = some e ∧
      okPoll ready e = false ∧ arrivesOn target e = false := by
    obtain ⟨values,h⟩ := hLoads q
    exact ⟨_,h,rfl,rfl⟩
  have hWait (q : Fin 4) : ∃ e, X.get (g,start+(2*q.val+1)) = some e ∧
      okPoll ready e = false ∧ arrivesOn target e = false := by
    exact ⟨_,by simpa only [Nat.add_assoc] using hWaits q,rfl,rfl⟩
  have hPrefix : ∀ k < 16, ∃ e, X.get (g,start+k) = some e ∧
      okPoll ready e = false ∧ (k < 14 → arrivesOn target e = false) := by
    intro k hk
    interval_cases k
    · obtain ⟨e,h,hP,hA⟩ := hLoad 0
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hWait 0
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hLoad 1
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hWait 1
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hLoad 2
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hWait 2
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hLoad 3
      exact ⟨e,h,hP,fun _ => hA⟩
    · obtain ⟨e,h,hP,hA⟩ := hWait 3
      exact ⟨e,h,hP,fun _ => hA⟩
    · exact ⟨_,hStats,rfl,fun _ => rfl⟩
    · exact ⟨_,hNotice,rfl,fun _ => rfl⟩
    · exact ⟨_,hProb ⟨0,by change 0<6; decide⟩,rfl,fun _ => rfl⟩
    · exact ⟨_,hProb ⟨1,by change 1<6; decide⟩,rfl,fun _ => rfl⟩
    · exact ⟨_,hProb ⟨2,by change 2<6; decide⟩,rfl,fun _ => rfl⟩
    · exact ⟨_,hProb ⟨3,by change 3<6; decide⟩,rfl,fun _ => rfl⟩
    · exact ⟨_,hProb ⟨4,by change 4<6; decide⟩,rfl,fun h => by omega⟩
    · exact ⟨_,hProb ⟨5,by change 5<6; decide⟩,rfl,fun h => by omega⟩
  refine ⟨countOutside (arrivesOn target) (length := 14) (fun k hk => ?_),?_,?_⟩
  · obtain ⟨e,h,_,hA⟩ := hPrefix k (by omega)
    exact ⟨e,h,hA hk⟩
  · intro q
    have hBound : 10+Repeated.unbiased.probabilityStoreOffset q ≤ 16 := by
      fin_cases q <;> decide
    rw [Nat.add_assoc]
    exact countOutside (okPoll ready) (fun k hk => by
      obtain ⟨e,h,hP,_⟩ := hPrefix k (by omega)
      exact ⟨e,h,hP⟩)
  · exact countOutside (arrivesOn target) (length := 8) (fun k hk => by
      obtain ⟨e,h,_,hA⟩ := hPrefix k (by omega)
      exact ⟨e,h,hA (by omega)⟩)

end
end PTX.Kernels.TmlFa4Fwd.Softmax
