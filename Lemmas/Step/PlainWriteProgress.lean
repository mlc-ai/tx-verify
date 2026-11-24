-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow

/-- An ordinary non-release store at a released cursor occurs in a maximal execution
if the thread's preceding event carries no pending allocation result-store obligation. -/
theorem plain_write_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {g pos : Nat} (hg : g < L.threads) {a : Acc} {data : List Byte}
    (hPlain : a.release = false)
    {t u dst : TState} {ending : Option TState} (hNext : Next K A L g t u (.write a data dst))
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hNoAllocation : ∀ c r, r ∈ X.tmemHistory c →
      r.own.event L 0 ≠ (g,(X.tr g).length-1))
    (hasm : ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,.wr a data⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,.wr a data⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some dst) ∧
      Run K A L g dst ((X.tr g).drop (pos+1)) ending := by
  let e : Event := ⟨u.pc,.wr a data⟩
  have hStep : EStep K A L g u e (some dst) := ⟨_,hNext.stop,rfl,rfl⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hLe] at hPrefix
    exact hMax.not_grows (plain_counted_extension hMax.1 hg (.inl hStarted) (hRelease hEq)
      hPrefix hNext.steps hStep hPlain hPlain nofun nofun nofun rfl
      (hMax.1.tmemPairResult.snoc_last (fun _ _ _ _ _ c r hr => hNoAllocation c r hr)) hasm)
  rw [List.drop_eq_getElem_cons hLt] at hTail
  obtain ⟨v,⟨he,hr⟩,hRest⟩ := hNext.continuing_event (by rintro ⟨_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hr
  refine ⟨?_,?_,hRest⟩
  · change (X.tr g)[pos]? = some e
    rw [List.getElem?_eq_getElem hLt,he]
  · rw [List.take_succ_eq_append_getElem hLt,he]
    exact hPrefix.snoc hNext.steps hStep

end PTX.Step
