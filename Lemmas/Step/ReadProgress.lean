-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.ReadSource
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow PTX.AsyncCopy

/-- A released ordinary read at a maximal frontier must already be recorded.
Its actual bytes determine the returned cursor and its remaining trace. -/
theorem readSourceOfMaximal {L : Launch} {K : Kernel} {A : List Assumption} {m : Mem0}
    {X : Execution} (hMax : Maximal L K A m X) (hSync : SyncGuarded L K X)
    {g pos : Nat} (hg : g < L.threads) {a : Acc} {dst : List (Option Byte) → TState}
    {t u : TState} {ending : Option TState}
    (hNext : Next K A L g t u (.read a dst))
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ bs r, (∀ e, NewRead L m X g e r a bs) →
      ∀ q ∈ A, q.wf L m (X.snoc g ⟨u.pc,.rd a bs⟩ r)) :
    ∃ bs, X.get (g,pos) = some ⟨u.pc,.rd a bs⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some (dst bs)) ∧
      Run K A L g (dst bs) ((X.tr g).drop (pos+1)) ending := by
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hEq := hBound.antisymm hLe
    have hStart : X.tr g ≠ [] := by
      intro h
      rw [h,List.length_nil] at hEq
      omega
    rw [List.take_of_length_le hLe] at hPrefix
    exact hMax.not_grows (read_source_counted_extension hMax.1 hg hStart (hRelease hEq)
      hPrefix hNext.steps hNext.stop hasm hSync)
  rw [List.drop_eq_getElem_cons hLt] at hTail
  obtain ⟨_,⟨bytes,hLength,hEvent,hState⟩,hRest⟩ :=
    hNext.continuing_event (by rintro ⟨_,_,_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hState
  have hGet : X.get (g,pos) = some ⟨u.pc,.rd a bytes⟩ := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hLt,hEvent]
  refine ⟨bytes,hGet,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hLt,hEvent]
  exact hPrefix.snoc hNext.steps ⟨_,hNext.stop,bytes,hLength,rfl,rfl⟩

end PTX.Step
