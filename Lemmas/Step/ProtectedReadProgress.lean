-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Read
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Kernel.ReadValue
import Lemmas.Kernel.ProgressDescent

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow PTX.AsyncCopy

/-- A protected launch read at a released cursor is recorded in a maximal execution.
It returns the launch bytes and advances the exact replay boundary. The assumptions'
constraints are asked of the extension given the read's launch sources (`hasm`). -/
theorem protected_read_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {g pos : Nat} (hg : g < L.threads) {a : Acc} {value : Value}
    (hSize : a.size = value.bytes)
    (hInitial : ∀ k < a.size, m (a.loc.at k) = some (some (value.byteAt k)))
    (hFree : ∀ k < a.size, ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers (a.loc.at k))
    {t u : TState} {ending : Option TState} {dst : List (Option Byte) → TState}
    (hNext : Next K A L g t u (.read a dst))
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : NewRead L m X g ⟨u.pc,.rd a (value.toBytes.map some)⟩ (fun _ => none) a
      (value.toBytes.map some) → ∀ q ∈ A, q.wf L m
        (X.snoc g ⟨u.pc,.rd a (value.toBytes.map some)⟩ (fun _ => none))) :
    X.get (g,pos) = some ⟨u.pc,.rd a (value.toBytes.map some)⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some (dst (value.toBytes.map some))) ∧
      Run K A L g (dst (value.toBytes.map some)) ((X.tr g).drop (pos+1)) ending := by
  let bs := value.toBytes.map some
  let e : Event := ⟨u.pc,.rd a bs⟩
  have hBytes : bs.length = a.size := by simp [bs,Value.toBytes,hSize]
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hLe] at hPrefix
    have hRead : NewRead L m X g e (fun _ => none) a bs := by
      refine ⟨hBytes,?_,?_⟩
      · intro k hk c hc
        have hK := hSize ▸ hk
        obtain rfl := Option.some.inj (hc.symm.trans (hInitial k hk))
        simp [bs,Value.toBytes,hK,Execution.initialByte]
      · intro k w dst data hk hWrite hCover _
        exact hFree k hk w dst data hWrite hCover
    have he : EStep K A L g u e (some (dst bs)) := ⟨_,hNext.stop,bs,hBytes,rfl,rfl⟩
    exact hMax.not_grows (read_counted_extension hMax.1 hg hStarted (hRelease hEq)
      hPrefix hNext.steps he hRead (hasm hRead))
  rw [List.drop_eq_getElem_cons hLt] at hTail
  obtain ⟨_,⟨observed,hLength,hEq,hState⟩,hRest⟩ :=
    hNext.continuing_event (by rintro ⟨_,_,_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hState
  have hGet : X.get (g,pos) = some ⟨u.pc,.rd a observed⟩ := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hLt,hEq]
  have hMem : X.MemReads (.thread (g,pos)) a observed := .inl ⟨_,hGet⟩
  have hExact : observed = bs := hMax.1.launch_value hMem hSize hFree hInitial
  subst observed
  refine ⟨hGet,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hLt,hEq]
  exact hPrefix.snoc hNext.steps ⟨_,hNext.stop,bs,hLength,rfl,rfl⟩

end PTX.Step
