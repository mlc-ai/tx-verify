-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Read
public import Lemmas.Flow.ContinuingEvent
import Lemmas.Protocol.LocalMemory
import Lemmas.Kernel.ProgressDescent
import Lemmas.Order.StageCausalityThread

@[expose] public section

namespace PTX.Step
open PTX PTX.Flow PTX.AsyncCopy

private theorem no_reverse_local_order {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hX : Consistent L K A m X)
    {g i j : Nat} {a dst : Acc} (hi : X.Access (g,i) a true) (hj : X.Access (g,j) dst true)
    (hij : i ≤ j) {loc : Loc} (ha : a.Covers loc) (hb : dst.Covers loc)
    (hLocal : loc.space = .local) :
    ¬ ByteCausality L X loc (.thread (g,j)) (.thread (g,i)) := by
  intro hOrder
  have hBack : baseCausality L X (g,j) (g,i) := by
    cases hOrder with
    | direct h => exact h.resolve_right fun hr => by cases hLocal.symm.trans hr.shared.1
    | commitOperand h => cases hLocal.symm.trans h
  have getOfAccess {e : EvId} {acc : Acc} (h : X.Access e acc true) :
      ∃ event, X.get e = some event := by
    rcases h with ⟨_,_,hFalse⟩ | ⟨_,⟨_,he⟩,_⟩ | ⟨_,_,⟨_,he⟩⟩
    · cases hFalse
    · exact ⟨_,he⟩
    · exact ⟨_,he⟩
  obtain ⟨_,hei⟩ := getOfAccess hi
  have hCycle : Relation.TransGen (stageCausality L X) (.thread (g,j), true)
      (.thread (g,i), true) :=
    (Relation.TransGen.single (stageCausality.of_baseCausality hBack)).tail
      (stageCausality.of_present hei)
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · obtain ⟨_,hej⟩ := getOfAccess hj
    have hFwd := po_of_overlap hi hj rfl hlt ⟨loc,ha,hb⟩
    exact hX.object.cause _ ((hCycle.tail
      (stageCausality.of_baseCausality (.single (.inl hFwd)))).tail
      (stageCausality.of_present hej))
  · exact hX.object.cause _ hCycle

/-- A released thread reads its most recent local write in a maximal execution. -/
theorem local_read_of_maximal {L : Launch} {K : Kernel} {A : List Assumption}
    {m : Mem0} {X : Execution} (hMax : Maximal L K A m X)
    {g pos write : Nat} (hg : g < L.threads)
    {a dst : Acc} {data : List Byte} {bs : List (Option Byte)} (hLocal : a.loc.space = .local)
    (hw : X.Writes (g,write) dst data) (hPrior : write < pos)
    (hSize : bs.length = a.size)
    (hBytes : ∀ k < a.size, dst.Covers (a.loc.at k) ∧
      bs[k]? = some (wbyte dst data (a.loc.at k)))
    (hOwner : ∀ k < a.size, ∀ w d written, X.MemWrites w d written → d.Covers (a.loc.at k) →
      ∃ j, w = .thread (g,j) ∧ X.Access (g,j) d true)
    (hLatest : ∀ k < a.size, ∀ j < pos, ∀ d, X.Access (g,j) d true →
      d.Covers (a.loc.at k) → j ≤ write)
    {t u : TState} {ending : Option TState} {next : List (Option Byte) → TState}
    (hNext : Next K A L g t u (.read a next))
    (hPrefix : Run K A L g {} ((X.tr g).take pos) (some t))
    (hTail : Run K A L g t ((X.tr g).drop pos) ending)
    (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Released L X g)
    (hasm : ∀ q ∈ A, q.wf L m
      (X.snoc g ⟨u.pc,.rd a bs⟩ (fun _ => some (.thread (g,write))))) :
    X.get (g,pos) = some ⟨u.pc,.rd a bs⟩ ∧
      Run K A L g {} ((X.tr g).take (pos+1)) (some (next bs)) ∧
      Run K A L g (next bs) ((X.tr g).drop (pos+1)) ending := by
  let e : Event := ⟨u.pc,.rd a bs⟩
  have hLt : pos < (X.tr g).length := by
    by_contra! hLe
    have hEq := Nat.le_antisymm hBound hLe
    have hStarted : X.tr g ≠ [] := by intro h; rw [h,List.length_nil] at hEq; omega
    rw [List.take_of_length_le hLe] at hPrefix
    have hRead : NewRead L m X g e (fun _ => some (.thread (g,write))) a bs := by
      refine ⟨hSize,fun k hk => ⟨_,_,.inl hw,hBytes k hk⟩,?_⟩
      intro k w d written hk hWrite hCover _
      obtain ⟨j,rfl,hAccess⟩ := hOwner k hk w d written hWrite hCover
      have hj : j < (X.tr g).length := hAccess.lt
      have hStored : X.Access (g,write) dst true := .inr (.inl ⟨_,hw,rfl⟩)
      exact no_reverse_local_order hMax.1 hAccess hStored
        (hLatest k hk j (by omega) d hAccess hCover) hCover (hBytes k hk).1 hLocal
    have he : EStep K A L g u e (some (next bs)) := ⟨_,hNext.stop,bs,hSize,rfl,rfl⟩
    exact hMax.not_grows (read_counted_extension hMax.1 hg hStarted (hRelease hEq)
      hPrefix hNext.steps he hRead hasm)
  rw [List.drop_eq_getElem_cons hLt] at hTail
  obtain ⟨_,⟨observed,hLength,hEq,hState⟩,hRest⟩ :=
    hNext.continuing_event (by rintro ⟨_,_,_,h⟩; cases h) hTail
  obtain rfl := Option.some.inj hState
  have hGet : X.get (g,pos) = some ⟨u.pc,.rd a observed⟩ := by
    change (X.tr g)[pos]? = _
    rw [List.getElem?_eq_getElem hLt,hEq]
  have hExact : observed = bs := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < a.size
    · have hActual := local_read_byte_of_last_write hMax.1 ⟨_,hGet⟩ hw hk (hBytes k hk).1
        hPrior (hOwner k hk) (fun j d ha hc => by
          rcases lt_trichotomy j pos with hj | rfl | hj
          · exact .inl (hLatest k hk j hj d ha hc)
          · rcases ha with ⟨_,_,hf⟩ | ⟨_,⟨_,he⟩,_⟩ | ⟨_,_,⟨_,he⟩⟩
            · cases hf
            · rw [hGet] at he
              cases he
            · rw [hGet] at he
              cases he
          · exact .inr hj)
      exact hActual.trans (hBytes k hk).2.symm
    · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  subst observed
  refine ⟨hGet,?_,hRest⟩
  rw [List.take_succ_eq_append_getElem hLt,hEq]
  exact hPrefix.snoc hNext.steps ⟨_,hNext.stop,bs,hLength,rfl,rfl⟩

end PTX.Step
