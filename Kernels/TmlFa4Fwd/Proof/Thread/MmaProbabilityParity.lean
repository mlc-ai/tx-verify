-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.MmaProbabilityCursor
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Proof.MmaGeometry
import Kernels.TmlFa4Fwd.Proof.MbarSafety
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

private def slot (stage packet : Fin 2) : Fin 4 :=
  ⟨2 * stage.val + packet.val, by have := stage.isLt; have := packet.isLt; omega⟩

private theorem waitHeads (stage packet : Fin 2) :
    probabilityWaitSites stage packet = [probabilityPc (slot stage packet) false,
      probabilityPc (slot stage packet) true] := by
  fin_cases stage <;> fin_cases packet <;> decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem waitHeadRole (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) {which : Fin 4} {tail : Bool}
    (hPc : e.pc = probabilityPc which tail) : warpIndex l g = 12 := by
  have hRange : 2297 ≤ e.pc ∧ e.pc < 2768 := by rw [hPc]; fin_cases which <;> cases tail <;> decide
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  rcases roleBodyPcOfEvent hp hX he (by omega) hHint with h | h
  · omega
  · split_ifs at h <;> omega

private theorem markAt {which : Fin 4} {e : Event} {q : Nat}
    (h : probabilityMark which e = some q) :
    e.pc = probabilityPc which false ∨ e.pc = probabilityPc which true := by
  unfold probabilityMark at h
  split at h
  · split at h <;> simp_all
  · cases h

private theorem probabilityRawParity (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (he : X.get (g,j) = some e) {which : Fin 4} {q : Nat}
    (hMark : probabilityMark which e = some q) :
    warpIndex l g = 12 ∧ ProbabilityAlternates 0 ((X.tr g).filterMap (probabilityMark which)) := by
  have hSite := markAt hMark
  have hWarp : warpIndex l g = 12 := hSite.elim (waitHeadRole hp hX he) (waitHeadRole hp hX he)
  have late {i : Nat} {ev : Event} {q : Nat}
      (hEv : X.get (g,i) = some ev) (hMark : probabilityMark which ev = some q) :
      ∃ s o, 5 ≤ i ∧ At s 174 [(1062, b32 12), (2535, b32 l.sharedBase)] ∧
        Run kernel Assumptions.all l g s ((X.tr g).drop 5) o := by
    have hb (b : Bool) : 173 < probabilityPc which b := by fin_cases which <;> cases b <;> decide
    have hLate : 173 < ev.pc := (markAt hMark).elim (fun h => h ▸ hb false) (fun h => h ▸ hb true)
    obtain ⟨t, o, hi, ht, hRun⟩ := nonzeroCommonPrefixOfLateEvent hp hX
      (event_thread_lt hX hEv) (by rw [hWarp]; decide) hEv hLate
    exact ⟨t, o, hi, ht.mono ⟨hWarp ▸ ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩, hRun⟩
  obtain ⟨t, o, hj, ht, hRun⟩ := late he hMark
  have hNonempty : (X.tr g).drop 5 ≠ [] := by
    intro hn
    have hLen := List.drop_eq_nil_iff.mp hn
    have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega
  obtain ⟨u, _, hHint, hu, hBody⟩ := firstRegisterHintFromCommon hp (event_thread_lt hX he)
    (⟨12, by decide⟩ : Fin 16) ht hRun hNonempty
  have hPrefix : ((X.tr g).take 6).filterMap (probabilityMark which) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro prior hMem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hMem
    have hBounds := hk
    rw [List.length_take] at hBounds
    have hkTrace : k < (X.tr g).length := by omega
    rw [List.getElem_take]
    have hGet : X.get (g,k) = some (X.tr g)[k] := List.getElem?_eq_getElem hkTrace
    cases hM : probabilityMark which (X.tr g)[k] with
    | none => rfl
    | some q =>
      obtain ⟨_, _, hk', _, _⟩ := late hGet hM
      have hK : k = 5 := by omega
      subst k
      rw [Option.some.inj (hGet.symm.trans hHint)] at hM
      have hNo : ∀ i : Fin 4, registerHintPc (⟨12, by decide⟩ : Fin 16) ≠ probabilityPc i false ∧
          registerHintPc (⟨12, by decide⟩ : Fin 16) ≠ probabilityPc i true := by decide
      exact ((markAt hM).elim (hNo which).1 (hNo which).2).elim
  obtain ⟨visits, hWalk⟩ := walkFromRun hBody
  have hEntry : At u 1908 (readyFrame l) :=
    hu.mono ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.1, trivial⟩
  refine ⟨hWarp, ?_⟩
  rw [← List.take_append_drop 6 (X.tr g), List.filterMap_append, hPrefix, List.nil_append]
  exact probabilityAlternatesFromEntry hp which hEntry hWalk

private theorem probabilityMarkMatches (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j cta : Nat} (stage packet : Fin 2)
    (hCta : g / l.block = cta) {e : Event} (he : X.get (g,j) = some e) :
    (probabilityMark (slot stage packet) e).isSome =
      okPoll (probabilityObject l cta stage packet) e := by
  obtain ⟨source, kind⟩ := e
  cases kind <;> try rfl
  case wait target q ok acq scope =>
    cases ok <;> try rfl
    let obj := probabilityObject l cta stage packet
    have hIff : target = obj ↔ source ∈ probabilityWaitSites stage packet := by
      constructor
      · intro hLoc
        subst target
        exact (probabilityWaitSite hp hX stage packet he).2
      · intro hSite
        have hAll : ∀ (s b : Fin 2) k, k ∈ probabilityWaitSites s b →
            k ∈ [2141, 2145, 2210, 2297, 2335, 2419, 2450, 2548, 2586, 2595, 2626] ∧
            fixedMmaWaitOffset k = 96 + 8 * s.val + 16 * b.val := by
          intro s b
          fin_cases s <;> fin_cases b <;> intro k hk <;>
            simp [probabilityWaitSites] at hk <;> rcases hk with rfl | rfl <;> decide
        obtain ⟨hFixed, hOffset⟩ := hAll stage packet source hSite
        rw [mmaFixedWaitAddress hp hX he hFixed, hOffset, hCta]
        rfl
    rw [waitHeads] at hIff
    simp only [probabilityMark, okPoll, sourceWaitSuccess,
      List.mem_cons, List.not_mem_nil, or_false] at hIff ⊢
    change (if source = probabilityPc (slot stage packet) false ∨
      source = probabilityPc (slot stage packet) true then some q else none).isSome =
      decide (target = obj)
    by_cases hLoc : target = obj
    · simp [hLoc, hIff.mp hLoc]
    · simp [hLoc, mt hIff.mpr hLoc]

private theorem probabilityParityAt {q k value : Nat} {es : List Nat}
    (hSeq : ProbabilityAlternates q es) (hQ : q < 2)
    (hAt : es[k]? = some value) : value = (q + k) % 2 := by
  induction hSeq generalizing k with
  | nil q => simp at hAt
  | @cons q rest H ih =>
    cases k with
    | zero =>
      have h := Option.some.inj hAt
      rw [← h, Nat.add_zero, Nat.mod_eq_of_lt hQ]
    | succ k =>
      have hBit : q ^^^ 1 < 2 := by interval_cases q <;> decide
      have hParsed := ih hBit hAt
      rw [hParsed]
      interval_cases q <;> simp only [Nat.reduceXor] <;> omega

/-- Every actual successful MMA acquire uses the selected probability packet's next parity.
Failed retries do not advance its local ordinal. -/
theorem probabilityAcquireParity (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j source q cta : Nat} {acq : Bool} {scope : MbarScope} (stage packet : Fin 2)
    (he : X.get (g,j) = some ⟨source, .wait (probabilityObject l cta stage packet)
      q true acq scope⟩) :
    warpIndex l g = 12 ∧ g / l.block = cta ∧
      q = okPolls (probabilityObject l cta stage packet) ((X.tr g).take j) % 2 := by
  let obj := probabilityObject l cta stage packet
  let mark := probabilityMark (slot stage packet)
  obtain ⟨hCta, hSite⟩ := probabilityWaitSite hp hX stage packet he
  rw [waitHeads] at hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hMark : mark ⟨source, .wait obj q true acq scope⟩ = some q := by
    simp [mark, probabilityMark, hSite]
  obtain ⟨hWarp, hHistory⟩ := probabilityRawParity hp hX he hMark
  refine ⟨hWarp, hCta.symm, ?_⟩
  have hCount : (((X.tr g).take j).filterMap mark).length =
      okPolls obj ((X.tr g).take j) := by
    rw [List.length_filterMap_eq_countP]
    apply List.countP_congr
    intro e hMem
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hMem)
    rw [probabilityMarkMatches hp hX stage packet hCta.symm (j := k) hk]
  have hSplit : (X.tr g).take (j + 1) =
      (X.tr g).take j ++ [⟨source, .wait obj q true acq scope⟩] := by
    rw [List.take_add_one]
    exact congrArg (fun e : Option Event => (X.tr g).take j ++ e.toList) he
  have hFull : (X.tr g).filterMap mark =
      ((X.tr g).take j).filterMap mark ++ q :: ((X.tr g).drop (j + 1)).filterMap mark := by
    conv_lhs => rw [← List.take_append_drop (j + 1) (X.tr g)]
    rw [hSplit, List.append_assoc, List.filterMap_append]
    simp [hMark]
  have hParse : ((X.tr g).filterMap mark)[okPolls obj ((X.tr g).take j)]? = some q := by
    rw [hFull, ← hCount, List.getElem?_append_right (by rfl), Nat.sub_self]
    rfl
  simpa only [Nat.zero_add] using probabilityParityAt hHistory (by decide) hParse

/-- The selected MMA lane observes probability generations in alternating parity order. -/
theorem probabilitySelectedAlternates (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta g : Nat} (stage packet : Fin 2) :
    SelectedAlternates (objectThreadSelected g) (X.objects (probabilityObject l cta stage packet))
      0 := by
  apply MbarRing.Poll.alternates hX (fun _ hr hPoll => actualInitOrPollClean hp hX hr (.inr hPoll))
  intro k source q acq sc hPoll
  rw [(probabilityAcquireParity hp hX stage packet hPoll).2.2, Nat.add_zero, Nat.mod_mod]

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
