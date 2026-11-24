-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.PrefixMemory
public import Lemmas.Kernel.Memory

/-! Recover the final bytes of the prefix array from the global event traces. -/
@[expose] public section
namespace FlashKda.Prefix
open PTX
noncomputable section

/-- Only stores by the first thread can contribute a final memory write. -/
theorem writer {X : Execution}
    (simple : ∀ id e, X.get id = some e → ordinary e = true)
    (active : ∀ id a bs, X.Writes id a bs → id.1 = 0)
    {w a bs} (hw : X.MemWrites w a bs) :
    ∃ i, w = .thread (0,i) ∧ X.Writes (0,i) a bs := by
  have bad {id : EvId} {pc : Nat} {kind : Kind} (hb : ordinary ⟨pc,kind⟩ = false) :
      X.get id ≠ some ⟨pc,kind⟩ := fun h => by simpa [hb] using simple _ _ h
  have noCopy (i s) : ¬ X.Copy i s := by rintro ⟨pc, h⟩; exact bad rfl h
  have noTensor (i addr s) : ¬ X.TensorIssue i addr s := by rintro ⟨pc, h⟩; exact bad rfl h
  have noStore (i addr s) : ¬ X.TensorStoreIssue i addr s := by rintro ⟨pc, h⟩; exact bad rfl h
  have noClc (i s dest) : ¬ X.ClcIssue i s dest := by rintro ⟨pc, h⟩; exact bad rfl h
  cases w with
  | thread id =>
    rcases hw with st | ⟨old, pc, h⟩
    · obtain ⟨g,i⟩ := id
      obtain rfl := active (g,i) a bs st
      exact ⟨i,rfl,st⟩
    · exact (bad rfl h).elim
  | async id part =>
    cases part <;> try contradiction
    all_goals simp [Execution.MemWrites, noCopy, noTensor, noStore, noClc] at hw

def finalBytes (base : Nat) (words : List Nat) (mem : Mem0) (final : FinalMem) : Prop :=
  (∀ i (hi : i < words.length) k, k < 4 →
    final ⟨.global,0,base + 4*i+k⟩ = some (some (.bits 32 (BitVec.ofNat 64 words[i]), k))) ∧
  ∀ l, ¬ (l.space = .global ∧ l.cta = 0 ∧ base ≤ l.addr ∧ l.addr < base+4*words.length) →
    final l = mem l

theorem final_of_stores {L X mem final base words}
    (fin : IsFinal L mem X final)
    (simple : ∀ id e, X.get id = some e → ordinary e = true)
    (active : ∀ id a bs, X.Writes id a bs → id.1 = 0)
    (values : (X.tr 0).filterMap stored = words.zipIdx.map fun (x,i) => outputWord base i x) :
    finalBytes base words mem final := by
  have source {w a bs} (hw : X.MemWrites w a bs) :
      ∃ j x, words[j]? = some x ∧ (a,bs) = outputWord base j x := by
    obtain ⟨i, _, pc, he⟩ := writer simple active hw
    have hm : (a, bs) ∈ (X.tr 0).filterMap stored :=
      List.mem_filterMap.mpr ⟨_, List.mem_iff_getElem?.mpr ⟨i,he⟩, rfl⟩
    rw [values] at hm
    obtain ⟨⟨x,j⟩, hi, eq⟩ := List.mem_map.mp hm
    exact ⟨j, x, List.mk_mem_zipIdx_iff_getElem?.mp hi, eq.symm⟩
  constructor
  · intro i hi k hk
    let v := words[i]
    let pair := outputWord base i v
    let l : Loc := ⟨.global,0,base+4*i+k⟩
    have hm : pair ∈ (X.tr 0).filterMap stored := by
      rw [values]
      exact List.mem_map.mpr ⟨(v,i), List.mk_mem_zipIdx_iff_getElem?.mpr
        (List.getElem?_eq_getElem hi), rfl⟩
    obtain ⟨e, em, es⟩ := List.mem_filterMap.mp hm
    obtain ⟨q, he⟩ := List.mem_iff_getElem?.mp em
    have event : e.kind = .wr pair.1 pair.2 := by
      obtain ⟨pc,kind⟩ := e
      cases kind <;> simp [stored] at es
      case wr a bs =>
        rw [← es]
    have hw : X.MemWrites (.thread (0,q)) pair.1 pair.2 := by
      refine Or.inl ⟨e.pc, ?_⟩
      change (X.tr 0)[q]? = _
      rw [he, ← event]
    have cover : pair.1.Covers l := by
      simp [pair, l, outputWord, Acc.Covers, Loc.InRange]; omega
    let candidates := (List.range (X.tr 0).length).map fun q => AsyncCopy.Ref.thread (0,q)
    apply fin.of_agree (ws := candidates) (w := .thread (0,q)) _ hw cover
    · intro w a bs hw hc
      obtain ⟨j,x,hx,eq⟩ := source hw
      have ha := congrArg Prod.fst eq
      change a = (outputWord base j x).1 at ha
      have same : j = i := by
        rw [ha] at hc
        simp [Acc.Covers, Loc.InRange, l, outputWord] at hc
        omega
      subst j
      have xv : x = v := by simpa [v, hi] using hx.symm
      subst x
      have hb := congrArg Prod.snd eq
      change bs = (outputWord base i v).2 at hb
      rw [ha, hb]
      simp [wbyte, outputWord, l, v, Value.toBytes, Value.bytes, Value.byteAt, hk]
    · intro w a bs hw _
      obtain ⟨j, rfl, pc, he⟩ := writer simple active hw
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr ((List.getElem?_eq_some_iff.mp he).choose), rfl⟩
  · intro l outside
    apply fin.unwritten
    intro w a bs hw hc
    obtain ⟨j, x, hx, eq⟩ := source hw
    have hj := (List.getElem?_eq_some_iff.mp hx).choose
    have ha := congrArg Prod.fst eq
    change a = (outputWord base j x).1 at ha
    rw [ha] at hc
    simp [outputWord, Acc.Covers, Loc.InRange] at hc
    exact outside ⟨hc.1, hc.2.1, by omega, by omega⟩

end
end FlashKda.Prefix
