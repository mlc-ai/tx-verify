-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Order.Order

@[expose] public section

/-! # Bytes read and bytes left

What the memory model gives a byte no conflicting access reaches. A read of a byte that no write
covers returns its launch content (`Consistent.launch_byte`); the memory after an execution holds
the byte of a byte's only writer (`IsFinal.unique`), the byte all of finitely many writers of a
byte agree on (`IsFinal.of_agree`) and the launch content of a byte no write covers
(`IsFinal.unwritten`). -/

namespace PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A byte no write covers reads its launch content.** -/
theorem Consistent.launch_byte (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (hr : X.MemReads e a bs) {k : Nat} (hk : k < a.size)
    (hno : ∀ w a' bs', X.MemWrites w a' bs' → ¬ a'.Covers (a.loc.at k)) {c : Byte}
    (hm : mem0 (a.loc.at k) = some (some c)) : bs[k]? = some (some c) := by
  have := (hX.rf e a bs hr).2 k hk
  cases hrf : X.rf e k with
  | none =>
    rw [hrf] at this
    rw [this _ hm]
    rfl
  | some w =>
    rw [hrf] at this
    obtain ⟨a', bs', hw, hc, -⟩ := this
    exact absurd hc (hno w a' bs' hw)

/-- A read returns as many bytes as it reads. -/
theorem Consistent.read_length (hX : Consistent L K A mem0 X) {e : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} (hr : X.MemReads e a bs) : bs.length = a.size :=
  (hX.rf e a bs hr).1

/-- **The memory after an execution holds the byte of a byte's only writer.** -/
theorem IsFinal.unique {m : FinalMem} (hf : IsFinal L mem0 X m) {l : Loc} {w : AsyncCopy.Ref}
    {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) (hc : a.Covers l)
    (hu : ∀ w' a' bs', X.MemWrites w' a' bs' → a'.Covers l → w' = w) :
    m l = some (wbyte a bs l) := by
  obtain ⟨_, -, hf⟩ := hf
  exact (hf l).1 w a bs hw hc fun w' a' bs' hw' hc' => .inl (hu w' a' bs' hw' hc')

/-- **The memory after an execution holds the launch content of a byte no write covers.** -/
theorem IsFinal.unwritten {m : FinalMem} (hf : IsFinal L mem0 X m) {l : Loc}
    (h : ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers l) : m l = mem0 l := by
  obtain ⟨_, -, hf⟩ := hf
  exact (hf l).2.1 h


/-- A strict order has a maximal element among the members of a list that satisfy `P`, when one
does. -/
theorem exists_max_of_list {α : Type*} {r : α → α → Prop} (irrefl : ∀ x, ¬ r x x)
    (trans : ∀ x y z, r x y → r y z → r x z) (P : α → Prop) :
    ∀ (xs : List α), (∃ x ∈ xs, P x) → ∃ x ∈ xs, P x ∧ ∀ y ∈ xs, P y → ¬ r x y
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | x :: xs, h => by
    by_cases hx : ∃ y ∈ xs, P y
    · obtain ⟨z, hz, hPz, hmax⟩ := exists_max_of_list irrefl trans P xs hx
      by_cases hP : P x ∧ r z x
      · refine ⟨x, List.mem_cons_self, hP.1, fun y hy hPy hxy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact irrefl _ hxy
        · exact hmax y hy hPy (trans _ _ _ hP.2 hxy)
      · refine ⟨z, List.mem_cons_of_mem _ hz, hPz, fun y hy hPy hzy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hP ⟨hPy, hzy⟩
        · exact hmax y hy hPy hzy
    · obtain ⟨y, hy, hPy⟩ := h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨y, List.mem_cons_self, hPy, fun z hz hPz _ => by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact irrefl _ ‹_›
          · exact hx ⟨z, hz, hPz⟩⟩
      · exact absurd ⟨y, hy, hPy⟩ hx

/-- **The memory after an execution holds the byte that all writers of a byte agree on**, when
the writers are finitely many (all in `ws`) and there is one. -/
theorem IsFinal.of_agree {m : FinalMem} (hf : IsFinal L mem0 X m) {l : Loc}
    {ws : List AsyncCopy.Ref} (hws : ∀ w a bs, X.MemWrites w a bs → a.Covers l → w ∈ ws)
    {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs) (hc : a.Covers l)
    {v : Option Byte} (hv : ∀ w a bs, X.MemWrites w a bs → a.Covers l → wbyte a bs l = v) :
    m l = some v := by
  obtain ⟨co, hco, hf⟩ := hf
  refine (hf l).2.2 v ?_ fun w a bs hmax hw => hv w a bs hw ?_
  · obtain ⟨u, -, hu, hmax⟩ := exists_max_of_list hco.irrefl hco.trans
      (fun u => ∃ a bs, X.MemWrites u a bs ∧ a.Covers l) ws
      ⟨w, hws w a bs hw hc, a, bs, hw, hc⟩
    refine ⟨u, hu, fun w' a' bs' hw' hc' => hmax w' (hws w' a' bs' hw' hc') ⟨a', bs', hw', hc'⟩⟩
  · obtain ⟨⟨a0, bs0, hw0, hc0⟩, -⟩ := hmax
    obtain ⟨hfp, rfl⟩ := hw0.unique hw
    obtain ⟨h1, h2⟩ := hc0
    refine ⟨?_, ?_⟩
    · rwa [← hfp.1]
    · rwa [← hfp.1, ← hfp.2]

end

end PTX
