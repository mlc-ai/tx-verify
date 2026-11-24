-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorReduce

@[expose] public section

/-! # Frames of the tensor-reduction rule (DEP-REDUCTION-VALUES)

`ReduceOk` depends only on the recorded tensor reduction elements (their old, source and written
bytes) and on the performed elements of linear reductions. Atomicity is MEM-ATOMICITY
(`Consistent.atomic`) and is framed separately. An extension that keeps these elements keeps the
rule. -/

namespace PTX.TensorStore
noncomputable section

variable {A : List Assumption} {X Y : Execution}

/-- Every performed reduction element of `Y` is one of `X` with the same bytes. -/
def ReduceFrame (X Y : Execution) : Prop :=
  ∀ i o' x y, Y.tensorStores i = some o' → o'.spec.reduce.isSome → (writeByte o' x y 0).isSome →
    ∃ o, X.tensorStores i = some o ∧ o.spec = o'.spec ∧ ∀ k,
      writeByte o' x y k = writeByte o x y k ∧ oldByte o' x y k = oldByte o x y k ∧
        readByte o' x y k = readByte o x y k

theorem ReduceFrame.of_eq (h : Y.tensorStores = X.tensorStores) : ReduceFrame X Y := by
  intro i o' _ _ ho' _ _
  exact ⟨o', h ▸ ho', rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- Replacing one observation by one that keeps every performed reduction element. -/
theorem ReduceFrame.update {i : EvId} {o : Observation}
    (hY : ∀ j, Y.tensorStores j = if j = i then some o else X.tensorStores j)
    (hi : o.spec.reduce.isSome → ∀ x y, (writeByte o x y 0).isSome →
      ∃ old, X.tensorStores i = some old ∧ old.spec = o.spec ∧ ∀ k,
        writeByte o x y k = writeByte old x y k ∧ oldByte o x y k = oldByte old x y k ∧
          readByte o x y k = readByte old x y k) :
    ReduceFrame X Y := by
  intro j o' x y ho' hr hw
  rw [hY] at ho'
  by_cases hj : j = i
  · subst j
    simp only [↓reduceIte, Option.some.injEq] at ho'
    subst o'
    exact hi hr x y hw
  · simp only [hj, ↓reduceIte] at ho'
    exact ⟨o', ho', rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem ReduceFrame.reduced (hs : ReduceFrame X Y) {i : EvId} {x y : Nat} {fp : Acc}
    (h : Reduced Y i x y fp) : Reduced X i x y fp := by
  obtain ⟨o', red, loc, ho', hr, hl, rfl, hw⟩ := h
  obtain ⟨o, ho, hsp, hb⟩ := hs i o' x y ho' (by simp [hr]) hw
  refine ⟨o, red, loc, ho, hsp ▸ hr, hsp ▸ hl, by rw [hsp], ?_⟩
  rw [← (hb 0).1]
  exact hw

/-- The performed linear reduction elements of `Y` are those of `X`: an element `Y` performs is
performed at an instruction of `X`, with `X`'s recorded copy effects. -/
def ReduceCopyFrame (X Y : Execution) : Prop :=
  ∀ i s r j, Y.Copy i s → s.writes = .reduce r → ((Y.async.copies i).elemWrites j).isSome →
    X.Copy i s ∧ X.async.copies i = Y.async.copies i

theorem ReduceOk.frame (h : ReduceOk A X) (hs : ReduceFrame X Y) (hc : ReduceCopyFrame X Y) :
    ReduceOk A Y := by
  refine ⟨?_, ?_⟩
  · intro i o' red x y v ho' hr hw hv k hk
    obtain ⟨o, ho, hsp, hbo⟩ := hs i o' x y ho' (by simp [hr]) hw
    have hold : elementBytes oldByte o' x y = elementBytes oldByte o x y := by
      unfold elementBytes; rw [hsp]; exact List.map_congr_left fun k _ => (hbo k).2.1
    have hsrc : elementBytes readByte o' x y = elementBytes readByte o x y := by
      unfold elementBytes; rw [hsp]; exact List.map_congr_left fun k _ => (hbo k).2.2
    rw [hold, hsrc, ← hsp] at hv
    rw [(hbo k).1]
    exact h.values i o red x y v ho (hsp ▸ hr) ((hbo 0).1 ▸ hw) hv k (hsp ▸ hk)
  · intro i s red j v hY hw hperf hv
    obtain ⟨hXc, heff⟩ := hc i s red j hY hw hperf
    exact heff ▸ h.copies i s red j v hXc hw (heff.symm ▸ hperf) (heff.symm ▸ hv)

theorem ReduceOk.of_tensorStores (h : ReduceOk A X) (hs : Y.tensorStores = X.tensorStores)
    (hc : ReduceCopyFrame X Y) : ReduceOk A Y :=
  h.frame (.of_eq hs) hc

/-- No reduction has been performed: no tensor store reduces and no linear copy is a reduction. -/
theorem ReduceOk.of_none (h : ∀ i o, X.tensorStores i = some o → o.spec.reduce = none)
    (hc : ∀ i s, X.Copy i s → ∀ r, s.writes ≠ .reduce r) : ReduceOk A X := by
  refine ⟨fun i o red x y v ho hr => ?_, copyReduceValues_of_none hc⟩
  rw [h i o ho] at hr
  cases hr

end
end PTX.TensorStore
