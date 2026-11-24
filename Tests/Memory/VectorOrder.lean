-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Order.OrderNotAccess

/-!
# Vector accesses are unordered among their elements (§8.2.4)

"Memory operations with a vector data type are modeled as a set of equivalent memory
operations with a scalar data type, executed in an unspecified order on the elements in the
vector." The elements of one `st.v2` are therefore not ordered by program order or by base
causality, while two scalar stores in program order are. A reader that observes element 1 of
such a store is not guaranteed to observe element 0, because nothing orders them.
-/
namespace PTX.Tests.VectorOrder
noncomputable section

def launch : Launch := { grid := 1, block := 1, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def base : Loc := ⟨.global, 0, 8⟩
def one : List Byte := (Value.bits 32 1).toBytes

-- The footprints the vector store `st.global.v2.b32 [8]` produces: element 1 is the second
-- scalar operation, at the next address (EXT-VECTOR-ELEM).
example : elemAcc base 4 2 1 = .ok { loc := base.at 4, size := 4, elem := 1 } := by
  simp [elemAcc, base, Loc.at]
  rfl

/-- One vector store of two 32-bit elements by thread 0, then an `exit`: the trace lists the
elements in element order. -/
def vec : Execution where
  tr g := if g = 0 then
    [⟨0, .wr { loc := base, size := 4, elem := 0 } one⟩,
     ⟨0, .wr { loc := base.at 4, size := 4, elem := 1 } one⟩,
     ⟨1, .exit⟩] else []
  rf _ _ := none

/-- Two scalar stores in program order. -/
def scalar : Execution where
  tr g := if g = 0 then
    [⟨0, .wr { loc := base, size := 4 } one⟩, ⟨1, .wr { loc := base.at 4, size := 4 } one⟩] else []
  rf _ _ := none

/-- Two scalar stores are program-ordered. -/
example : po scalar (0, 0) (0, 1) := by
  refine ⟨rfl, by decide, by decide, ?_⟩
  decide

/-- The elements of one vector store are not. -/
theorem elements_not_po : ¬ po vec (0, 0) (0, 1) ∧ ¬ po vec (0, 1) (0, 0) := by
  refine ⟨fun h => h.2.2.2 ?_, fun h => absurd h.2.1 (by decide)⟩
  decide

/-- The vector store's elements are ordered with the next instruction. -/
example : po vec (0, 0) (0, 2) ∧ po vec (0, 1) (0, 2) :=
  ⟨po_of_not_access rfl (by decide) (by decide) (by decide),
    po_of_not_access rfl (by decide) (by decide) (by decide)⟩

/-- In an execution without barriers, warp barriers, acquire waits, cluster barriers, fences or
release stores, causality is program order. -/
theorem baseCausality_po {X : Execution}
    (hk : ∀ g ev, ev ∈ X.tr g → (∀ id c, ev.kind ≠ .bar id c) ∧
      (∀ mask inst, ev.kind ≠ .warpBar mask inst) ∧
      (∀ m q sc, ev.kind ≠ .wait m q true true sc) ∧
      (∀ a bs, ev.kind = .wr a bs → a.release = false) ∧
      (∀ a old new, ev.kind = .rmw a old new → a.release = false))
    (hnf : ∀ g ev, ev ∈ X.tr g → ∀ sem s, ev.kind ≠ .fence sem s)
    (hc : ∀ c, X.clusters c = []) {e f : EvId} (h : baseCausality launch X e f) : po X e f := by
  refine baseCausality_of_noBar ?_ ?_ ?_ ?_ ?_ ?_ h
  · rintro e k ⟨-, ⟨count, pc, hb⟩, -⟩
    exact (hk _ _ (List.mem_of_getElem? hb)).1 _ _ rfl
  · rintro w m ⟨pc, q, sc, hw⟩
    exact (hk _ _ (List.mem_of_getElem? hw)).2.2.1 _ _ _ rfl
  · rintro e f ⟨-, i, j, ⟨phase, ⟨k, s, t, cta, w, lanes, g, hi, -⟩, -⟩, -⟩
    simp [hc] at hi
  · rintro e f ⟨i, j, ⟨-, mask, inst, ⟨pc, hw⟩, -⟩, -⟩
    exact (hk _ _ (List.mem_of_getElem? hw)).2.1 _ _ rfl
  · rintro e f ⟨a, b, bs, cs, hw, -, hrel, -⟩
    rcases hw with ⟨pc, hwr⟩ | ⟨old, pc, hrm⟩
    · have := (hk _ _ (List.mem_of_getElem? hwr)).2.2.2.1 _ _ rfl
      rw [this] at hrel
      cases hrel
    · have := (hk _ _ (List.mem_of_getElem? hrm)).2.2.2.2 _ _ _ rfl
      rw [this] at hrel
      cases hrel
  · intro e f
    refine not_fenceSync_of_noFence ?_ e f
    rintro ⟨g, i⟩ sem s ⟨pc, hget⟩
    exact hnf g ⟨pc, .fence sem s⟩ (List.mem_of_getElem? hget) sem s rfl

/-- Neither element of the vector store is base-causality-before the other: nothing orders them,
so a reader that sees element 1 of the store is not guaranteed element 0. -/
theorem elements_not_baseCausality : ¬ baseCausality launch vec (0, 0) (0, 1) ∧
    ¬ baseCausality launch vec (0, 1) (0, 0) := by
  have hk : ∀ g ev, ev ∈ vec.tr g → (∀ id c, ev.kind ≠ .bar id c) ∧
      (∀ mask inst, ev.kind ≠ .warpBar mask inst) ∧
      (∀ m q sc, ev.kind ≠ .wait m q true true sc) ∧
      (∀ a bs, ev.kind = .wr a bs → a.release = false) ∧
      (∀ a old new, ev.kind = .rmw a old new → a.release = false) := by
    intro g ev hev
    simp only [vec] at hev
    split_ifs at hev
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl | rfl <;> simp
    · cases hev
  have hnf : ∀ g ev, ev ∈ vec.tr g → ∀ sem s, ev.kind ≠ .fence sem s := by
    intro g ev hev
    simp only [vec] at hev
    split_ifs at hev
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl | rfl <;> simp
    · cases hev
  have hc : ∀ c, vec.clusters c = [] := fun _ => rfl
  exact ⟨fun h => elements_not_po.1 (baseCausality_po hk hnf hc h), fun h => elements_not_po.2
      (baseCausality_po hk hnf hc h)⟩

end
end PTX.Tests.VectorOrder
