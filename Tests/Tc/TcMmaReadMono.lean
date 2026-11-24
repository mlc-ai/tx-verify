-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Tmem.TmemPairRecord

/-! Tensor Memory load values are fixed once read: extensions that add no evidence about
old events keep every old load's constraint, and only a new load adds one. -/
namespace PTX.Tests.TcMmaReadMono
open TcMma
noncomputable section

-- The trivial extension.
example (L : Launch) (X : Execution) : ReadPreserved L X X :=
  ⟨Execution.le_refl X, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ h => h, fun _ _ h => .inl h,
    fun _ => Iff.rfl, fun _ h => .inl h⟩

-- Without loads, and with every A operand in shared memory, the read rule holds.
example (L : Launch) (A : List Assumption) (X : Execution)
    (h : ∀ e a vals sh, ¬ X.TLd e a vals sh)
    (hA : ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.aTmem = none) :
    ReadOk L A X :=
  readOk_of_no_load h hA

-- Appending an instruction that is not a load keeps the rule, given only that causality
-- into old events is unchanged.
example (L : Launch) (A : List Assumption) (X : Execution) (g : Nat) (e : Event)
    (r : Nat → Option AsyncCopy.Ref) (h : ReadOk L A X) (ht : AsyncCopy.CommitOk X)
    (ho : AsyncCopy.ObjectsOk X) (hte : AsyncCopy.TcEffectsOk X)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
        (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    (hk : ∀ pc ta vals sh, e ≠ ⟨pc, .tc (.ld ta vals sh)⟩) : ReadOk L A (X.snoc g e r) :=
  readOk_snoc h ht ho hte hbo fun pc ta vals sh he => (hk pc ta vals sh he).elim

-- A new load must itself satisfy the rule for every read source it has.
example (L : Launch) (A : List Assumption) (X : Execution) (g pc ta : Nat) (vals : List Value)
    (sh : TcShape)
    (r : Nat → Option AsyncCopy.Ref) (h : ReadOk L A X) (ht : AsyncCopy.CommitOk X)
    (ho : AsyncCopy.ObjectsOk X) (hte : AsyncCopy.TcEffectsOk X)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ⟨pc, .tc (.ld ta vals sh)⟩ r) x f ↔ baseCausality L X x f))
    (hnew : ∀ (j : Nat) source cell value,
      ReadSource L (X.snoc g ⟨pc, .tc (.ld ta vals sh)⟩ r) .ld source (g, (X.tr g).length) cell →
      Wrote L A (X.snoc g ⟨pc, .tc (.ld ta vals sh)⟩ r) source cell value →
      ∃ word, vals[j]? = some word ∧ WordContains value word) :
    ReadOk L A (X.snoc g ⟨pc, .tc (.ld ta vals sh)⟩ r) := by
  apply readOk_snoc h ht ho hte hbo
  intro pc' ta' vals' sh' he j source cell value _ hs hw
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.ld.injEq] at he
  obtain ⟨rfl, rfl, rfl, rfl⟩ := he
  exact hnew j source cell value hs hw

-- Recording an unpaired release adds no coverage, so old loads keep their constraints.
private def release : Tmem.Pair.Requests :=
  ⟨⟨0, 0, fun _ => 0, 0, none, .dealloc 0 32⟩, .one, .dealloc 0 32⟩
example (L : Launch) (A : List Assumption) (X : Execution) (h : ReadOk L A X)
    (hte : AsyncCopy.TcEffectsOk X)
    (hnp : ∀ q ∈ X.tmemPairing, q.1 ≠ release.own ∧ q.2 ≠ release.own) :
    ReadOk L A (X.recordEntry 0 release) := by
  apply Tmem.Pair.readOk_recordEntry h hte _ hnp
  rintro owner e col ⟨n, base, ha, -⟩
  cases ha

-- Pairing two recorded requests adds no read constraint either, when no lane of a pairing of
-- allocations happens before an event (EXT-PAIR-ALLOC-ORDER).
example (L : Launch) (A : List Assumption) (X : Execution) (h : ReadOk L A X)
    (hte : AsyncCopy.TcEffectsOk X) (q : Tmem.Pair.WarpRequest × Tmem.Pair.WarpRequest)
    (hq : Tmem.Pair.PairingQuiet L X q) : ReadOk L A (X.recordPairing q) :=
  Tmem.Pair.readOk_recordPairing h hte hq

-- An old load's sources restrict to the smaller execution.
example (L : Launch) (_A : List Assumption) (X Y : Execution) (h : ReadPreserved L X Y)
    {k : TmemRead} {source load : EvId} {cell : Cell}
    (hl : load.2 < (X.tr load.1).length) (hs : ReadSource L Y k source load cell) :
    ReadSource L X k source load cell := (h.readSource hl hs).1

end
end PTX.Tests.TcMmaReadMono
