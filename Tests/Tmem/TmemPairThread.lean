-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.FinCases
public import Core.Assembly.Correctness
public import Core.Source.Decode
public import Core.Tmem.TmemPairRequests
public import Core.Thread.Run

namespace PTX.Tests.TmemPairThread
noncomputable section

private def L : Launch := { grid := 2, block := 384, params := fun _ => none, clusterSize := 2 }
private def env : Decode.Env := { classes := [⟨"r".toList, 3, 32⟩], labels := [], params := [] }
private def t : TState := { regs := fun
  | 0 => some (.bits 32 128)
  | 1 => some (.bits 32 512)
  | 2 => some (.bits 32 0)
  | _ => none }

example : Decode.op env "tcgen05.alloc.cta_group::2.sync.aligned.shared::cta.b32"
    [.address [.register "r0"], .register "r1"] = .ok (.tcAlloc .two 0 0 (.reg 1)) := rfl
example : Decode.op env "tcgen05.dealloc.cta_group::2.sync.aligned.b32"
    [.register "r2", .register "r1"] = .ok (.tcDealloc .two (.reg 2) (.reg 1)) := rfl
example : Decode.op env "tcgen05.relinquish_alloc_permit.cta_group::2.sync.aligned" [] =
    .ok (.tcRelinquish .two) := rfl

example : tcTmpl L 384 t (.tcDealloc .two (.reg 2) (.reg 1)) =
    .tc (.resource .two none (.dealloc 0 512)) (next t) := rfl
example : tcTmpl L 384 t (.tcRelinquish .two) = .tc (.resource .two none .relinquish) (next t) :=
    rfl

-- The allocation event is the request: it carries no column. Its destination belongs to the
-- executing CTA; thread 384 is lane 0 of its warp, so it goes on to the address store.
example : tcTmpl L 384 t (.tcAlloc .two 0 0 (.reg 1)) =
    .tc (.resource .two (some ⟨.shared, 1, 128⟩) (.alloc 512)) { t with sub := 1 } := rfl
example : tcTmpl L 385 t (.tcAlloc .two 0 0 (.reg 1)) =
    .tc (.resource .two (some ⟨.shared, 1, 128⟩) (.alloc 512)) (next t) := rfl

-- The returned address is stored in local shared memory as a separate ordinary write, after
-- the allocation returns; the stored column is open (OBJ-TMEM-ALLOC-RESULT fixes it).
example : tcTmpl L 384 { t with sub := 1 } (.tcAlloc .two 0 0 (.reg 1)) =
    .tcAllocStore ⟨.shared, 1, 128⟩ { t with pc := 1, sub := 0 } := rfl
example (col : Nat) (h : col < 2 ^ 16) (u : TState) :
    Fires 7 (.tcAllocStore ⟨.shared, 1, 128⟩ u)
      ⟨7, .wr { loc := ⟨.shared, 1, 128⟩, size := 4 } (Value.bits 32 (BitVec.ofNat 64 col)).toBytes⟩
      (some u) :=
  ⟨col, h, rfl, rfl⟩

example : tcTmpl L 384 t (.tcDealloc .two (.reg 2) (.imm 96)) =
    .ub .badValue := rfl

-- A request is no longer rejected by kind alone, but completion must cover it.
example (X : Execution) (i : EvId) (pc : Nat) (dst : Option Loc) (a : Tmem.Request)
    (h : X.get i = some ⟨pc, .tc (.resource .two dst a)⟩) (hc : Complete L X) :
    Tmem.Pair.Covered L X i := hc.2.2 i pc .two dst a h

open Tmem.Pair
private def left : WarpRequest := ⟨0, 0, fun _ => 0, 5, none, .relinquish⟩
private def right : WarpRequest := ⟨1, 11, fun _ => 0, 9, none, .relinquish⟩
private def X : Execution := {
  tr := fun g => if g < 32 then [⟨5, .tc (.resource .two none .relinquish)⟩]
    else if 736 ≤ g ∧ g < 768 then [⟨9, .tc (.resource .two none .relinquish)⟩] else [],
  rf := fun _ _ => none }

-- Different local warp numbers and source PCs are allowed across the CTA pair.
example : PairValid L X (left, right) := by
  refine ⟨by decide, ?_, ?_, ?_, by decide, by decide, rfl⟩
  · refine ⟨by decide, by decide, ?_, 0, ?_⟩
    · intro lane
      fin_cases lane <;> rfl
    · intro lane
      fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · refine ⟨by decide, by decide, ?_, 0, ?_⟩
    · intro lane
      fin_cases lane <;> rfl
    · intro lane
      fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · unfold SameCtaGroup CtaInCluster Launch.ctaGroupRanks CtaGroup.size
    decide

-- Two warps of the same CTA cannot stand in for peer participation.
example (Y : Execution) (a b : WarpRequest) (h : a.cta = b.cta) :
    ¬ PairValid L Y (a, b) := by
  intro hv
  exact hv.2.2.2.2.1 h

-- Erasing even one required lane invalidates its warp request.
example (Y : Execution) (w : WarpRequest) (lane : Fin 32)
    (h : Y.get (w.event L lane) = none) : ¬ w.Valid L Y .two := by
  intro hv
  have he := hv.2.2.1 lane
  rw [h] at he
  cases he

end
end PTX.Tests.TmemPairThread
