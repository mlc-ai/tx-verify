-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Obj
public import Kernels.InklingRelDecode.Flow.Code.Part015
public import Lemmas.Protocol.UnitNotify
public import Lemmas.Step.Object
public import Lemmas.Snoc.SnocObjectOrder
import Lemmas.Flow.MemTmpl

/-! Test of the information in the worker rows and KvPreload. Append an arrival by lane
zero, outside both worker warps and past the preload PCs. The test is about the exported
projections; reachability of the softmax register file is exactly the missing producer fact. -/

@[expose] public section
set_option maxRecDepth 4096
namespace PTX.Tests.InklingKvSources
open PTX PTX.Proof PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof
open MBarrier AsyncCopy

def loc (L : Launch) := Protocol.KV.emptyLoc L 0 0
def event (L : Launch) : Event := ⟨1013,.arrive (loc L) 0 1 true .cta⟩
def rec (L : Launch) (X : Execution) :=
  Step.checkedRecord (.thread (0,(X.tr 0).length)) (.arrive 1 0)
    (stateBefore (X.objects (loc L)) (X.objects (loc L)).length)

noncomputable def extend (L : Launch) (X : Execution) :=
  X.snocObject 0 (event L) (fun _ => none) (loc L) (rec L X)

/-- At PC 1013 the object comes from register 1709. The decoded instruction and
guard admit this local event when that register holds empty slot zero's address. -/
public theorem local_arrival :
    let L : Launch := { grid := 1, block := 256, params := fun _ => none }
    let t : TState := { pc := 1013, regs := fun r =>
      if r = 1709 then some (b32 213248) else if r = 177 then some (.pred true) else none }
    EStep kernel Assumptions.all L 0 t (event L) (some (next t)) := by
  dsimp only
  refine ⟨_, out_event rfl Flow.code_1013 (by rfl) (by rfl), ?_⟩
  exact ⟨rfl,rfl⟩

/-- An unchanged worker trace includes every one of its prefix counts. KvPreload
is also preserved, for arbitrary original traces, including nonempty prologue traces. -/
public theorem preserve (Q : Params) (L : Launch) (X : Execution) (hp : Iface.KvPreload Q L X) :
    (∀ g, 4 ≤ g % L.block / 32 → (extend L X).tr g = X.tr g) ∧
      Iface.KvPreload Q L (extend L X) := by
  constructor
  · intro g hw
    have hn : g ≠ 0 := by rintro rfl; simp at hw
    simp [extend, Execution.snocObject, Execution.appendObject, Execution.snoc, hn]
  · have old {g k : Nat} {ev : Event} (he : (extend L X).get (g,k) = some ev) (hpc : ev.pc < 574) :
        X.get (g,k) = some ev ∧ ((extend L X).tr g).take k = (X.tr g).take k := by
      change (X.snoc 0 (event L) (fun _ => none)).get (g,k) = some ev at he
      rw [snoc_get] at he
      split at he
      · cases he
        exact False.elim ((by decide : ¬ 1013 < 574) hpc)
      · exact ⟨he,snoc_take (r := fun _ => none) (v := (g,k)) (Nat.le_of_lt (len_of_get he))⟩
    constructor
    · intro g k pc c slot tx n rel sc hl hh he
      obtain ⟨he',hpfx⟩ := old he hh
      rw [hpfx]
      exact hp.arrive hl hh he'
    · intro g k pc c slot a sp hl hh he hm
      obtain ⟨he',hpfx⟩ := old he hh
      rw [hpfx]
      exact hp.copy hl hh he' hm

/-- A direct thread arrival cannot be a commit notification, an init or a poll. -/
public theorem not_notify (L : Launch) (X : Execution) (producer : Nat) (named : Loc)
    (delta : Nat) (selected : Nat → Prop) :
    ¬ MbarRing.Notify.Obj (extend L X) (loc L) producer named delta selected := by
  intro H
  have hm : rec L X ∈ (extend L X).objects (loc L) := by
    simp [extend, Execution.snocObject, Execution.appendObject]
  have ha : (rec L X).action = .arrive 1 0 := Step.checkedRecord_action ..
  have hid : (rec L X).id = .thread (0,(X.tr 0).length) := Step.checkedRecord_id ..
  cases H.src _ hm with
  | init h => have hh := ha.symm.trans h; cases hh
  | poll _ _ h => have hh := ha.symm.trans h; cases hh
  | commit h => have hh := hid.symm.trans h; cases hh

/-- Equality of all worker traces and the preload row does not imply that
empty slot zero has only notification arrivals. -/
theorem rows_insufficient (Q : Params) (L : Launch) (X : Execution)
    (hp : Iface.KvPreload Q L X) :
    ¬ (∀ Y : Execution, (∀ g, 4 ≤ g % L.block / 32 → Y.tr g = X.tr g) →
        Iface.KvPreload Q L Y → ∃ producer named delta,
          MbarRing.Notify.Obj Y (loc L) producer named delta) := by
  intro h
  obtain ⟨hw, hp'⟩ := preserve Q L X hp
  obtain ⟨p, n, d, hn⟩ := h (extend L X) hw hp'
  exact not_notify L X p n d _ hn

end PTX.Tests.InklingKvSources
