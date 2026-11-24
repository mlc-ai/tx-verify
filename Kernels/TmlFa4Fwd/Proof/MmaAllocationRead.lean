-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaStartup
public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Lemmas.Async.ReadSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue

noncomputable section

/-- The ordinary allocation-result load uses the shared base and scalar element zero. -/
theorem allocationReadTemplateFromBase {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {facts : List (Nat × Value)} (ht : At t 1911 facts)
    (hBase : t.regs 2535 = some (b32 l.sharedBase)) :
    out kernel Assumptions.all l g t = .ev
      (.read { loc := allocationSlot l g, size := 4 } (afterLoad t [1179])) := by
  have hBound : l.sharedBase + 312 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAddr : effAddr l g t .shared 2535 312 = .ok (allocationSlot l g) :=
    effAddr_b32_off (off := 312) hBase hBound
  have hAlign : (allocationSlot l g).addr % 4 = 0 := by
    have h := hp.shared.1
    change (l.sharedBase + 312) % 4 = 0
    omega
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_1911) rfl rfl]
  change Out.ev (loadTmpl [] l g t .shared false 32 [1179] 2535 312) = _
  unfold loadTmpl
  rw [hAddr]
  simp only [bind, Except.bind, List.length_singleton, ht.2.1]
  rw [elemAcc_ok (by decide : 0 < 32 / 8) (by simpa using hAlign)]
  simp [Loc.at]

/-- The first ordinary shared read returns the word published by the allocating warp. -/
theorem allocationReadTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 1911 (entryFacts p l g)) :
    out kernel Assumptions.all l g t = .ev
      (.read { loc := allocationSlot l g, size := 4 } (afterLoad t [1179])) :=
  allocationReadTemplateFromBase hp ht
    (holds_mem ht.2.2.2.2 (by simp [entryFacts, startupFacts]))

/-- Once memory provenance identifies the allocation word, the actual load rebuilds that word. -/
theorem allocationReadValue {p : Params} {l : Launch} {g col : Nat} {t : TState}
    (ht : At t 1911 (entryFacts p l g)) :
    At (afterLoad t [1179] ((b32 col).toBytes.map some)) 1912
      ((1179, b32 col) :: entryFacts p l g) := by
  have hRebuild := rebuild_scalar (v := b32 col) (by decide : 0 < 4) rfl
  rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild]
  have hEq : { setReg t 1179 (b32 col) with pc := t.pc + 1, sub := 0, acc := [] } =
      next (setReg t 1179 (b32 col)) := by
    have hSub := ht.2.1
    have hAcc := ht.2.2.1
    cases t
    simp_all [setReg, next]
  rw [hEq]
  exact ht.set (by
    intro pair hm
    simp only [entryFacts, startupFacts, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> exact of_decide_eq_true rfl)

end
end PTX.Kernels.TmlFa4Fwd.Mma
