-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegReq
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Every thread makes one register request

For the safety classes (`ERR-SETMAXNREG`, the `setmaxnreg` class of `ERR-ALIGNED`): over a followed
consistent execution without undefined behaviour, a request is its thread's first
(`request_first`), at its warpgroup's pc (`request_pc`), and an `exit` follows a request
(`request_exit`); its direction and count are its warpgroup's (`request_value`, `regCount`).
The lemmas are `Common/RegReq.lean`'s (`req_first`, `req_state`, `req_exit`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A request is at its warpgroup's pc.** -/
theorem request_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    (pc = 103 ∧ warp L g < 4) ∨ (pc = 1842 ∧ 4 ≤ warp L g ∧ warp L g < 8) ∨
      (pc = 2606 ∧ 8 ≤ warp L g ∧ warp L g < 12) := by
  obtain ⟨-, -, -, h⟩ := req_state hp hX hFw hnu he
  exact h

/-- **A request is its thread's first.** -/
theorem request_first (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ((X.tr g).take k).countP SetMaxNReg.isRequest = 0 :=
  req_first hp hX hFw hnu he

/-- **A thread exits after its register request.** -/
theorem request_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k pc : Nat}
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    1 ≤ ((X.tr g).take k).countP SetMaxNReg.isRequest :=
  req_exit hp hX hFw hnu he

/-- **The direction and count of a warp's request**: `inc 224` (warpgroup 0), `dec 72`
(warpgroup 1), `inc 208` (warpgroup 2). -/
def regCount (w : Nat) : Bool × Nat :=
  if w < 4 then (true, 224) else if w < 8 then (false, 72) else (true, 208)

/-- **A request has its warp's direction and count.** -/
theorem request_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {k pc n inst : Nat} {inc : Bool}
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    (inc, n) = regCount (warp L g) := by
  have hpc := request_pc hp hX hFw hnu he
  obtain ⟨ins, hc, hop⟩ := req_op hX he
  rcases hpc with ⟨rfl, hw⟩ | ⟨rfl, hw, hw'⟩ | ⟨rfl, hw, hw'⟩
  · rw [Flow.code_103, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [regCount, hw, ite_true]
  · rw [Flow.code_1842, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [regCount, show ¬ warp L g < 4 by omega, hw', ite_true, ite_false]
  · rw [Flow.code_2606, Option.some.injEq] at hc
    subst hc
    simp only [Op.setMaxReg.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    simp only [regCount, show ¬ warp L g < 4 by omega, show ¬ warp L g < 8 by omega, ite_false]

/-- The lanes of one warp have one warp index. -/
theorem warp_of_sameWarp (hp : Pre P L m) {g h : Nat} (hw : SameWarp L g h) :
    warp L g = warp L h := by
  simp only [warp, tidOf_x_eq hp, ← hp.block]
  exact hw.2

/-- The lanes of one warpgroup have one request. -/
theorem regCount_group (hp : Pre P L m) {g h : Nat} (hs : SetMaxNReg.SameGroup L g h) :
    regCount (warp L g) = regCount (warp L h) := by
  obtain ⟨-, hgrp⟩ := hs
  rw [hp.block] at hgrp
  simp only [warp, tidOf_x_eq hp, regCount]
  split_ifs <;> first | rfl | omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
