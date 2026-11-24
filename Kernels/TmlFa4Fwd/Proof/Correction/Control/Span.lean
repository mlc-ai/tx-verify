-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Correction.Havoc
import Tactics.KernelRfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Flow PTX.Proof

/-- The suffix containing every rescale and output pack. -/
def tailCode : List Instr :=
    Decoded.code250 ++ (Decoded.code251 ++ (Decoded.code252 ++ (Decoded.code253 ++ (
    Decoded.code254 ++ (Decoded.code255 ++ (Decoded.code256 ++ (Decoded.code257 ++ (
    Decoded.code258 ++ (Decoded.code259 ++ (Decoded.code260 ++ (Decoded.code261 ++ (
    Decoded.code262 ++ (Decoded.code263 ++ (Decoded.code264 ++ (Decoded.code265 ++ (
    Decoded.code266 ++ (Decoded.code267 ++ (Decoded.code268 ++ (Decoded.code269 ++ (
    Decoded.code270 ++ (Decoded.code271 ++ (Decoded.code272 ++ (Decoded.code273 ++ (
    Decoded.code274 ++ (Decoded.code275 ++ (Decoded.code276 ++ (Decoded.code277 ++ (
    Decoded.code278 ++ (Decoded.code279 ++ (Decoded.code280 ++ (Decoded.code281 ++ (
    Decoded.code282 ++ (Decoded.code283 ++ (Decoded.code284 ++ (Decoded.code285 ++ (
    Decoded.code286 ++ (Decoded.code287)))))))))))))))))))))))))))))))))))))

theorem tailCode_eq : kernel.code.drop 8000 = tailCode := by kernel_rfl

noncomputable def spanOk (s dst : Site) : Bool :=
  let a := s.pc + 1
  let b := dst.pc
  8000 ≤ a && a ≤ b && b ≤ 9206 &&
    Havoc.check hooks (liveAt dst) a b ((tailCode.drop (a - 8000)).take (b-a))

private theorem codeLength : 9206 ≤ kernel.code.length := by decide +kernel

theorem cross_span {s dst : Site} (h : spanOk s dst = true) (val : Nat → Value) :
    SegU kernel Assumptions.all L g (s.pc+1) (factsFrom (liveAt dst) val)
      dst.pc (factsFrom (liveAt dst) val) := by
  simp only [spanOk, Bool.and_eq_true, decide_eq_true_eq] at h
  apply SegU.of_havoc rules_frame hooks_ok h.1.1.2 (h.1.2.trans codeLength) _ (fun _ hp => hp)
  have keys : (factsFrom (liveAt dst) val).map Prod.fst = liveAt dst := by
    simp only [factsFrom, List.map_map, Function.comp_def]
    exact List.map_id _
  rw [keys]
  have hc := h.2
  simpa only [← tailCode_eq, List.drop_drop, Nat.add_sub_of_le h.1.1.1,
    Nat.sub_add_cancel h.1.1.1] using hc

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
