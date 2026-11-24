-- SPDX-License-Identifier: Apache-2.0
module

public import Tactics.KernelRfl
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Flow.LdConsumed

@[expose] public section

/-! # The loads with an implicit `wait::ld`

Every site of `tcLdDataflowSites` passes `ldConsumedAt` (one evaluation of the code, here), so the
assumptions' `tcLdWait` is membership of the list: a site's proof compares numbers and does not walk
the code. -/

namespace PTX.Kernels.TmlFa4Fwd.Assumptions
open PTX PTX.Assumption

/-- The code from position 6656 on, as the decoder's chunks: the check reads only this slice. -/
def ldTail : List Instr :=
    Decoded.code208 ++ ( Decoded.code209 ++ ( Decoded.code210 ++ ( Decoded.code211 ++ (
    Decoded.code212 ++ ( Decoded.code213 ++ ( Decoded.code214 ++ ( Decoded.code215 ++ (
    Decoded.code216 ++ ( Decoded.code217 ++ ( Decoded.code218 ++ ( Decoded.code219 ++ (
    Decoded.code220 ++ ( Decoded.code221 ++ ( Decoded.code222 ++ ( Decoded.code223 ++ (
    Decoded.code224 ++ ( Decoded.code225 ++ ( Decoded.code226 ++ ( Decoded.code227 ++ (
    Decoded.code228 ++ ( Decoded.code229 ++ ( Decoded.code230 ++ ( Decoded.code231 ++ (
    Decoded.code232 ++ ( Decoded.code233 ++ ( Decoded.code234 ++ ( Decoded.code235 ++ (
    Decoded.code236 ++ ( Decoded.code237 ++ ( Decoded.code238 ++ ( Decoded.code239 ++ (
    Decoded.code240 ++ ( Decoded.code241 ++ ( Decoded.code242 ++ ( Decoded.code243 ++ (
    Decoded.code244 ++ ( Decoded.code245 ++ ( Decoded.code246 ++ ( Decoded.code247 ++ (
    Decoded.code248 ++ ( Decoded.code249 ++ ( Decoded.code250 ++ ( Decoded.code251 ++ (
    Decoded.code252 ++ ( Decoded.code253 ++ ( Decoded.code254 ++ ( Decoded.code255 ++ (
    Decoded.code256 ++ ( Decoded.code257 ++ ( Decoded.code258 ++ ( Decoded.code259 ++ (
    Decoded.code260 ++ ( Decoded.code261 ++ ( Decoded.code262 ++ ( Decoded.code263 ++ (
    Decoded.code264 ++ ( Decoded.code265 ++ ( Decoded.code266 ++ ( Decoded.code267 ++ (
    Decoded.code268 ++ ( Decoded.code269 ++ ( Decoded.code270 ++ ( Decoded.code271 ++ (
    Decoded.code272 ++ ( Decoded.code273 ++ ( Decoded.code274 ++ ( Decoded.code275 ++ (
    Decoded.code276 ++ ( Decoded.code277 ++ ( Decoded.code278 ++ ( Decoded.code279 ++ (
    Decoded.code280 ++ ( Decoded.code281 ++ ( Decoded.code282 ++ ( Decoded.code283 ++ (
    Decoded.code284 ++ ( Decoded.code285 ++ ( Decoded.code286 ++ ( Decoded.code287)))))))))))))))))
      ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem ldTail_eq : kernel.code.drop 6656 = ldTail := by
  kernel_rfl

theorem ldConsumed_sites : tcLdDataflowSites.all (ldConsumedAt kernel) = true := by
  have h : tcLdDataflowSites.all (fun pc =>
      Nat.ble 6656 pc && Flow.ldConsumedIn ldTail (pc - 6656)) = true := by kernel_rfl
  refine List.all_eq_true.mpr fun pc hpc => ?_
  have h1 := List.all_eq_true.mp h pc hpc
  simp only [Bool.and_eq_true] at h1
  rw [Flow.ldConsumedAt_eq_in ldTail_eq (Nat.le_of_ble_eq_true h1.1)]
  exact h1.2

theorem tcLdWait_iff (pc : Nat) :
    all.any (·.tcLdWait pc) = tcLdDataflowSites.contains pc := by
  rw [all_tcLdWait]
  cases h : tcLdDataflowSites.contains pc
  · rfl
  · rw [List.all_eq_true.mp ldConsumed_sites pc (by simpa using h)]
    rfl

/-- Close `Assumptions.all.any (·.tcLdWait pc) = b` at a literal position. -/
macro "ld_wait" : tactic =>
  `(tactic| exact (PTX.Kernels.TmlFa4Fwd.Assumptions.tcLdWait_iff _).trans (by kernel_rfl))

end PTX.Kernels.TmlFa4Fwd.Assumptions
