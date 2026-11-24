-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof Epilogue

private theorem roleCoreCode :
    ((kernel.code.drop 1904).take 864).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The MMA warp executes only Core instruction rules. Its polling and commit assumptions
constrain which traces are consistent with those rules. -/
theorem out_eq_core {l : Launch} {g : Nat} {t : TState}
    (hlo : 1904 ≤ t.pc) (hhi : t.pc < 2768) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hi : ((kernel.code.drop 1904).take 864)[t.pc - 1904]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
      exact hc
    have hCore := List.all_eq_true.mp roleCoreCode ins (List.mem_of_getElem? hi)
    apply Assumptions.out_all_eq_nil _ _ _ hc hCore
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- A decoded MMA segment transports to the full kernel model along its fallthrough path. -/
theorem localRun {l : Launch} {g pc n : Nat} {t u : TState}
    (hlo : 1904 ≤ pc) (hhi : pc + n ≤ 2768) (hpc : t.pc = pc)
    (hStraight : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hRun : run kernel [] l g n t = some u) : run kernel Assumptions.all l g n t = some u :=
  schedulerLocalTransport (lo := pc) (len := n) hStraight
    (fun hLo hHi => out_eq_core (by omega) (by omega)) hRun hpc.ge (by omega)

end PTX.Kernels.TmlFa4Fwd.Mma
