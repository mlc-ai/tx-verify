-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Assumptions
public import Lemmas.Flow.WarpUniform

@[expose] public section

/-!
# Audit: the site lists of the FA4 assumptions

Each check evaluates the decoded program. The assumptions do not depend on these theorems: each
constructor applies only at its listed sites (and `tcLdDataflowAt` only where `ldConsumedAt`
holds); the checks confirm that the lists name the instructions `DECISIONS.md` describes.
-/

namespace PTX.Kernels.FlashAttn4Fwd.Assumptions
open PTX

/-- The software-exp2 template matches at every listed site. -/
theorem swExp2Sites_match :
    swExp2Sites.all (fun pc => (Assumption.cuteExp2.matchAt kernel pc).isSome) = true := by
  decide +kernel

/-- The kernel has exactly 24 `add.rm.f32x2` instructions, one in each software-exp2 segment. -/
theorem addRm_count : (kernel.code.filter (fun i => match i.op with
    | .float i => i.op == .add && i.ty == ⟨.f32, 2⟩ && i.rnd == some .rm
    | _ => false)).length = swExp2Sites.length := by
  decide +kernel

/-- `peerBitSites` are exactly the kernel's `and.b32` with the peer-bit mask. -/
theorem peerBitSites_eq : peerBitSites = (kernel.code.zipIdx.filter (fun p => match p.1.op with
    | .int ⟨.and, .int .b 32, false, [some _], [.reg _, .imm m]⟩ => m == Assumption.peerBitMask
    | _ => false)).map (·.2) := by
  decide +kernel

/-- `tcLdSites` are exactly the kernel's `tcgen05.ld` instructions. -/
theorem tcLdSites_eq : tcLdSites = (kernel.code.zipIdx.filter (fun p => match p.1.op with
    | .tcLd .. => true
    | _ => false)).map (·.2) := by
  decide +kernel

/-- The listed sites are guarded `bra.uni` instructions on the predicate that the unguarded
`mbarrier.try_wait` right before each writes, and they are exactly the kernel's guarded `bra.uni`
instructions. With `Proof.Safety.poll_guards` (every guarded uniform instruction is a poll branch,
`Kernel.pollBranch`) they are exactly the kernel's poll branches. -/
theorem pollAgreeSites_ops :
    pollAgreeSites.all (fun pc => match kernel.code[pc]?, kernel.code[pc - 1]? with
      | some ⟨some (p, false), .bra _ true⟩, some ⟨none, .mbarWait d ..⟩ => p == d
      | _, _ => false) = true ∧
    pollAgreeSites = (kernel.code.zipIdx.filter (fun p => match p.1 with
      | ⟨some _, .bra _ true⟩ => true
      | _ => false)).map (·.2) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end PTX.Kernels.FlashAttn4Fwd.Assumptions
