-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QLoad
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QEntry

@[expose] public section

/-! # The strict query entry as far as the first query site -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem ldq0_tags : ∀ τ ∈ Data.tags (.ldq 0), τ = .scale ∨ τ = .zero := by decide +kernel

/-- **From the end of the copy tail to the first query site**: the groups before it are off. -/
theorem qentry {m} (hp : Pre Q L m) (hw : w = b32 0) (c : Control.D) (v : Data.Vals)
    (hv : ∀ k, (v.q k).bytes = 2) (hi : Nat) (hle : hi ≤ 64)
    (hoff : ∀ n, n < hi → queryOn (g % L.block) (n / 16) c = false) :
    SegQ kernel Assumptions.all L g (QT proQt) 316 ([(525, Data.scaleVal L)] ++ facts Q L g w c 316)
      (qSiteAt hi).pc (dFacts Q L g w (dq c v (qSiteAt hi))) := by
  have e1 := qe_entry (Q := Q) (L := L) (g := g) (w := w) hp hw c
  have e2 : SegQ kernel Assumptions.all L g (QT proQt) 388
      ([(198, Data.zeroV), (199, Data.zeroV), (525, Data.scaleVal L)] ++ facts Q L g w c 388) 388
      (SkipF Q L g w c v 0) := by
    refine SegQ.sub fun q hq => ?_
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
      rcases ldq0_tags τ hτ with rfl | rfl <;> simp [Data.Tag.reg, Data.Tag.val, Data.zeroV]
    · exact List.mem_append_right _ h
  refine SegQ.comp e1 (SegQ.comp e2 ?_)
  by_cases h64 : hi < 64
  · have := qs_run (Q := Q) (w := w) c v hi 0 ⟨hi, h64⟩ (by simp) fun k hk hk' => hoff k hk'
    have e : qSiteAt hi = .ldq ⟨hi, h64⟩ := by simp [qSiteAt, h64]
    rw [e]
    exact this.comp (SegQ.sub fun q hq => List.mem_cons_of_mem _ hq)
  · have : hi = 64 := by omega
    subst this
    exact qs_to_stq (w := w) c v ⟨0, by omega⟩ hv fun k _ _ => hoff k (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
