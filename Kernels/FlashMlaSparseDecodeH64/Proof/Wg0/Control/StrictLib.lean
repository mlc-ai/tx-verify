-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # Warpgroup 0's strict steps: kinds

`stepAt_tcLdS`: a Tensor Memory load into registers the control facts do not name continues to
the successor `dn` whatever it loads, the successor's facts being the state's (the load writes
data registers only), reached by the exact segment `hseg`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **A Tensor Memory load**: the strict step. -/
theorem stepAt_tcLdS {d dn : D} {pc : Nat} {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hpc : d.site.pc = pc) (hc : kernel.code[pc]? = some ⟨none, .tcLd ds ta sh⟩)
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hn : ∀ a vals, (code P L g w).next d ⟨pc, .tc (.ld a vals sh)⟩ = some (some dn))
    (hs : d.el = 0) (hs' : dn.el = 0) (hoff : ∀ r ∈ ctlLive pc, r ∉ ds)
    (hdn : dn.el < elems dn.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (d.site.pc + 1) ((code P L g w).facts d)
      dn.site.pc ((code P L g w).facts dn)) :
    (code P L g w).StepAt d := by
  subst hpc
  refine Code.StepAt.of (fun _ => ⟨_, hc, rfl, trivial⟩)
    (Code.step_tcLd (C := code P L g w) (nv := fun _ => some (some dn)) (gd := none)
      (F' := fun _ => (code P L g w).facts d) hc hsh (noLdWait _) hn
      hs (by simp only [D.acc, hs, ↓reduceIte]) ?_
      (fun _ => by simp) ?_)
  · intro t vals d' _ _ hh
    exact holds_setRegs_frame (live := ctlLive d.site.pc) (val := valueOf P L g w d)
      (val' := valueOf P L g w d) hh (fun r hr => ⟨hoff r hr, hr, rfl⟩)
  · intro vals d' hd
    obtain rfl := Option.some.inj (Option.some.inj hd)
    exact ⟨fun _ => hseg, hs', by simp only [D.acc, hs', ↓reduceIte], fun _ => hdn⟩

/-- A site that is no peer read has an empty accumulator. -/
theorem acc_nil_nopld {d : D} (hnp : ∀ k, d.site ≠ .pld k) : D.acc d = [] := by
  unfold D.acc
  split
  · rfl
  · split
    · rename_i k hk
      exact absurd hk (hnp k)
    · rfl

/-- **A vector store of `n` elements**: the first three elements stay at the instruction, the last
goes on to `s` by the exact segment `hseg`. -/
theorem stepAt_stS {d : D} {pc : Nat} {gd : Option (Nat × Bool)} {a : MemAccess} {s : Site}
    {n : Nat}
    (hpc : d.site.pc = pc) (hc : kernel.code[pc]? = some ⟨gd, .mem a⟩) (hk : a.kind = .store)
    (hl : (Op.mem a).isLocal = false) (hlen : a.srcs.length = n) (he : elems d.site = n)
    (hnp : ∀ k, d.site ≠ .pld k)
    (hg : Code.GuardTrue ((code P L g w).facts d) gd) (hs0 : 0 < elems s)
    (hsd : ∀ e, (code P L g w).next d e = some (some (elemNext d n s)))
    (hseg : ∃ m, Seg kernel Assumptions.all L g m (pc + 1) ((code P L g w).facts d)
      s.pc ((code P L g w).facts { d with site := s, el := 0 })) :
    (code P L g w).StepAt d := by
  subst hpc
  refine Code.StepAt.of (fun _ => ⟨_, hc, hl, hg⟩) ?_
  by_cases h3 : d.el + 1 < n
  · refine Code.step_vec_mid (C := code P L g w) (dn := { d with el := d.el + 1 }) hc hk
      (by simp only; omega) (fun e => ?_) rfl rfl ?_ rfl (fun h => ?_)
    · rw [hsd e]; simp only [elemNext, h3, ↓reduceIte]
    · exact (acc_nil_nopld (d := { d with el := d.el + 1 }) hnp).trans (acc_nil_nopld hnp).symm
    · simp only at h ⊢; omega
  · refine Code.step_vec_last (C := code P L g w) (dn := { d with site := s, el := 0 }) hc hk
      (by simp only; omega) (fun e => ?_) (acc_nil_nopld hnp)
      ⟨fun _ => hseg, rfl, by simp [D.acc], fun _ => hs0⟩
    · rw [hsd e]; simp only [elemNext, h3, ↓reduceIte]

/-- **A Tensor Memory store** (no implicit wait): the strict step. -/
theorem stepAt_tcStS {d dn : D} {pc : Nat} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hpc : d.site.pc = pc) (hc : kernel.code[pc]? = some ⟨none, .tcSt ta ss sh⟩)
    (hw : Assumptions.all.any (·.tcStWaitLd pc) = false)
    (hn : ∀ e, (code P L g w).next d e = some (some dn)) (hs : d.el = 0) (hs' : dn.el = 0)
    (hdn : dn.el < elems dn.site)
    (hseg : ∃ n, Seg kernel Assumptions.all L g n (pc + 1) ((code P L g w).facts d)
      dn.site.pc ((code P L g w).facts dn)) :
    (code P L g w).StepAt d := by
  subst hpc
  refine Code.StepAt.of (fun _ => ⟨_, hc, rfl, trivial⟩)
    (Code.step_issueAt (C := code P L g w) (ins0 := ⟨none, .tcSt ta ss sh⟩) hc ?_ hn hs
      (by simp only [D.acc, hs, ↓reduceIte]) ⟨fun _ => hseg, hs', ?_, fun _ => hdn⟩)
  · intro t e u ht hf
    exact fires_tcSt_next (by rw [ht]; exact hw) hf
  · simp only [D.acc, hs', ↓reduceIte]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
