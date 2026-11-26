-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictB
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictBase
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictD
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictE
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictF
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.StrictLib
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part003
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part004
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part005
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part008
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part009
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part011
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part012
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part013
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part014
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part015
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part016
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part017
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part019
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part021
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part022
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part023
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part024
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part026
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part027
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part029
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.IssueNext
import Lemmas.Flow.Step.TcSteps

@[expose] public section

/-! # Warpgroup 0's strict steps: the dispatcher over the sites without data windows

`stepAtS`: every state at element 0 of a site with a pure control window has an exact step
(`Code.StepAt`). The sites with data windows (`sitePure = false`) are the strict data steps'. -/

/-! # Warpgroup 0's strict steps at the end of a block and at the exit -/

/-! # Warpgroup 0's strict steps at the sites without data (1) -/

/-! # Warpgroup 0's strict steps at the Tensor Memory loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

set_option hygiene false in
/-- A tensor-memory load site's strict step: `stepAt_tcLdS` at `pc`, next state `dn`. -/
local macro "tcLd_site " n:ident " : " site:term " => " pc:num s:term:max c:ident : command =>
  `(theorem $n (d : D) (hs : d.site = $site) (he : d.el = 0) : (code P L g w).StepAt d := by
      w0s_state d
      simp only at hs he
      subst he hs
      refine stepAt_tcLdS (pc := $pc) (dn := ⟨$s, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩)
        rfl $c (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl (by decide +kernel)
        Nat.one_pos ?_
      dsimp only [code, facts, Site.pc]
      seg_sym using w0_segS)

tcLd_site stepAt_sldfalse0S : .sld false 0 => 278 (.sld false 1) Flow.code_278
tcLd_site stepAt_sldfalse1S : .sld false 1 => 280 (.sldw) Flow.code_280
tcLd_site stepAt_sldtrue0S : .sld true 0 => 283 (.sld true 1) Flow.code_283
tcLd_site stepAt_sldtrue1S : .sld true 1 => 285 (.sldw) Flow.code_285

theorem stepAt_sldS (a : Bool) (k : Fin 2) (d : D) (hs : d.site = .sld a k) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases k <;> cases a
  · exact stepAt_sldfalse0S d hs he
  · exact stepAt_sldtrue0S d hs he
  · exact stepAt_sldfalse1S d hs he
  · exact stepAt_sldtrue1S d hs he

tcLd_site stepAt_rld0S : .rld 0 => 716 (.rldw 0) Flow.code_716
tcLd_site stepAt_rld1S : .rld 1 => 817 (.rldw 1) Flow.code_817
tcLd_site stepAt_rld2S : .rld 2 => 918 (.rldw 2) Flow.code_918
tcLd_site stepAt_rld3S : .rld 3 => 1019 (.rldw 3) Flow.code_1019

theorem stepAt_rldS (c : Fin 4) (d : D) (hs : d.site = .rld c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_rld0S d hs he
  · exact stepAt_rld1S d hs he
  · exact stepAt_rld2S d hs he
  · exact stepAt_rld3S d hs he

tcLd_site stepAt_old0S : .old 0 => 1201 (.oldw 0) Flow.code_1201
tcLd_site stepAt_old1S : .old 1 => 1361 (.oldw 1) Flow.code_1361
tcLd_site stepAt_old2S : .old 2 => 1519 (.oldw 2) Flow.code_1519
tcLd_site stepAt_old3S : .old 3 => 1676 (.oldw 3) Flow.code_1676

theorem stepAt_oldS (c : Fin 4) (d : D) (hs : d.site = .old c) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  fin_cases c
  · exact stepAt_old0S d hs he
  · exact stepAt_old1S d hs he
  · exact stepAt_old2S d hs he
  · exact stepAt_old3S d hs he

theorem stepAt_tcfaS (d : D) (hs : d.site = .tcfa) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  w0s_state d
  simp only at hs he
  subst he hs
  refine Code.StepAt.of (fun _ => ⟨_, Flow.code_275, rfl, trivial⟩)
    (Code.step_issue (C := code P L g w)
      (dn := ⟨.sld (scmpi .gt .s w 1) 0, 0, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩) Flow.code_275
      (fun hf => Code.fires_tcPlain_next (.inl rfl) hf) (fun _ => rfl) rfl rfl
      ⟨fun _ => ?_, rfl, rfl, fun _ => Nat.one_pos⟩)
  dsimp only [code, facts, Site.pc]
  seg_sym using w0_segS

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- The named barrier. -/
w0s_free stepAt_bar0S : .bar0

/-- The valid-mask poll. -/
w0s_free stepAt_wvS : .wv

/-- The QK poll. -/
w0s_free stepAt_wqS : .wq

/-- The wait of the score loads. -/
w0s_free stepAt_sldwS : .sldw

/-- The fence after the score loads. -/
w0s_free stepAt_tcfbS : .tcfb

/-- The max store. -/
w0s_free stepAt_mstS : .mst

/-- The second barrier. -/
w0s_free stepAt_bar2S : .bar2

/-- The valid-mask arrival. -/
w0s_free stepAt_arrVS : .arrV

/-- The rescale arm's closing fence. -/
w0s_free stepAt_rsfbS : .rsfb

/-- The proxy fence. -/
w0s_free stepAt_fpxS : .fpx

/-- The epilogue's first barrier. -/
w0s_free stepAt_ebar0S : .ebar0

/-- The epilogue's store. -/
w0s_free stepAt_estS : .est

/-- The epilogue's second barrier. -/
w0s_free stepAt_ebar1S : .ebar1

/-- The LSE store. -/
w0s_free stepAt_lseS : .lse

/-- The poll before the output. -/
w0s_free stepAt_wsvS : .wsv

/-- The commit. -/
w0s_free stepAt_commitS : .commit

/-- The final barrier. -/
w0s_free stepAt_ebarS : .ebar

/-- The deallocation. -/
w0s_free stepAt_deallocS : .dealloc

/-- The bulk wait. -/
w0s_free stepAt_bwaitS : .bwait

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **The exit**: no event follows. -/
theorem stepAt_exitS (d : D) (hs : d.site = .exit) : (code P L g w).StepAt d := by
  have hp : (code P L g w).pc d = 3611 := by show d.site.pc = 3611; rw [hs]; rfl
  refine ⟨fun _ => ⟨⟨none, .ret⟩, by rw [hp]; exact Flow.code_3611, rfl, trivial⟩,
    fun ins _ _ hc hf => ?_⟩
  rw [hp, Flow.code_3611] at hc
  obtain rfl := Option.some.inj hc
  simp [eventTmpl, Fires] at hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {m : Mem0}

/-- The sites whose window to the next event touches no data register. -/
def sitePure : Site → Bool
  | .smr | .sink | .arrL | .vm | .bar1 | .mld | .vote | .rsf | .eld | .efa | .arrS => false
  | .pld _ | .rldw _ | .oldw _ => false
  | .pst k => k.val == 7
  | _ => true

/-- **Warpgroup 0's strict steps at the pure sites.** -/
theorem stepAtS (hp : Pre P L m) (d : D) (hpu : sitePure d.site = true) (he : d.el = 0) :
    (code P L g w).StepAt d := by
  cases hs : d.site <;> rw [hs] at hpu <;> try exact absurd hpu (by decide)
  case pld _ => exact absurd hpu (by simp [sitePure])
  case rldw _ => exact absurd hpu (by simp [sitePure])
  case oldw _ => exact absurd hpu (by simp [sitePure])
  case lenA => exact stepAt_lenAS hp d hs he
  case lenB => exact stepAt_lenBS d hs he
  case bwait => exact stepAt_bwaitS d hs he
  case bar0 => exact stepAt_bar0S d hs he
  case wv => exact stepAt_wvS d hs he
  case wq => exact stepAt_wqS d hs he
  case tcfa => exact stepAt_tcfaS d hs he
  case sld a k => exact stepAt_sldS a k d hs he
  case sldw => exact stepAt_sldwS d hs he
  case tcfb => exact stepAt_tcfbS d hs he
  case pst k =>
    obtain rfl : k = 7 := Fin.ext (by simpa [sitePure] using hpu)
    exact stepAt_pst7S d hs he
  case mst => exact stepAt_mstS d hs he
  case bar2 => exact stepAt_bar2S d hs he
  case arrV => exact stepAt_arrVS d hs he
  case ost k => exact stepAt_ostS k d hs
  case rld c => exact stepAt_rldS c d hs he
  case rst c => exact stepAt_rstS c d hs he
  case rstw c => exact stepAt_rstwS c d hs he
  case rsfb => exact stepAt_rsfbS d hs he
  case fpx => exact stepAt_fpxS d hs he
  case ebar0 => exact stepAt_ebar0S d hs he
  case est => exact stepAt_estS d hs he
  case ebar1 => exact stepAt_ebar1S d hs he
  case lse => exact stepAt_lseS d hs he
  case wsv => exact stepAt_wsvS d hs he
  case old c => exact stepAt_oldS c d hs he
  case ost2 c k => exact stepAt_ost2S c k d hs
  case ofpx c => exact stepAt_ofpxS c d hs he
  case obar c => exact stepAt_obarS c d hs he
  case oel c => exact stepAt_oelS c d hs he
  case otma c => exact stepAt_otmaS c d hs he
  case commit => exact stepAt_commitS d hs he
  case ebar => exact stepAt_ebarS d hs he
  case dealloc => exact stepAt_deallocS d hs he
  case exit => exact stepAt_exitS d hs

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
