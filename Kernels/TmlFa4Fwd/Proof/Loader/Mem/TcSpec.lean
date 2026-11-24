-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Tc
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSite

@[expose] public section

/-! # What warp 14's tensor copies issue

At copy `c` of TMA group `t` a lane issues the copy of its decoded site (`siteOf t c`): through the
launch's Q or Bias map, a box at the signed values of the site's column, row and
head registers, into the CTA's shared window at the site's offset (`tc_spec`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- **What a tensor copy issues** from thread state `t`: the copy of site `j` at a box whose origin
is the signed values of the site's coordinate registers. -/
def TcIssue (p : Params) (L : Launch) (g : Nat) (j : Fin 14) (t : TState) (e : Event) : Prop :=
  ∃ (xc xr xh : BitVec 64) (mb : Loc), t.regs (inputSite j).colReg = some (.bits 32 xc) ∧
    t.regs (inputSite j).rowReg = some (.bits 32 xr) ∧ t.regs 7169 = some (.bits 32 xh) ∧
    e.kind = .tensorIssue (inputMapAddress p (inputSite j))
      ⟨⟨2, inputMap p (inputSite j), boxOrigin xc xr xh,
        ⟨.shared, g / L.block, L.sharedBase + (inputSite j).sharedOffset⟩, none⟩, mb, false, .one⟩

theorem site_bounds (j : Fin 14) : ((inputSite j).sharedOffset : Int) % 128 = 0 ∧
    (inputSite j).sharedOffset ≤ 216064 ∧ ((inputSite j).barrierOffset : Int) % 8 = 0 := by
  revert j; decide

/-- The issue of one site, from its registers. -/
theorem tc_issue (hp : Pre p L m) (hg : g < L.threads) {A : List Assumption} (j : Fin 14)
    {t : TState} {pc : Nat} {e : Event} {o : Option TState} {xc xr xh xb xp : BitVec 64}
    (hmap : tensorMap L g t (.reg (inputSite j).mapReg)
      [.reg (inputSite j).colReg, .reg (inputSite j).rowReg, .reg 7169] .tile =
        .ok (inputMapAddress p (inputSite j), ⟨2, inputMap p (inputSite j)⟩))
    (h2535 : t.regs 2535 = some (b32 L.sharedBase))
    (hc : t.regs (inputSite j).colReg = some (.bits 32 xc)) (hcal : Al 3 xc)
    (hr : t.regs (inputSite j).rowReg = some (.bits 32 xr)) (hh : t.regs 7169 = some (.bits 32 xh))
    (hb : t.regs (inputSite j).barrierReg = some (.bits 32 xb)) (hbal : Al 3 xb)
    (hpol : t.regs (inputSite j).policyReg = some (.bits 64 xp))
    (hf : Fires pc (eventTmpl A L g t (.cpTensor false false 2535 (inputSite j).sharedOffset
      (.reg (inputSite j).mapReg) [.reg (inputSite j).colReg, .reg (inputSite j).rowReg, .reg 7169]
      (inputSite j).barrierReg (inputSite j).barrierOffset none .tile
      (some (.reg (inputSite j).policyReg)))) e o) :
    TcIssue p L g j t e := by
  obtain ⟨h1, h2, h3⟩ := site_bounds j
  have hfmt : (inputMap p (inputSite j)).format = .bf16 := by
    unfold inputMap; split <;> rfl
  rw [tc_tmpl hp hg hmap hfmt h2535 ⟨Int.natCast_nonneg _, by simpa using h2, h1⟩ hc hcal hr hh hb
    hbal ⟨Int.natCast_nonneg _, h3⟩ hpol] at hf
  simp only [Fires] at hf
  exact ⟨xc, xr, xh, _, hc, hr, hh, by rw [hf.1]; rfl⟩

set_option hygiene false in
macro "spec_site " n:ident tt:num c:num j:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {kk : Fin 2} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.tc $tt $c, v, kk⟩ t)
    (hc : kernel.code[(Site.tc $tt $c).pc]? = some ins)
    (hf : Fires (Site.tc $tt $c).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    TcIssue p L g $j t e := by
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hsb : Al 3 (Mma.sbW L) := by
    have := hp.shared.1
    unfold Al Mma.sbW; simp only [BitVec.toNat_ofNat]; omega
  exact tc_issue hp hg $j (inputMapReady hp (s := inputSite $j) (lreg h (by lit_mem) rfl))
    (lreg h (by lit_mem) rfl) (lreg h (by lit_mem) rfl) (by al3_tac) (lreg h (by lit_mem) rfl)
    (lreg h (by lit_mem) rfl) (lreg h (by lit_mem) rfl) (by al3_tac) (lreg h (by lit_mem) rfl) hf)

spec_site spec_0_0 0 0 0
spec_site spec_0_1 0 1 1
spec_site spec_1_0 1 0 2
spec_site spec_1_1 1 1 3
spec_site spec_2_0 2 0 4
spec_site spec_2_1 2 1 5
spec_site spec_3_0 3 0 6
spec_site spec_3_1 3 1 7
spec_site spec_4_0 4 0 8
spec_site spec_4_1 4 1 9
spec_site spec_5_0 5 0 10
spec_site spec_5_1 5 1 11
spec_site spec_6_0 6 0 12
spec_site spec_6_1 6 1 13

set_option maxHeartbeats 4000000 in
/-- **What a tensor copy of warp 14 issues.** -/
theorem tc_spec (hp : Pre p L m) (hg : g < L.threads) {tt : Fin 7} {c : Fin 2} {v : V}
    {kk : Fin 2} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.tc tt c, v, kk⟩ t)
    (hc : kernel.code[(Site.tc tt c).pc]? = some ins)
    (hf : Fires (Site.tc tt c).pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    TcIssue p L g (siteOf tt c) t e := by
  fin_cases tt <;> fin_cases c
  · exact spec_0_0 hp hg h hc hf
  · exact spec_0_1 hp hg h hc hf
  · exact spec_1_0 hp hg h hc hf
  · exact spec_1_1 hp hg h hc hf
  · exact spec_2_0 hp hg h hc hf
  · exact spec_2_1 hp hg h hc hf
  · exact spec_3_0 hp hg h hc hf
  · exact spec_3_1 hp hg h hc hf
  · exact spec_4_0 hp hg h hc hf
  · exact spec_4_1 hp hg h hc hf
  · exact spec_5_0 hp hg h hc hf
  · exact spec_5_1 hp hg h hc hf
  · exact spec_6_0 hp hg h hc hf
  · exact spec_6_1 hp hg h hc hf

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
