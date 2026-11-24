-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WordAlign
public import Kernels.TmlFa4Fwd.Proof.Loader.Input
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSite
public import Lemmas.Flow.Step.ShapeAsync
public import Lemmas.Flow.Step.ShapeRegs
import Kernels.TmlFa4Fwd.Flow.Code.Part010
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part018
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Lemmas.Flow.LoadShared

@[expose] public section

/-! # Warp 14's tensor copies are no undefined behaviour

Each of the 14 tensor copies (`tc`) is one of the decoded Q and Bias loads (`inputSite`): its map
register holds the ABI's parameter pointer, which resolves to the launch's Q or Bias map
(`Loader.inputMapReady`); its destination is the shared base plus a multiple of 128 below the
shared window's end; its barrier the shared base plus a multiple of 8; its column word a multiple
of 8 for every value of the tile's words (the Q columns are 0 and 64, the Bias columns
`1152 - 128 max(r29, 0)` and the like, multiples of 64 modulo `2 ^ 32`), so the `bf16` box start
is 16-byte aligned; the route is the issuing CTA's (`tc_ok`). No range of the tile's words is
needed: a negative column is a box partly outside the tensor, which the map fills. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem al_sub32 {x y : BitVec 64} (hx : Al 3 x) (hy : Al 3 y) : Al 3 (sub32 x y) := by
  unfold Al at *
  simp only [sub32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_sub]
  omega

theorem al_max32 {k : Nat} {x y : BitVec 64} (hx : Al k (r32 x)) (hy : Al k (r32 y)) :
    Al k (max32 x y) := by
  unfold max32; split <;> assumption

/-- A shared effective address of a word that is a multiple of 8, plus a multiple of 8, is a
multiple of 8. -/
theorem eff_al8 {x : BitVec 64} {off : Int} (hx : Al 3 x) (h8 : off % 8 = 0) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0 := by
  unfold Al at hx
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have e : ((off % ((2 ^ 64 : Nat) : Int)).toNat) % 8 = 0 := by omega
  generalize (off % ((2 ^ 64 : Nat) : Int)).toNat = b at e ⊢
  have : x.toNat % 8 = 0 := by omega
  omega

/-- The box origin of a tensor copy from its coordinate words: their signed 32-bit values. -/
def boxOrigin (xc xr xh : BitVec 64) : Fin 3 → Int := fun axis =>
  (BitVec.ofNat 32
    ([truncBits 32 xc, truncBits 32 xr, truncBits 32 xh].getD axis.val 0).toNat).toInt

set_option maxHeartbeats 2000000 in
/-- **A tensor copy of the decoded form issues its box** when its map resolves to a launch
descriptor of `bf16` elements, its destination is the shared base plus a multiple of 128 inside
the window, its column word is a multiple of 8, its barrier address a multiple of 8 and its
operands are defined. -/
theorem tc_tmpl (hp : Pre p L m) (hg : g < L.threads) {A : List Assumption} {t : TState}
    {so bo : Int} {mr cr rr br pr addr : Nat} {desc : TensorDescriptor.Descriptor 2}
    {xc xr xh xb xp : BitVec 64}
    (hmap : tensorMap L g t (.reg mr) [.reg cr, .reg rr, .reg 7169] .tile = .ok (addr, ⟨2, desc⟩))
    (hfmt : desc.format = .bf16)
    (h2535 : t.regs 2535 = some (b32 L.sharedBase))
    (hso : 0 ≤ so ∧ so.toNat ≤ 216064 ∧ so % 128 = 0)
    (hc : t.regs cr = some (.bits 32 xc)) (hcal : Al 3 xc)
    (hr : t.regs rr = some (.bits 32 xr)) (hh : t.regs 7169 = some (.bits 32 xh))
    (hb : t.regs br = some (.bits 32 xb)) (hbal : Al 3 xb) (hbo : 0 ≤ bo ∧ bo % 8 = 0)
    (hpol : t.regs pr = some (.bits 64 xp)) :
    eventTmpl A L g t (.cpTensor false false 2535 so (.reg mr)
      [.reg cr, .reg rr, .reg 7169] br bo none .tile (some (.reg pr))) =
      .tensorIssue addr ⟨⟨2, desc, boxOrigin xc xr xh,
        ⟨.shared, g / L.block, L.sharedBase + so.toNat⟩, none⟩, smLoc L g xb bo, false,
        .one⟩ (next t) := by
  have hSh := hp.shared.2.1
  have hSb := hp.shared.1
  obtain ⟨hs0, hs1, hs2⟩ := hso
  have hBound : L.sharedBase + so.toNat < 2 ^ 32 := by omega
  have hso' : so = ((so.toNat : Nat) : Int) := (Int.toNat_of_nonneg hs0).symm
  have hD : sharedEffAddr L g t false 2535 so =
      .ok ⟨.shared, g / L.block, L.sharedBase + so.toNat⟩ := by
    rw [hso']
    rw [Int.toNat_natCast]
    exact effAddr_b32_off h2535 hBound
  have hDAlign : (L.sharedBase + so.toNat) % 128 = 0 := by omega
  have hM := mbarLoc_bits (L := L) (g := g) (off := bo) hb (eff_al8 hbal hbo.2)
  have hCs : [Opnd.reg cr, .reg rr, .reg 7169].mapM (readBits L g t 32) =
      .ok [truncBits 32 xc, truncBits 32 xr, truncBits 32 xh] := by
    simp [List.mapM_cons, List.mapM_nil, readBits, readReg, hc, hr, hh, bind, Except.bind,
      pure, Except.pure]
  have hBox : TensorDescriptor.BoxAligned desc
      (fun axis : Fin 3 => (BitVec.ofNat 32
        ([truncBits 32 xc, truncBits 32 xr, truncBits 32 xh].getD axis.val 0).toNat).toInt) := by
    unfold TensorDescriptor.BoxAligned
    rw [hfmt]
    simp only [TensorDescriptor.Format.bytes, Fin.val_zero, List.getD_cons_zero]
    unfold Al at hcal
    have h8 : (truncBits 32 xc).toNat % 8 = 0 := by
      simp only [truncBits, BitVec.toNat_ofNat]; omega
    have hlt : (truncBits 32 xc).toNat < 2 ^ 32 := by
      simp only [truncBits, BitVec.toNat_ofNat]; omega
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    generalize (truncBits 32 xc).toNat = n at h8 hlt
    rw [Nat.mod_eq_of_lt hlt]
    split <;> omega
  have hAlign := (requireBoxAligned_eq_ok desc _).mpr hBox
  have hLoad : tensorLoadCopy L g t false false 2535 so (.reg mr)
      [.reg cr, .reg rr, .reg 7169] br bo .tile =
        .ok (addr, ⟨⟨2, desc, fun axis : Fin 3 => (BitVec.ofNat 32
          ([truncBits 32 xc, truncBits 32 xr, truncBits 32 xh].getD axis.val 0).toNat).toInt,
          ⟨.shared, g / L.block, L.sharedBase + so.toNat⟩, none⟩, smLoc L g xb bo, false,
          .one⟩) := by
    simp only [tensorLoadCopy, hmap, hD, bind, Except.bind, pure, Except.pure]
    simp only [hDAlign, Bool.false_eq_true, ↓reduceIte, hM, hCs, TensorMode.transfer,
      TensorMode.rowCoordinates, hAlign]
  have hPolicyRead : cachePolicyRead L g t (some (.reg pr)) = .ok () := by
    simp [cachePolicyRead, readBits, readReg, hpol, bind, Except.bind, pure, Except.pure]
  have hCta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCl : CtaInCluster L (g / L.block) (g / L.block) := ⟨hCta, hCta, rfl⟩
  have hGrid : L.clusterGridValid := hp.launch.1
  have hRoute : TensorRoute L (g / L.block) false .one
      ⟨.shared, g / L.block, L.sharedBase + so.toNat⟩ (smLoc L g xb bo) :=
    ⟨hGrid, rfl, rfl, hCl, hCl, fun _ => ⟨rfl, rfl⟩, (sameCtaGroup_iff L .one _ _).2 ⟨hCl, rfl⟩⟩
  have hE : eventTmpl A L g t (.cpTensor false false 2535 so (.reg mr)
      [.reg cr, .reg rr, .reg 7169] br bo none .tile (some (.reg pr))) =
      tensorTmpl L g t (.cpTensor false false 2535 so (.reg mr)
      [.reg cr, .reg rr, .reg 7169] br bo none .tile (some (.reg pr))) := rfl
  rw [hE, show boxOrigin xc xr xh = fun axis : Fin 3 => (BitVec.ofNat 32
    ([truncBits 32 xc, truncBits 32 xr, truncBits 32 xh].getD axis.val 0).toNat).toInt from rfl]
  simp [tensorTmpl, hPolicyRead, hLoad, hRoute, bind, Except.bind, pure, Except.pure, ofExec]

/-- **A tensor copy of the decoded form has a rule.** -/
theorem tc_ok (hp : Pre p L m) (hg : g < L.threads) {A : List Assumption} {t : TState}
    {so bo : Int} {mr cr rr br pr addr : Nat} {desc : TensorDescriptor.Descriptor 2}
    {xc xr xh xb xp : BitVec 64} {f : Fault}
    (hu : eventTmpl A L g t (.cpTensor false false 2535 so (.reg mr)
      [.reg cr, .reg rr, .reg 7169] br bo none .tile (some (.reg pr))) = .ub f)
    (hmap : tensorMap L g t (.reg mr) [.reg cr, .reg rr, .reg 7169] .tile = .ok (addr, ⟨2, desc⟩))
    (hfmt : desc.format = .bf16)
    (h2535 : t.regs 2535 = some (b32 L.sharedBase))
    (hso : 0 ≤ so ∧ so.toNat ≤ 216064 ∧ so % 128 = 0)
    (hc : t.regs cr = some (.bits 32 xc)) (hcal : Al 3 xc)
    (hr : t.regs rr = some (.bits 32 xr)) (hh : t.regs 7169 = some (.bits 32 xh))
    (hb : t.regs br = some (.bits 32 xb)) (hbal : Al 3 xb) (hbo : 0 ≤ bo ∧ bo % 8 = 0)
    (hpol : t.regs pr = some (.bits 64 xp)) : False := by
  rw [tc_tmpl hp hg hmap hfmt h2535 hso hc hcal hr hh hb hbal hbo hpol] at hu
  cases hu

/-- `Al 3` of the tile's column words: the closure of `WordAlign.lean` with subtraction. -/
macro "al3_tac" : tactic => `(tactic| repeat (first | (with_reducible apply al_sub32) | al_step))

set_option hygiene false in
/-- The theorem of one tensor copy (`j`: its decoded load). -/
macro "tc_site " n:ident tt:num c:num j:num : command => `(
set_option maxHeartbeats 4000000 in
theorem $n (hp : Pre p L m) (hg : g < L.threads) {v : V} {kk : Fin 2} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.tc $tt $c, v, kk⟩ t)
    (hc : kernel.code[(Site.tc $tt $c).pc]? = some ins)
    (hf : Fires (Site.tc $tt $c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  intro hk
  have hu := fires_ub hf hk
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hsb : Al 3 (Mma.sbW L) := by
    have := hp.shared.1
    unfold Al Mma.sbW; simp only [BitVec.toNat_ofNat]; omega
  exact tc_ok hp hg hu
    (inputMapReady hp (s := inputSite $j)
      (lreg h (by lit_mem) rfl)) rfl (lreg h (by lit_mem) rfl) (by decide)
    (lreg h (by lit_mem) rfl) (by al3_tac) (lreg h (by lit_mem) rfl) (lreg h (by lit_mem) rfl)
    (lreg h (by lit_mem) rfl) (by al3_tac) (by decide) (lreg h (by lit_mem) rfl))

tc_site tc_0_0 0 0 0
tc_site tc_0_1 0 1 1
tc_site tc_1_0 1 0 2
tc_site tc_1_1 1 1 3
tc_site tc_2_0 2 0 4
tc_site tc_2_1 2 1 5
tc_site tc_3_0 3 0 6
tc_site tc_3_1 3 1 7
tc_site tc_4_0 4 0 8
tc_site tc_4_1 4 1 9
tc_site tc_5_0 5 0 10
tc_site tc_5_1 5 1 11
tc_site tc_6_0 6 0 12
tc_site tc_6_1 6 1 13

set_option maxHeartbeats 4000000 in
/-- **No tensor copy of warp 14 is undefined behaviour.** -/
theorem tc_safe (hp : Pre p L m) (hg : g < L.threads) {tt : Fin 7} {c : Fin 2} {v : V}
    {kk : Fin 2} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD ⟨.tc tt c, v, kk⟩ t)
    (hc : kernel.code[(Site.tc tt c).pc]? = some ins)
    (hf : Fires (Site.tc tt c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  fin_cases tt <;> fin_cases c
  · exact tc_0_0 hp hg h hc hf f
  · exact tc_0_1 hp hg h hc hf f
  · exact tc_1_0 hp hg h hc hf f
  · exact tc_1_1 hp hg h hc hf f
  · exact tc_2_0 hp hg h hc hf f
  · exact tc_2_1 hp hg h hc hf f
  · exact tc_3_0 hp hg h hc hf f
  · exact tc_3_1 hp hg h hc hf f
  · exact tc_4_0 hp hg h hc hf f
  · exact tc_4_1 hp hg h hc hf f
  · exact tc_5_0 hp hg h hc hf f
  · exact tc_5_1 hp hg h hc hf f
  · exact tc_6_0 hp hg h hc hf f
  · exact tc_6_1 hp hg h hc hf f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
