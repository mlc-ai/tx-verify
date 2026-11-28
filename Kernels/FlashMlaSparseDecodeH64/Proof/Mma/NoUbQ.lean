-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorOk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Nc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Objs
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Geometry.Maps
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Lemmas.Flow.CommitSelf
import Lemmas.Flow.Step.ElectFull
import Lemmas.Flow.Step.TcCpWs
import Lemmas.Flow.TensorIssueCopy

@[expose] public section

/-! # The MMA warp's query loads fire no undefined behaviour

-- domain: consistent

The eight tensor loads of the query tile: the map operand is the query map's descriptor slot of
`param_1` (`Pre.mapQBind`, valid), the destination and the barrier are the thread's CTA's shared
words, the box start is a multiple of 16 bytes, and the CTA routes to itself. -/

/-! # The MMA warp's states fire no undefined behaviour

-- domain: consistent

One declaration per site family, in the form of `Shape.lean`'s (`shape_open`, then the operand
checks of `NoUbOps.lean`): the event fired from the state is no fault. The loop's sites ask the
stage word to be `0` or `1` (`LoopOk`). -/

/-! # The MMA warp's instructions fire no undefined behaviour: the operand checks

-- domain: consistent

Per instruction, from the register facts of its site: a poll names an 8-byte aligned word
(`poll_nonub`, `Lib/PollNoUb.lean`), a commit is one CTA's (`commit_nonub`, `resolve_one`), a
`tcgen05.cp` and the two forms of `tcgen05.mma` have their operands and decode (`cp_nonub`,
`mmaTmem_nonub`, `mmaSmem_nonub`). Each concludes that the event is no fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A one-CTA commit of a launch of one-CTA clusters resolves. -/
theorem resolve_one (hp : Pre P L m) {c a : Nat} (hc : c < L.grid) :
    ∃ s, TcCommit.resolve L .one c ⟨.shared, c, a⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta c)) = some s := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := fun k => by
    rw [hp.clusterPlaces]
    rfl
  have hn : c < L.nclusters := by rw [hp.nclusters]; exact hc
  unfold TcCommit.resolve
  split_ifs with h
  · exact ⟨_, rfl⟩
  · exfalso
    refine h ⟨hp.launchValid.1, hc, rfl, hc, rfl, ?_⟩
    rw [Launch.rankOfCta_unit hs hn, Launch.clusterSizeOf_unit hs]
    decide

/-- **An unmasked one-CTA commit at an aligned word is no fault.** -/
theorem commit_nonub (hp : Pre P L m) {A : List Assumption} {t : TState} {base : Nat} {off : Int}
    {pc : Nat} {e : Event} {o : Option TState} {x : BitVec 64} {wx : Nat}
    (hg : g < L.threads) (hb : t.regs base = some (.bits wx x))
    (hal : (smLoc L g x off).addr % 8 = 0)
    (hf : Fires pc (eventTmpl A L g t (.tcCommit .one base off none)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  simp only [eventTmpl, tcCommitTmpl, mbarClusterLoc, sharedEffAddr, readReg, hb, readBits,
    bind, Except.bind, pure, Except.pure, hg] at hf
  simp only [smLoc] at hal
  simp only [hal, ↓reduceIte] at hf
  obtain ⟨s, hs⟩ := resolve_one
    (a := (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat) hp (cta_lt hp hg)
  rw [hs] at hf
  simp only [ofExec, Fires] at hf
  rw [hf.1]
  intro f h
  cases h

/-- A word `c` bytes above the shared base, a multiple of 8, is 8-byte aligned. -/
theorem align_sbw (hp : Pre P L m) {c : Nat} (hc : c ≤ 222944) (h8 : c % 8 = 0) :
    (smLoc L g (addi (sbw L) c) 0).addr % 8 = 0 := by
  rw [smLoc_sbw hp hc]
  obtain ⟨hA, -⟩ := base_facts hp
  simp only
  omega

/-- A word `c` bytes above a stage's base, a multiple of 8, is 8-byte aligned. -/
theorem align_bb (hp : Pre P L m) (b : Fin 2) {c : Nat} (hc : c ≤ 222936) (h8 : c % 8 = 0) :
    (smLoc L g (addi (bb L (W b.val)) c) 0).addr % 8 = 0 := by
  rw [smLoc_bb hp b hc]
  obtain ⟨hA, -⟩ := base_facts hp
  simp only
  omega

/-- A 64-bit word register as the number it holds. -/
theorem b64_of {t : TState} {r : Nat} {x : BitVec 64} (h : t.regs r = some (.bits 64 x)) :
    t.regs r = some (b64 x.toNat) := by
  simp [b64, h]

/-- A 32-bit word register as the number it holds. -/
theorem b32_of {t : TState} {r : Nat} {x : BitVec 64} (h : t.regs r = some (.bits 32 x)) :
    t.regs r = some (b32 x.toNat) := by
  simp [b32, h]

/-- **A `tcgen05.cp` of one CTA from a decoded source is no fault.** -/
theorem cp_nonub (hp : Pre P L m) {A : List Assumption} {t : TState} {ta rs : Nat}
    {xa xs w : BitVec 64} {src : TcShared.Descriptor} {pc : Nat} {e : Event} {o : Option TState}
    (hg : g < L.threads) (hA : t.regs ta = some (.bits 32 xa)) (ha : xa.toNat < 2 ^ 32)
    (hok : TcCopy.AddressOk .s128x256b xa.toNat) (hS : t.regs rs = some (.bits 64 xs))
    (hw : xs = w) (hd : TcShared.decode w.toNat = some src)
    (hf : Fires pc (eventTmpl A L g t (.tcCp .one .s128x256b ta (.reg rs) none)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  have hS' := readBits64_of (L := L) (g := g) hS
  have hc := ctaGroup_self hp (cta_lt hp hg)
  have h := tc_cp (L := L) (t := t) (sd := .reg rs) (fmt := none) hg (b32_of hA) ha hok
    (s := xs.toNat) (by rw [hS']; simp) (Nat.lt_of_lt_of_le xs.isLt (by simp)) (hw ▸ hd) hc
  simp only [eventTmpl, h, Fires] at hf
  rw [hf.1]
  intro f h
  cases h

/-- The form of the role's MMAs, with the zero-column mask descriptor `0`. -/
structure MmaFormZ (m : TcMmaInstr) (rI re : Nat) : Prop extends MmaForm m rI re where
  zcm : m.zeroColumnMask = some (.imm 0)

/-- A decoded descriptor of group `one`. -/
theorem decode_group {i : Nat} {desc : TcMma.Descriptor}
    (h : TcMma.decode .one true .f16 i = some desc) : desc.group = .one := by
  unfold TcMma.decode at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
      rfl
    · cases h

theorem zcm_ok {t : TState} {z : Option Opnd} (h : z = some (.imm 0)) :
    zeroColumnMaskOk L g t z = .ok () := by
  rw [h]
  exact zeroColumnMaskOk_imm0

/-- **An MMA with A in Tensor Memory is no fault** when its operands read and decode. -/
theorem mmaTmem_nonub (hp : Pre P L m) {A : List Assumption} {t : TState} {mi : TcMmaInstr}
    {ta rI re rb : Nat} {xd xa xi xb wb : BitVec 64} {acc : Bool} {pc : Nat} {e : Event}
    {o : Option TState} {db : TcShared.Descriptor} {desc : TcMma.Descriptor}
    (hg : g < L.threads) (hF : MmaFormZ mi rI re) (hmA : mi.a = .tmem ta 0)
    (hmB : mi.bdesc = .reg rb) (hd : t.regs mi.d = some (.bits 32 xd)) (hc : xd.toNat < 2 ^ 32)
    (hA : t.regs ta = some (.bits 32 xa)) (ha : xa.toNat < 2 ^ 32)
    (hI : t.regs rI = some (.bits 32 xi)) (hi : xi.toNat < 2 ^ 32)
    (he : t.regs re = some (.pred acc)) (hB : t.regs rb = some (.bits 64 xb))
    (hw : xb = wb) (hdb : TcShared.decode wb.toNat = some db)
    (hdi : TcMma.decode .one true .f16 xi.toNat = some desc) (ht : desc.transposeA = false)
    (hf : Fires pc (eventTmpl A L g t (.tcMma mi)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  have hcg := ctaGroup_self hp (cta_lt hp hg)
  have hs : TcMma.makeOperands L (g / L.block) desc db db =
      some ⟨desc, db, db, g / L.block, g / L.block, none, {}⟩ := by
    simp [TcMma.makeOperands, decode_group hdi, hcg]
  have h := tc_mmaTmem (L := L) (t := t) (m := mi) (ta := ta) (rB := rb) (rI := rI) (aoff := 0)
    (c := xd.toNat) (a := xa.toNat) (a' := xa.toNat) (b := xb.toNat) (i := xi.toNat)
    (ms := [0, 0, 0, 0]) (accumulate := acc) hF.rule hmA hmB hF.idesc hg (b32_of hd) hc
    (b32_of hA) ha (tmemOffset_zero _) (b64_of hB) (Nat.lt_of_lt_of_le xb.isLt (by simp))
    (b32_of hI) hi (by rw [hF.mask]; exact mask0_read)
    (by rw [hF.mask, hF.group]; rfl) (by rw [hF.enable]; exact mmaEnable_of he)
    (zcm_ok hF.zcm) (hw ▸ hdb) (by rw [hF.group, hF.ws, hF.kind]; exact hdi) ht hs
  simp only [eventTmpl, h, Fires] at hf
  rw [hf.1]
  intro f h
  cases h

/-- **An MMA with A in shared memory is no fault** when its operands read and decode. -/
theorem mmaSmem_nonub (hp : Pre P L m) {A : List Assumption} {t : TState} {mi : TcMmaInstr}
    {ra rI re rb : Nat} {xd xi xa xb wa wb : BitVec 64} {acc : Bool} {pc : Nat} {e : Event}
    {o : Option TState} {da db : TcShared.Descriptor} {desc : TcMma.Descriptor}
    (hg : g < L.threads) (hF : MmaFormZ mi rI re) (hmA : mi.a = .smem (.reg ra))
    (hmB : mi.bdesc = .reg rb) (hd : t.regs mi.d = some (.bits 32 xd)) (hc : xd.toNat < 2 ^ 32)
    (hI : t.regs rI = some (.bits 32 xi)) (hi : xi.toNat < 2 ^ 32)
    (he : t.regs re = some (.pred acc))
    (hA : t.regs ra = some (.bits 64 xa)) (hB : t.regs rb = some (.bits 64 xb))
    (hwa : xa = wa) (hwb : xb = wb) (hda : TcShared.decode wa.toNat = some da)
    (hdb : TcShared.decode wb.toNat = some db)
    (hdi : TcMma.decode .one true .f16 xi.toNat = some desc)
    (hf : Fires pc (eventTmpl A L g t (.tcMma mi)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  have hcg := ctaGroup_self hp (cta_lt hp hg)
  have hs : TcMma.makeOperands L (g / L.block) desc da db =
      some ⟨desc, da, db, g / L.block, g / L.block, none, {}⟩ := by
    simp [TcMma.makeOperands, decode_group hdi, hcg]
  have h := tc_mmaSmem (L := L) (t := t) (m := mi) (rA := ra) (rB := rb) (rI := rI)
    (c := xd.toNat) (a := xa.toNat) (b := xb.toNat) (i := xi.toNat) (ms := [0, 0, 0, 0])
    (accumulate := acc) hF.rule hmA hmB hF.idesc hg (b32_of hd) hc (b64_of hA)
    (Nat.lt_of_lt_of_le xa.isLt (by simp)) (b64_of hB)
    (Nat.lt_of_lt_of_le xb.isLt (by simp)) (b32_of hI) hi
    (by rw [hF.mask]; exact mask0_read)
    (by rw [hF.mask, hF.group]; rfl) (by rw [hF.enable]; exact mmaEnable_of he)
    (zcm_ok hF.zcm) (hwa ▸ hda) (hwb ▸ hdb) (by rw [hF.group, hF.ws, hF.kind]; exact hdi) hs
  simp only [eventTmpl, h, Fires] at hf
  rw [hf.1]
  intro f h
  cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The obligation of one site: the event is no fault. -/
abbrev NoUbAt (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (code P L g).ShapeAt (fun _ e => ∀ f, e.kind ≠ .ub f) d

theorem noUb_elect (d : D) (hs : d.site = .elect) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  obtain ⟨inst, ld, -, hk⟩ := fires_elect_full (readBits_of (rg 794)) (by decide) hf
  rw [hk]
  intro f h
  cases h

theorem noUb_loadTopk (hp : Pre P L m) (d : D) (hs : d.site = .loadTopk)
    (hok : eqz64 (pw8 (P.topkLenBase.getD 0)) = false) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  intro t ins e o hat _ hc hf
  obtain ⟨x, hx⟩ := ptr_of_ne hok
  obtain ⟨bs, hk, -⟩ := read_topk hp hx hat hc hf
  rw [hk]
  intro f h
  cases h

theorem noUb_loadExtra (hp : Pre P L m) (d : D) (hs : d.site = .loadExtra)
    (hok : eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  intro t ins e o hat _ hc hf
  obtain ⟨x, hx⟩ := ptr_of_ne hok
  obtain ⟨bs, hk, -⟩ := read_extra hp hx hat hc hf
  rw [hk]
  intro f h
  cases h

theorem noUb_qWait (hp : Pre P L m) (d : D) (hs : d.site = .qWait) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact poll_nonub (by rw [hpc]; decide) (rg 811) (rg 812)
    (align_sbw hp (by decide) (by decide)) hf

theorem noUb_qCopyWait (hp : Pre P L m) (d : D) (hs : d.site = .qCopyWait) :
    NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact poll_nonub (by rw [hpc]; decide) (rg 843) (rg 812)
    (align_sbw hp (by decide) (by decide)) hf

theorem noUb_qCopyCommit (hp : Pre P L m) (hg : g < L.threads) (d : D)
    (hs : d.site = .qCopyCommit) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  shape_open
  exact commit_nonub hp hg (rg 843) (align_sbw hp (by decide) (by decide)) hf

theorem noUb_kvWait (hp : Pre P L m) (d : D) (hs : d.site = .kvWait)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  obtain ⟨b, rfl⟩ := hb
  shape_open
  exact poll_nonub (by rw [hpc]; decide) (rg 855) (rg 879)
    (align_bb hp b (by decide) (by decide)) hf

theorem noUb_soWait (hp : Pre P L m) (d : D) (hs : d.site = .soWait)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  obtain ⟨b, rfl⟩ := hb
  shape_open
  exact poll_nonub (by rw [hpc]; decide) (rg 878) (rg 879)
    (align_bb hp b (by decide) (by decide)) hf

theorem noUb_qkCommit (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : d.site = .qkCommit)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  obtain ⟨b, rfl⟩ := hb
  shape_open
  exact commit_nonub hp hg (rg 877) (align_bb hp b (by decide) (by decide)) hf

theorem noUb_pvCommit (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : d.site = .pvCommit)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  cases hs
  obtain ⟨b, rfl⟩ := hb
  shape_open
  exact commit_nonub hp hg (rg 883) (align_bb hp b (by decide) (by decide)) hf

theorem noUb_qCopy (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : ∃ k, d.site = .qCopy k) :
    NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  have hd := cpW_decode hp (k := k.val) k.isLt
  fin_cases k <;> shape_open <;>
    exact cp_nonub hp hg rg_ (by decide) (by decide) rg_ rfl hd hf

theorem noUb_qk (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : ∃ k, d.site = .qk k)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  obtain ⟨b, rfl⟩ := hb
  have hdb := qkBW_decode hp b.isLt k.isLt
  fin_cases k <;> shape_open <;>
    exact mmaTmem_nonub hp hg ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ rfl rfl rg_
      (by decide) rg_ (by decide) rg_ (by decide) rg_ rg_ rfl hdb (desc := MmaFoot.qkD)
      (by decide) (by decide) hf

theorem noUb_pv (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : ∃ k, d.site = .pv k)
    (hb : ∃ b : Fin 2, d.pha = W b.val) : NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  obtain ⟨b, rfl⟩ := hb
  have hda := pvAW_decode hp k.isLt
  have hdb := pvBW_decode hp b.isLt k.isLt
  fin_cases k <;> shape_open <;>
    exact mmaSmem_nonub hp hg ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ rfl rfl rg_
      (by decide) rg_ (by decide) rg_ rg_ rg_ rfl rfl hda hdb (desc := MmaFoot.pvD) (by decide) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The query map operand checks.** -/
theorem qMap_ok (hp : Pre P L m) {t : TState} {cs : List Opnd}
    (hm : t.regs 3058 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + 128))))
    (hcs : cs.length = 4) :
    tensorMap L g t (.reg 3058) cs .tile =
      .ok (P.param1Base + 128,
        ⟨3, mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass⟩) := by
  have h64 : (BitVec.ofNat 64 (P.param1Base + 128)).toNat = P.param1Base + 128 := by
    have := hp.param1Range
    simp only [BitVec.toNat_ofNat]
    omega
  have hal := hp.param1Align
  unfold tensorMap
  have h1 : (P.param1Base + 128) % 64 = 0 := by omega
  have hcrd : TensorMode.tile.coordinates 3 = 4 := rfl
  simp only [bind, Except.bind, pure, Except.pure, tensorMapAddress_bits hm, h64, h1,
    ↓reduceIte, hp.mapQBind, hcs, hcrd, Geometry.mapQ_valid_of_pre hp, true_or]

/-- A 32-bit destination register as the thread's CTA's shared word. -/
theorem dst_loc' {t : TState} {r : Nat} {x : BitVec 64} (hr : t.regs r = some (.bits 32 x)) :
    sharedEffAddr L g t true r 0 = .ok ⟨.shared, g / L.block, (truncBits 32 x).toNat⟩ := by
  simp [sharedEffAddr, readReg, hr, readBits, bind, Except.bind, pure, Except.pure, truncBits]

/-- A word that is a multiple of 8 is a multiple of 16 bytes as a two-byte element origin. -/
theorem origin_align {w : Nat} (h : w % 8 = 0) :
    (BitVec.ofNat 32 w).toInt * 2 % 16 = 0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  split_ifs <;> omega

/-- **A query load is no fault.** -/
theorem qLoad_nonub (hp : Pre P L m) {t : TState} {dst r0 : Nat} {pol : Option Opnd}
    {pc : Nat} {e : Event} {o : Option TState} {x x0 x1 x2 x3 : BitVec 64} {c : Nat}
    (hg : g < L.threads) (hpol : cachePolicyRead L g t pol = .ok ())
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor true false dst 0 (.reg 3058) [.reg r0, .reg 812, .reg 459, .reg 460] 811 0 none
        .tile pol)) e o)
    (hr0 : t.regs r0 = some (.bits 32 x0)) (hr1 : t.regs 812 = some (.bits 32 x1))
    (hr2 : t.regs 459 = some (.bits 32 x2)) (hr3 : t.regs 460 = some (.bits 32 x3))
    (hm : t.regs 3058 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + 128))))
    (hb : t.regs 811 = some (.bits 32 (Arith32.addi (sbw L) 222776)))
    (hdr : t.regs dst = some (.bits 32 x)) (hx : (truncBits 32 x).toNat = L.sharedBase + c)
    (hc : c % 128 = 0) (h0 : x0.toNat % 8 = 0) : ∀ f, e.kind ≠ .ub f := by
  have hmap := qMap_ok hp (g := g) hm (cs := [.reg r0, .reg 812, .reg 459, .reg 460]) rfl
  have hvs : [Opnd.reg r0, .reg 812, .reg 459, .reg 460].mapM (readBits L g t 32) =
      .ok [truncBits 32 x0, truncBits 32 x1, truncBits 32 x2, truncBits 32 x3] := by
    simp only [List.mapM_cons, List.mapM_nil, readBits_of hr0, readBits_of hr1, readBits_of hr2,
      readBits_of hr3, bind, Except.bind, pure, Except.pure]
  have hba : TensorDescriptor.BoxAligned (TensorMode.tile.transfer
      (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass))
      (fun axis : Fin 4 => (BitVec.ofNat 32 ([truncBits 32 x0, truncBits 32 x1,
        truncBits 32 x2, truncBits 32 x3].getD axis.val 0).toNat).toInt) := by
    simp only [TensorDescriptor.BoxAligned, TensorMode.transfer]
    simp [mapQ, encodeTiled, TensorDescriptor.Format.bytes, truncBits]
    exact origin_align (by omega)
  have hcp := tensorLoadCopy_of (ca := true) (gt := false) (dst := dst) (off := 0) (mb := 811)
    (moff := 0) hmap (dst_loc' hdr) (by simp only; rw [hx]; exact base_128 hp c hc)
    (by simp only [↓reduceIte]; exact mbarClusterLoc_bits hb (sbw_m8 hp (c := 222776) (by decide)))
    hvs hba
  exact tensor_nonub hpol hcp (route_self hp (cta_lt hp hg)) hf

/-- The workspace word `n` bytes above the shared base is the base plus `n`. -/
theorem dst_addi (hp : Pre P L m) {n : Nat} (hn : n ≤ 222944) :
    (truncBits 32 (Arith32.addi (sbw L) n)).toNat = L.sharedBase + n := by
  have h := congrArg Loc.addr (smLoc_sbw (g := 0) hp hn)
  simpa [smLoc, truncBits] using h

/-- The shared base word is the base. -/
theorem dst_sbw (hp : Pre P L m) : (truncBits 32 (sbw L)).toNat = L.sharedBase + 0 := by
  have h := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  simp only [sbw, truncBits, BitVec.toNat_ofNat]
  omega

theorem noUb_qLoad (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : ∃ k, d.site = .qLoad k) :
    NoUbAt P L g d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  have hd := fun {n : Nat} (hn : n ≤ 222944) => dst_addi hp hn
  fin_cases k <;> shape_open
  · exact qLoad_nonub hp hg (pol_ok (rg 3059)) hf (rg 812) (rg 812) (rg 459) (rg 460)
      (rg 3058) (rg 811) rg_ (dst_sbw hp) (by decide) (by decide)
  all_goals
    refine qLoad_nonub hp hg (pol_ok (rg 3059)) hf rg_ (rg 812) (rg 459) (rg 460)
      (rg 3058) (rg 811) rg_ (hd ?_) ?_ ?_ <;> decide

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
