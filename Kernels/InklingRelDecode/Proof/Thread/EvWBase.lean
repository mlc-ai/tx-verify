-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WCompAll
public import Kernels.InklingRelDecode.Proof.Thread.EvWBar
public import Lemmas.Flow.Region
public import Lemmas.Flow.TcTmpl
public import Lemmas.Flow.TensorBox
public import Lemmas.Flow.Events
public import Lemmas.Flow.NotRegister

@[expose] public section

/-!
# Tools of the event shapes: the copies and the shared-symbol loads

The shape tables of the loader and the MMA warp (`EvWLoader`, `EvWMma`) are proved by
`site_shape`; this file holds the steps of the sites it does not cover, each about one kind of
instruction and stated on the registers it reads:

* a tensor load into the CTA's own shared window (`cp.async.bulk.tensor` with a 32-bit register
  destination, `.shared::cta`): the map address, the descriptor, the destination, the barrier, the
  origin from two 32-bit coordinate registers (`fires_cpTensor_cta`, `fires_kvCopy`);
  `Lemmas/Flow/TensorBox.lean` states only the cluster-address form;
* a vector load from a shared symbol (`fires_ldv_sharedSym`).

None of them mentions a program counter of the kernel.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}
  {Q : Params} {mem0 : Mem0}

/-- What a successful non-cluster tensor load's copy is made of. -/
theorem tensorLoadCopy_cta {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {a : Nat} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t false grp dst off map cs mb moff lm = .ok (a, s)) :
    sharedEffAddr L g t false dst off = .ok s.sharedBase ∧ mbarLoc L g t mb moff = .ok s.mbar ∧
      s.clusterAddress = false ∧ s.group = (if grp then .two else .one) ∧
      ∃ vs, cs.mapM (readBits L g t 32) = .ok vs ∧
        ∀ axis : Fin (s.outer + 1),
          s.origin axis = (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    Bool.false_eq_true, ↓reduceIte] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a'', outer, d'⟩ <;> rw [hm] at h
  · cases h
  rcases hd : sharedEffAddr L g t false dst off with f | dl <;> simp only [hd] at h
  · cases h
  by_cases hal : dl.addr % 128 = 0
  · simp only [hal, ↓reduceIte] at h
    rcases hb : mbarLoc L g t mb moff with f | ml <;> simp only [hb] at h
    · cases h
    rcases hv : cs.mapM (readBits L g t 32) with f | vs <;> simp only [hv] at h
    · cases h
    rcases hq : requireBoxAligned (lm.transfer d') (fun axis =>
      (BitVec.ofNat 32 (vs.getD (↑axis) 0).toNat).toInt) with f | w <;> simp only [hq] at h
    · cases h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, vs, rfl, fun _ => rfl⟩
  · simp [hal] at h

/-- **A tensor load into the CTA's own window.** A `cp.async.bulk.tensor` with a `.shared::cta`
destination register, two 32-bit coordinate registers `r0`, `r1` holding `v0`, `v1`, and no
multicast, that fires issues one copy of the map at the address its map operand evaluates to: the
map's descriptor, the destination its register evaluates to, the barrier its operand names,
non-cluster addressing, the instruction's CTA group, and the box origin `(v0, v1)` read as signed
32-bit integers. -/
theorem fires_cpTensor_cta {grp : Bool} {dst mb r0 r1 : Nat} {off moff : Int} {map : Opnd}
    {lm : TensorMode} {v0 v1 : Nat}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor false grp dst off map [.reg r0, .reg r1] mb moff
      none lm)) e (some u))
    (h0 : t.regs r0 = some (b32 v0)) (h1 : t.regs r1 = some (b32 v1)) (hv0 : v0 < 2 ^ 32)
    (hv1 : v1 < 2 ^ 32) :
    ∃ a s, e = ⟨pc, .tensorIssue a s⟩ ∧ u = next t ∧ tensorMapAddress L g t map = .ok a ∧
      (∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = lm.transfer d) ∧
      sharedEffAddr L g t false dst off = .ok s.sharedBase ∧ mbarLoc L g t mb moff = .ok s.mbar ∧
      s.clusterAddress = false ∧ s.group = (if grp then .two else .one) ∧
      (s.rows = none ↔ lm = .tile) ∧
      ∀ i : Fin (s.outer + 1), s.origin i =
        if i.val = 0 then (BitVec.ofNat 32 v0).toInt
        else if i.val = 1 then (BitVec.ofNat 32 v1).toInt else 0 := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor false grp dst off map [.reg r0, .reg r1] mb
      moff none lm)) e (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := false) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := [.reg r0, .reg r1])
    (lm := lm) with ⟨f, hT⟩ | ⟨a', s', hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, hu⟩ := hf'
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    obtain ⟨hma, -, d, hd, -, hdesc, hrows⟩ := tensorLoadCopy_ok hcopy
    obtain ⟨hdst, hmb, hca, hgrp, vs, hvs, hor⟩ := tensorLoadCopy_cta hcopy
    refine ⟨a', s', rfl, Option.some.inj hu, hma, ⟨d, hd, hdesc⟩, hdst, hmb, hca, hgrp,
      hrows, ?_⟩
    simp only [List.mapM_cons, List.mapM_nil, readBits_b32 h0 hv0, readBits_b32 h1 hv1, bind,
      Except.bind, pure, Except.pure] at hvs
    cases hvs
    intro i
    rw [hor i]
    rcases i with ⟨_ | _ | i, hi⟩
    all_goals simp [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show v0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show v1 < 18446744073709551616 by omega)]

theorem memTmpl_sharedSym {a : MemAccess} {o : Nat}
    (hr : a.rule = some .threadAccess) (hb : a.addr.base = .sharedSym o) :
    memTmpl A L g t a = accessTmpl A L g t a := by
  unfold memTmpl
  rw [hr, hb]
  split <;> simp_all

/-- **A vector load from a shared symbol.** Element `t.sub` of a 32-bit weak load from
`global_smem + o + off` reads four bytes at that address plus `4 t.sub`, as element `t.sub` of
the vector. -/
theorem fires_ldv_sharedSym {a : MemAccess} {o off : Nat}
    (hr : a.rule = some .threadAccess) (hb : a.addr.base = .sharedSym o)
    (ho : a.addr.off = (off : Int)) (hk : a.kind = .load) (hnc : a.nc = false)
    (hsp : a.space = some (.shared .cta)) (hsem : a.sem = .weak)
    (hglob : (a.nc || a.hints.globalOnly || a.vec == 8 ||
      (a.vec == 4 && a.elem.width == 64)) = false)
    (hw : a.elem.width = 32) (hb32 : L.sharedBase + o + off < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ ac bs, e = ⟨pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, g / L.block, L.sharedBase + o + off + 4 * t.sub⟩ ∧
      ac.size = 4 ∧ ac.elem = t.sub := by
  simp only [eventTmpl, memTmpl_sharedSym hr hb, accessTmpl, hk, hnc] at hf
  rw [accessAcc_of_weak hsem] at hf
  simp only [accessLoc, hsp, hb, pure, Except.pure, bind, Except.bind, hglob, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte] at hf
  split at hf
  · simp [Fires] at hf
  · rename_i ac hE
    simp only [Fires] at hf
    obtain ⟨bs, -, he, -⟩ := hf
    refine ⟨ac, bs, he, ?_⟩
    unfold elemAcc at hE
    split_ifs at hE
    cases hE
    refine ⟨?_, by simp [hw], rfl⟩
    simp only [Loc.at, wrapAddr, ho, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
      BitVec.toNat_ofInt]
    have ho' : ((off : Int) % ((2 ^ 64 : Nat) : Int)).toNat = off := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
    simp only [ho', hw]
    simp only [Nat.mod_eq_of_lt (show L.sharedBase + o < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (show L.sharedBase + o + off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hb32, Nat.mod_eq_of_lt (show L.sharedBase + o + off < 2 ^ 64 by omega)]

/-- The signed 32-bit integer a 32-bit word is. -/
def i32 (x : Nat) : Int := (BitVec.ofNat 32 x).toInt

/-- The copy a K/V tensor load into the CTA's window issues: the `kv_rows` map, the box origin
`(col, row)`, the destination and the barrier. -/
def kvCopySpec (Q : Params) (cta : Nat) (col row dst : Nat) (bar : Loc) : TensorCopy.Spec :=
  ⟨⟨1, mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass, ![i32 col, i32 row], ⟨.shared, cta, dst⟩,
    none⟩, bar, false, .one⟩

theorem fires_kvCopy (hpre : Pre Q L mem0) {dst mb rc rr dv cv rv bv : Nat}
    (hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0))
    (hd : t.regs dst = some (b32 dv)) (hb : t.regs mb = some (b32 bv))
    (hc : t.regs rc = some (b32 cv)) (hr : t.regs rr = some (b32 rv))
    (hdv : dv < 2 ^ 32) (hbv : bv < 2 ^ 32) (hcv : cv < 2 ^ 32) (hrv : rv < 2 ^ 32)
    (hf : Fires pc (eventTmpl A L g t (.cpTensor false false dst 0 (.reg 1949)
      [.reg rc, .reg rr] mb 0 none .tile)) e (some u)) :
    e = ⟨pc, .tensorIssue Q.kvMap
      (kvCopySpec Q (g / L.block) cv rv dv ⟨.shared, g / L.block, bv⟩)⟩ ∧ u = next t := by
  obtain ⟨a, s, he, hu, hma, ⟨d, hd1, hd2⟩, hdst, hmb, hca, hgrp, hrows, hor⟩ :=
    fires_cpTensor_cta hf hc hr hcv hrv
  refine ⟨?_, hu⟩
  have hsh : sharedEffAddr L g t false dst 0 = .ok ⟨.shared, g / L.block, dv⟩ := by
    have := effAddr_b32 (L := L) (g := g) (t := t) hd hdv
    simpa [effAddr] using this
  rw [hsh] at hdst
  have hbm : s.mbar = ⟨.shared, g / L.block, bv⟩ := by
    have := effAddr_b32 (L := L) (g := g) (t := t) hb hbv
    simp only [mbarLoc, this, bind, Except.bind] at hmb
    split_ifs at hmb
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at hmb; exact hmb.symm)
  have hmap' : a = Q.kvMap := by
    simp only [tensorMapAddress, readValue, readReg, hmap, hpre.paramKv, pure, Except.pure,
      bind, Except.bind] at hma
    split_ifs at hma
    all_goals first
      | (simp at hma; done)
      | (cases hma; rfl)
  subst hmap'
  simp only [Except.ok.injEq] at hdst
  have hout : s.outer = 1 := by
    have := Option.some.inj (hd1.symm.trans hpre.mapKvBind)
    exact (Sigma.mk.inj this).1
  have hdd : HEq d (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) := by
    have := Option.some.inj (hd1.symm.trans hpre.mapKvBind)
    exact (Sigma.mk.inj this).2
  rcases s with ⟨⟨o, dsc, ori, sb, rws⟩, mbr, ca', grp'⟩
  simp only at hout hd2 hdst hbm hca hgrp hrows hor hdd
  subst hout
  have hdd' : d = mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass := eq_of_heq hdd
  subst hdd'
  simp only [TensorMode.transfer] at hd2
  subst hd2 hdst hbm hca
  rw [he]
  have hgrp' : grp' = .one := by simpa using hgrp
  have hrows' : rws = none := hrows.2 trivial
  subst hgrp' hrows'
  have hori : ori = ![i32 cv, i32 rv] := by
    funext i
    rw [hor i]
    fin_cases i <;> simp [i32]
  subst hori
  rfl

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
