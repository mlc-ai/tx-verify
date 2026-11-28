-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.NcRead
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Geometry.Maps
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorOk
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.GatherDst
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Lemmas.Flow.Step.ElectFull
import Lemmas.Flow.Step.RdNoUb
import Lemmas.Flow.TensorIssueCopy

@[expose] public section

/-! # The TMA warp's gathers fire no undefined behaviour

-- domain: consistent

A gather4 load reads a cache map of `param_1` (the main one, or the extra one when the extra cache
is on), writes the thread's CTA's raw tile at an address multiple of 128, signals the raw tile's
barrier and takes the column `0` and the four row words the coordinate loads kept, which read as
32-bit words (`CoordInv`). -/

/-! # The TMA warp's states fire no undefined behaviour: the operand checks

-- domain: consistent

One declaration per site family: the event fired from the state is no fault. The election's mask
is the full warp; a length load reads the row's word through a set pointer (`Tma.topk_read`); the
polls name 8-byte aligned words; a coordinate element reads at a 16-byte aligned address. -/

/-! # The coordinate words the TMA state keeps are 32-bit words

`CoordInv d`: at a coordinate load of quadruple `k >= 1` the last loaded quadruple (`cq`) is four
32-bit words, the elements already loaded (`ac`) are 32-bit words, and at a gather both kept
quadruples are. A coordinate element's loaded value is a 32-bit word when its bytes rebuild one
(`coordInv_succ`), so the invariant is kept along the lane's states; the gathers' coordinate
registers then read as 32-bit words (`Tma/NoUbGather.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A 32-bit word. -/
def Bits32 (v : Value) : Prop := ∃ z, v = .bits 32 z

/-- A quadruple of 32-bit words. -/
def QuadBits (q : Quad) : Prop := Bits32 q.w0 ∧ Bits32 q.w1 ∧ Bits32 q.w2 ∧ Bits32 q.w3

/-- **The coordinate words are 32-bit words** where the machine reads them. -/
def CoordInv (d : D) : Prop :=
  match d.site with
  | .coord0 k => 1 ≤ k.val → QuadBits d.cq
  | .coord1 k => (1 ≤ k.val → QuadBits d.cq) ∧ Bits32 d.ac.w0
  | .coord2 k => (1 ≤ k.val → QuadBits d.cq) ∧ Bits32 d.ac.w0 ∧ Bits32 d.ac.w1
  | .coord3 k => (1 ≤ k.val → QuadBits d.cq) ∧ Bits32 d.ac.w0 ∧ Bits32 d.ac.w1 ∧ Bits32 d.ac.w2
  | .gather _ => QuadBits d.cp ∧ QuadBits d.cq
  | _ => True

variable {P : Params} {L : Launch} {g : Nat}

/-- A coordinate element's successor holds the 32-bit word its bytes rebuild. -/
theorem rdAny_bits {e : Event} {F : Value → D} {a : D}
    (hrd : ∀ x bs, e.kind = .rd x bs → ∃ z, rebuild 3 bs = .ok (.bits 32 z))
    (h : rdAny e F = some (some a)) : ∃ z, a = F (.bits 32 z) := by
  unfold rdAny at h
  split at h
  · rename_i x bs hk
    obtain ⟨z, hz⟩ := hrd x bs hk
    simp only [hz, Except.toOption, Option.getD_some, Option.some.injEq] at h
    exact ⟨z, h.symm⟩
  · cases h

theorem poll_succ {d d' a : D} {e : Event} (h : poll d e d' = some (some a)) :
    a = d ∨ a = d' := by
  unfold poll at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    split <;> simp
  · cases h

theorem ncWord_succ {e : Event} {F : BitVec 64 → D} {a : D}
    (h : ncWord e F = some (some a)) : ∃ x, a = F x := by
  unfold ncWord at h
  split at h
  · split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, h.symm⟩
      · cases h
    · cases h
  · cases h

theorem electNext_succ {d a : D} {e : Event} (h : electNext P L g d e = some (some a)) :
    a = leadNext P L g d ∨ ∃ s, a = { d with site := .leave s } := by
  unfold electNext at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    split
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩
  · cases h

/-- A state whose invariant is vacuous: no gather and no load past the first quadruple's. -/
def Free (d : D) : Prop :=
  match d.site with
  | .coord0 k => k.val = 0
  | .coord1 _ | .coord2 _ | .coord3 _ | .gather _ => False
  | _ => True

theorem coordInv_of_free {d : D} (h : Free d) : CoordInv d := by
  unfold Free at h
  unfold CoordInv
  split <;> simp_all

/-- A coordinate load's site. -/
def IsCoord (s : Site) : Prop :=
  ∃ k, s = .coord0 k ∨ s = .coord1 k ∨ s = .coord2 k ∨ s = .coord3 k

/-- **The invariant is kept by a step** whose coordinate elements rebuild 32-bit words. -/
theorem coordInv_succ {d a : D} {f : Event} (hI : CoordInv d)
    (hrd : IsCoord d.site → ∀ x bs, f.kind = .rd x bs → ∃ z, rebuild 3 bs = .ok (.bits 32 z))
    (ha : succ P L g d f = some (some a)) : CoordInv a := by
  tma_state d
  cases s <;> simp only [succ] at ha
  case coord0 k =>
    obtain ⟨z, rfl⟩ := rdAny_bits (hrd ⟨k, .inl rfl⟩) ha
    simp only [CoordInv, Bits32] at hI ⊢
    exact ⟨hI, z, rfl⟩
  case coord1 k =>
    obtain ⟨z, rfl⟩ := rdAny_bits (hrd ⟨k, .inr (.inl rfl)⟩) ha
    simp only [CoordInv, Bits32] at hI ⊢
    exact ⟨hI.1, hI.2, z, rfl⟩
  case coord2 k =>
    obtain ⟨z, rfl⟩ := rdAny_bits (hrd ⟨k, .inr (.inr (.inl rfl))⟩) ha
    simp only [CoordInv, Bits32] at hI ⊢
    exact ⟨hI.1, hI.2.1, hI.2.2, z, rfl⟩
  case coord3 k =>
    obtain ⟨z, rfl⟩ := rdAny_bits (hrd ⟨k, .inr (.inr (.inr rfl))⟩) ha
    simp only [CoordInv] at hI
    obtain ⟨hq, h0, h1, h2⟩ := hI
    have hnew : QuadBits { ac with w3 := .bits 32 z } := ⟨h0, h1, h2, z, rfl⟩
    by_cases hk : k.val = 0
    · simp only [CoordInv, afterQuad, afterCoord, hk, ↓reduceIte]
      exact fun _ => hnew
    · simp only [CoordInv, afterQuad, afterCoord, hk, ↓reduceIte]
      exact ⟨hq (by omega), hnew⟩
  case gather k =>
    simp only [CoordInv] at hI
    obtain rfl := (Option.some.inj (Option.some.inj ha)).symm
    simp only [CoordInv, afterGather]
    split_ifs
    · trivial
    · exact hI
    · exact fun _ => hI.2
  case elect =>
    apply coordInv_of_free
    rcases electNext_succ ha with rfl | ⟨s, rfl⟩
    · unfold leadNext afterTopk lensD
      split <;> (try split) <;> (try split) <;> exact trivial
    · exact trivial
  case loadTopk =>
    apply coordInv_of_free
    obtain ⟨x, rfl⟩ := ncWord_succ ha
    unfold afterTopk lensD
    split <;> exact trivial
  case loadExtra =>
    apply coordInv_of_free
    obtain ⟨x, rfl⟩ := ncWord_succ ha
    simp [Free, lensD]
  case qWait =>
    apply coordInv_of_free
    rcases poll_succ ha with rfl | rfl <;> simp [Free]
  case storeWait =>
    apply coordInv_of_free
    rcases poll_succ ha with rfl | rfl
    · simp [Free]
    · unfold loopEntry
      split <;> exact trivial
  case coordWait =>
    apply coordInv_of_free
    rcases poll_succ ha with rfl | rfl <;> simp [Free]
  case rawWait =>
    apply coordInv_of_free
    rcases poll_succ ha with rfl | rfl <;> simp [Free]
  case rawArrive =>
    apply coordInv_of_free
    obtain rfl := (Option.some.inj (Option.some.inj ha)).symm
    simp [Free]
  case coordFree =>
    apply coordInv_of_free
    obtain rfl := (Option.some.inj (Option.some.inj ha)).symm
    unfold loopEnd
    split <;> exact trivial
  case outBar =>
    apply coordInv_of_free
    obtain rfl := (Option.some.inj (Option.some.inj ha)).symm
    simp [Free]
  case exit => cases ha
  case leave => cases ha

/-- The elected lane's first state satisfies the invariant. -/
theorem coordInv_lead (d : D) : CoordInv (leadNext P L g d) := by
  apply coordInv_of_free
  unfold leadNext afterTopk lensD
  split <;> (try split) <;> (try split) <;> exact trivial

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The obligation of one site: the event is no fault. -/
abbrev NoUbAt (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  (code P L g).ShapeAt (fun _ e => ∀ f, e.kind ≠ .ub f) d

theorem noUb_elect (d : D) (hs : d.site = .elect) : NoUbAt P L g d := by
  tma_state d
  cases hs
  tma_open
  obtain ⟨inst, ld, -, hk⟩ := fires_elect_full (readBits_reg (rg 663)) (by decide) hf
  rw [hk]
  intro f h
  cases h

theorem noUb_lens (hp : Pre P L m) (d : D) (hok : SiteOk P L g d)
    (hs : d.site = .loadTopk ∨ d.site = .loadExtra) : NoUbAt P L g d := by
  intro t ins e o hat _ hc hf
  rcases hs with hs | hs
  · obtain ⟨x, hx⟩ := len_ptr (hok.1 hs)
    obtain ⟨bs, hk, -⟩ := topk_read hp hx hs hat hc hf
    rw [hk]
    intro f h
    cases h
  · obtain ⟨x, hx⟩ := len_ptr (hok.2.1 hs)
    obtain ⟨bs, hk, -⟩ := extra_read hp hx hs hat hc hf
    rw [hk]
    intro f h
    cases h

theorem noUb_qWait (hp : Pre P L m) (d : D) (hs : d.site = .qWait) : NoUbAt P L g d := by
  tma_state d
  cases hs
  tma_open
  exact poll_nonub (by rw [hpc]; decide) (rg 669) (rg 670)
    (al8 (m8_addi (m8_sbw hp) (by decide))) hf

theorem noUb_storeWait (hp : Pre P L m) (d : D) (hs : d.site = .storeWait) :
    NoUbAt P L g d := by
  tma_state d
  cases hs
  tma_open
  exact poll_nonub (by rw [hpc]; decide) (rg 672) (rg 670)
    (al8 (m8_addi (m8_sbw hp) (by decide))) hf

theorem noUb_coordWait (hp : Pre P L m) (d : D) (hs : d.site = .coordWait) :
    NoUbAt P L g d := by
  tma_state d
  cases hs
  tma_open
  exact poll_nonub (by rw [hpc]; decide) (rg 685) (rg 686)
    (al8 (m8_addi (m8_ringB hp _) (by decide))) hf

theorem noUb_rawWait (hp : Pre P L m) (d : D) (hs : d.site = .rawWait) : NoUbAt P L g d := by
  tma_state d
  cases hs
  tma_open
  exact poll_nonub (by rw [hpc]; decide) (rg 688) (rg 689)
    (al8 (m8_addi (m8_tileB hp _) (by decide))) hf

/-- **The coordinate quadruples' base plus a multiple of 16 is 16-byte aligned**, whatever the
ring slot. -/
theorem crd_al16 (hp : Pre P L m) (d : D) {off : Int} (h16 : off % 16 = 0) :
    (truncBits 32 (truncBits 32 (crdB L d) + BitVec.ofInt 64 off)).toNat % 16 = 0 := by
  have h2 := hp.sharedAlignment
  have h3 := hp.sharedBase
  have h4 := hp.sharedRange
  unfold sharedBytes at h4
  simp only [crdB, ringB, mad32, add32, shl, r32, i32, sbw, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, BitVec.toNat_shiftLeft]
  norm_num [Nat.shiftLeft_eq]
  omega

theorem noUb_coord (hp : Pre P L m) (d : D)
    (hs : ∃ k, d.site = .coord0 k ∨ d.site = .coord1 k ∨ d.site = .coord2 k ∨
      d.site = .coord3 k) : NoUbAt P L g d := by
  tma_state d
  obtain ⟨k, hs | hs | hs | hs⟩ := hs <;> cases hs <;> fin_cases k <;> tma_openS <;>
    change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
  all_goals
    refine fires_rd_nonub (rg 782) ?_ ?_ hf
    · decide
    · exact crd_al16 hp _ (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **A gather4 load is no fault** from the facts of its operands. -/
theorem gather_nonub_of (hp : Pre P L m) (hg : g < L.threads) {t : TState} {dst r1 r2 r3 r4 : Nat}
    {x : Nat} {y bw pw : BitVec 64} {c : Nat} {pc : Nat} {e : Event}
    {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensor false false dst 0 (.reg 3049)
        [.reg 691, .reg r1, .reg r2, .reg r3, .reg r4] 696 0 none .fourRows
        (some (.reg 3050)))) e o)
    (hm : t.regs 3049 = some (.bits 64 (BitVec.ofNat 64 (P.param1Base + x))))
    (hx : x = 768 ∨ (x = 896 ∧ P.extra_topk ≠ 0))
    (h691 : t.regs 691 = some (.bits 32 0))
    (hrows : ∀ r, r ∈ [r1, r2, r3, r4] → ∃ z, t.regs r = some (.bits 32 z))
    (hdr : t.regs dst = some (.bits 32 y)) (hy : (truncBits 32 y).toNat = L.sharedBase + c)
    (hc : c % 128 = 0) (hb : t.regs 696 = some (.bits 32 bw))
    (hb8 : (truncBits 32 (truncBits 32 bw + BitVec.ofInt 64 0)).toNat % 8 = 0)
    (hpol : t.regs 3050 = some (.bits 64 pw)) : ∀ f, e.kind ≠ .ub f := by
  have h64 : (BitVec.ofNat 64 (P.param1Base + x)).toNat = P.param1Base + x := by
    have := hp.param1Range
    simp only [BitVec.toNat_ofNat]
    omega
  have hxr : x = 768 ∨ x = 896 := by omega
  have hal : (P.param1Base + x) % 64 = 0 := by
    have := hp.param1Align
    omega
  obtain ⟨d0, hbind, hval, hbox⟩ : ∃ d0 : TensorDescriptor.Descriptor 1,
      L.tensorMaps (P.param1Base + x) = some ⟨1, d0⟩ ∧ TensorDescriptor.Valid d0 ∧
        d0.box.size 1 = 1 := by
    rcases hx with rfl | ⟨rfl, hne⟩
    · exact ⟨_, hp.mapKVBind, Geometry.mapKv_valid_of_pre hp, by
        simp [mapKv, encodeKv]⟩
    · rcases hp.mapExtraKvBind with h0 | hb'
      · exact absurd h0 hne
      · exact ⟨_, hb', Geometry.mapExtraKv_valid_of_pre hp hne, by
          simp [mapExtraKv, encodeKv]⟩
  obtain ⟨z1, h1⟩ := hrows r1 (by simp)
  obtain ⟨z2, h2⟩ := hrows r2 (by simp)
  obtain ⟨z3, h3⟩ := hrows r3 (by simp)
  obtain ⟨z4, h4⟩ := hrows r4 (by simp)
  have hmap : tensorMap L g t (.reg 3049)
      [.reg 691, .reg r1, .reg r2, .reg r3, .reg r4] .fourRows =
      .ok (P.param1Base + x, ⟨1, d0⟩) := by
    unfold tensorMap
    simp only [bind, Except.bind, pure, Except.pure, tensorMapAddress_bits hm, h64, hal,
      hbind, hval, hbox]
    simp [TensorMode.coordinates]
  have hvs : [Opnd.reg 691, .reg r1, .reg r2, .reg r3, .reg r4].mapM (readBits L g t 32) =
      .ok [truncBits 32 0, truncBits 32 z1, truncBits 32 z2, truncBits 32 z3,
        truncBits 32 z4] := by
    simp only [List.mapM_cons, List.mapM_nil, readBits32_reg h691, readBits32_reg h1,
      readBits32_reg h2, readBits32_reg h3, readBits32_reg h4, bind, Except.bind, pure,
      Except.pure]
  have hba : TensorDescriptor.BoxAligned (TensorMode.fourRows.transfer d0)
      (fun axis : Fin 2 => (BitVec.ofNat 32 ([truncBits 32 0, truncBits 32 z1, truncBits 32 z2,
        truncBits 32 z3, truncBits 32 z4].getD axis.val 0).toNat).toInt) := by
    simp [TensorDescriptor.BoxAligned, truncBits]
  have h128 : (truncBits 32 y).toNat % 128 = 0 := by
    have := hp.sharedAlignment
    have := hp.sharedBase
    omega
  have hcp := tensorLoadCopy_of (ca := false) (gt := false) (dst := dst) (off := 0) (mb := 696)
    (moff := 0) hmap (dst_loc hdr) h128
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact mbarLoc_bits hb hb8) hvs hba
  exact tensor_nonub (pol_ok hpol) hcp (route_self hp (cta_lt hp hg)) hf

/-- **The coordinate registers of a gather's quadruple hold 32-bit words.** -/
theorem crd_bits (d : D) (k : Fin 16) (hs : d.site = .gather k) (hI : CoordInv d) {r : Nat}
    (hr : r ∈ ldRegs k.val) : ∃ z, valueOf P L g d r = .bits 32 z := by
  have hq : QuadBits d.cp ∧ QuadBits d.cq := by simpa only [CoordInv, hs] using hI
  obtain ⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, ⟨a2, ha2⟩, ⟨a3, ha3⟩⟩ := hq.1
  obtain ⟨⟨b0, hb0⟩, ⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨b3, hb3⟩⟩ := hq.2
  tma_state d
  simp only at hs
  subst hs
  dsimp only at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  fin_cases k <;> simp only [ldRegs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;>
    simp [valueOf, values, dstVals, valuesLoop, valuesPre, valuesLaunch, crdWord, crdSlot,
      crdSrc, Quad.list, List.lookup, ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]

set_option linter.unusedSimpArgs false in
/-- **A gather is no fault** in a loop state whose coordinate words are 32-bit words, whose block
is a main one or has the extra cache on. -/
theorem noUb_gather (hp : Pre P L m) (hg : g < L.threads) (d : D) (hs : ∃ k, d.site = .gather k)
    (hI : CoordInv d) {b : Nat} (hb : b < 2) (hbuf : d.buf = W b)
    (hmain : isMain d = true ∨ P.extra_topk ≠ 0) : NoUbAt P L g d := by
  obtain ⟨k, hs⟩ := hs
  have hq := fun {r : Nat} (hr : r ∈ ldRegs k.val) => crd_bits (P := P) (L := L) (g := g) d k hs
    hI hr
  have hx : (sel (isMain d) 768 896).toNat = 768 ∨
      ((sel (isMain d) 768 896).toNat = 896 ∧ P.extra_topk ≠ 0) := by
    cases hm : isMain d
    · rw [hm] at hmain
      exact .inr ⟨by simp [sel], hmain.resolve_left (by decide)⟩
    · exact .inl (by simp [sel])
  have hR : ∀ {n : Nat}, n ≤ 165632 →
      (truncBits 32 (addi (rawB L d) (n : Int))).toNat = L.sharedBase + (36864 * b + n) :=
    fun hn => rawDst hp hb hbuf hn
  tma_state d
  simp only at hs
  subst hs
  fin_cases k <;> tma_open <;>
  · have hreg := regs_of_factsFrom hF (r := 3049) (by decide)
    simp only [valueOf, values, dstVals, valuesLoop, valuesPre,
      List.lookup, List.cons_append, List.nil_append, Option.getD_some] at hreg
    refine gather_nonub_of hp hg hf hreg hx (regs_of_factsFrom hF (by decide)) ?_
      (regs_of_factsFrom hF (by decide)) (hR (by decide)) ?_ (regs_of_factsFrom hF (by decide))
      ?_ (regs_of_factsFrom hF (by decide))
    · intro r hr
      obtain ⟨z, hz⟩ := hq (r := r) (by simpa [ldRegs] using hr)
      refine ⟨z, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        rw [regs_of_factsFrom hF (by decide), hz]
    · interval_cases b <;> decide
    · exact al8 (m8_addi (m8_tileB hp _) (by decide))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
