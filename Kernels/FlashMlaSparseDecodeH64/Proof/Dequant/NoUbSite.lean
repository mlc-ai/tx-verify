-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Shape
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.MemLoc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeSetup
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.PollNoUb
import Lemmas.Flow.Step.RdNoUb
import Lemmas.Flow.StoreSrc
import Lemmas.Flow.UbStop
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part040
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part042
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part043
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part044
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part045
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part046
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part047
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part048
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part049
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part050
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part051
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part052
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part053
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part054
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part055
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # Warpgroup 2's states fire no undefined behaviour: the control sites

`noUbAt_<family>`: the event fired from a state of the control machine at the site is no fault:
the set-up and the barrier's events have no fault alternative in the shape table; the polls name
8-aligned barrier words (`ring_m8`, `ringQ_m8`); the length loads read through a set pointer
(`LenOk`); the scale and raw loads read at 16- and 8-aligned addresses of the lane's rows
(`scale_loc`, `rawRd_loc`). The stores need the payload register, which is a data register:
`Data/NoUb.lean`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control
open Data (chunkReg)

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The set-up's pointers are set at the length loads. -/
def LenOk (P : Params) (d : D) : Prop :=
  (d.site = .lenA → eqz64 (pw8 (P.topkLenBase.getD 0)) = false) ∧
    (d.site = .lenB → eqz64 (pw8 (P.extraTopkLenBase.getD 0)) = false)

/-- The obligation of one site: the event is no fault. -/
abbrev NoUbAt (P : Params) (L : Launch) (g : Nat) (w : BitVec 64) (d : D) : Prop :=
  (code P L g w).ShapeAt (fun _ e => ∀ f, e.kind ≠ .ub f) d

/-- The Q barrier's word is 8-byte aligned. -/
theorem ringQ_m8 (hp : Pre P L m) :
    (truncBits 32 (truncBits 32 (qW L) + BitVec.ofInt 64 0)).toNat % 8 = 0 := by
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have h3 := hp.sharedRange
  unfold sharedBytes at h3
  simp only [qW, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

theorem noUbAt_simple (hp : Pre P L m) (d : D)
    (hs : d.site = .smr ∨ d.site = .fpx ∨ d.site = .arrD ∨ d.site = .arrF ∨ d.site = .bar ∨
      d.site = .exit) : NoUbAt P L g w d := by
  intro t ins e o hat hi hc hf
  rcases hs with hs | hs | hs | hs | hs | hs
  · have h := shapeAt_smr (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    obtain ⟨inst, hk⟩ := h
    rw [hk]; intro f h; cases h
  · have h := shapeAt_fpx (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    rw [h]; intro f h; cases h
  · have h := shapeAt_arrD hp (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    rw [h]; intro f h; cases h
  · have h := shapeAt_arrF hp (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    rw [h]; intro f h; cases h
  · have h := shapeAt_bar hp (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    rw [h]; intro f h; cases h
  · have h := shapeAt_exit (g := g) (w := w) d hs hat hi hc hf
    simp only [EvK, hs] at h
    rw [h]; intro f h; cases h


theorem noUbAt_polls (hp : Pre P L m) (d : D)
    (hs : d.site = .wq ∨ d.site = .wraw ∨ d.site = .wsv) : NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  rcases hs with hs | hs | hs <;> cases hs <;> dq_open
  · exact poll_nonub (by rw [hpc]; decide) (rg 2434) (rg 2435) (ringQ_m8 hp) hf
  · exact poll_nonub (by rw [hpc]; decide) (rg 2458) (rg 2459) (ring_m8 hp sb (by decide)) hf
  · exact poll_nonub (by rw [hpc]; decide) (rg 2461) (rg 2462) (ring_m8 hp sb (by decide)) hf

theorem noUbAt_len (hp : Pre P L m) (d : D) (hl : LenOk P d)
    (hs : d.site = .lenA ∨ d.site = .lenB) : NoUbAt P L g w d := by
  intro t ins e o hat hi hc hf
  rcases hs with hs | hs
  · obtain ⟨x, hx⟩ := len_ptr (hl.1 hs)
    obtain ⟨bs, hk, -⟩ := topk_read hp hx hs hat hi hc hf
    rw [hk]; intro f h; cases h
  · obtain ⟨x, hx⟩ := len_ptr (hl.2 hs)
    obtain ⟨bs, hk, -⟩ := extra_read hp hx hs hat hi hc hf
    rw [hk]; intro f h; cases h


/-- A scale vector is 16-byte aligned. -/
theorem scale_al (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) :
    (smLoc L g (r2338W L g b) (scaleOff r)).addr % 16 = 0 := by
  have h := congrArg Loc.addr (scale_loc (L := L) hp g b r 0)
  simp only [Loc.at, wsLoc, Region.lo] at h
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have := (slotF b).isLt
  omega

/-- A raw word is 8-byte aligned. -/
theorem raw_al (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) (s : Fin 8) :
    (smLoc L g (rawRowW L g b) (rawOff r s)).addr % 8 = 0 := by
  have h := congrArg Loc.addr (rawRd_loc (L := L) hp g b r s)
  simp only [Loc.at, wsLoc, Region.lo] at h
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have := (slotF b).isLt
  omega

theorem scale_nonub (hp : Pre P L m) (b : Bool) {t : TState} {base pc : Nat} {ds : List Nat}
    {off : Int} {e : Event} {o : Option TState}
    (hr : t.regs base = some (.bits 32 (r2338W L g b))) (hoff : ∃ r : Fin 4, off = scaleOff r)
    (hlen : ds.length = 4)
    (hf : Fires pc (loadTmpl Assumptions.all L g t .shared false 32 ds base off) e o) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨r, rfl⟩ := hoff
  exact fires_rd_nonub hr (by decide) (by rw [hlen]; exact scale_al hp g b r) hf

theorem raw_nonub (hp : Pre P L m) (b : Bool) {t : TState} {base pc : Nat} {ds : List Nat}
    {off : Int} {e : Event} {o : Option TState}
    (hr : t.regs base = some (.bits 32 (rawRowW L g b))) (hoff : ∃ (r : Fin 4) (s : Fin 8),
      off = rawOff r s) (hlen : ds.length = 1)
    (hf : Fires pc (loadTmpl Assumptions.all L g t .shared false 64 ds base off) e o) :
    ∀ f, e.kind ≠ .ub f := by
  obtain ⟨r, s, rfl⟩ := hoff
  exact fires_rd_nonub hr (by decide) (by rw [hlen]; exact raw_al hp g b r s) hf

theorem noUbAt_scale (hp : Pre P L m) (d : D) (hs : ∃ r, d.site = .scale r) :
    NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨r, hs⟩ := hs
  cases hs
  fin_cases r <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact scale_nonub hp sb (regs_of_factsFrom hF (by decide +kernel)) (by decide +kernel) rfl hf

theorem noUbAt_raw0 (hp : Pre P L m) (d : D) (hs : ∃ i, d.site = .raw 0 i) :
    NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨i, hs⟩ := hs
  cases hs
  fin_cases i <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact raw_nonub hp sb (regs_of_factsFrom hF (by decide +kernel)) (by decide +kernel) rfl hf

theorem noUbAt_raw1 (hp : Pre P L m) (d : D) (hs : ∃ i, d.site = .raw 1 i) :
    NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨i, hs⟩ := hs
  cases hs
  fin_cases i <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact raw_nonub hp sb (regs_of_factsFrom hF (by decide +kernel)) (by decide +kernel) rfl hf

theorem noUbAt_raw2 (hp : Pre P L m) (d : D) (hs : ∃ i, d.site = .raw 2 i) :
    NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨i, hs⟩ := hs
  cases hs
  fin_cases i <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact raw_nonub hp sb (regs_of_factsFrom hF (by decide +kernel)) (by decide +kernel) rfl hf

theorem noUbAt_raw3 (hp : Pre P L m) (d : D) (hs : ∃ i, d.site = .raw 3 i) :
    NoUbAt P L g w d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨i, hs⟩ := hs
  cases hs
  fin_cases i <;> dq_open <;>
  · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact raw_nonub hp sb (regs_of_factsFrom hF (by decide +kernel)) (by decide +kernel) rfl hf

theorem noUbAt_raw (hp : Pre P L m) (d : D) (hs : ∃ r i, d.site = .raw r i) :
    NoUbAt P L g w d := by
  obtain ⟨r, i, hs⟩ := hs
  fin_cases r
  exacts [noUbAt_raw0 hp d ⟨i, hs⟩, noUbAt_raw1 hp d ⟨i, hs⟩, noUbAt_raw2 hp d ⟨i, hs⟩,
    noUbAt_raw3 hp d ⟨i, hs⟩]

/-- A 16-byte shared store of a 16-byte register to an aligned address is no fault. -/
theorem st128_nonub {t : TState} {base src pc : Nat} {x : BitVec 64} {v : Value} {e : Event}
    {o : Option TState} (hr : t.regs base = some (.bits 32 x)) (hs : t.sub = 0)
    (hal : (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 0)).toNat % 16 = 0)
    (hv : t.regs src = some v) (hb : v.bytes = 16)
    (hf : Fires pc (storeTmpl L g t .shared 128 base 0 [.reg src]) e o) :
    ∀ f, e.kind ≠ .ub f := by
  intro f he
  have h := fires_ub hf he
  simp only [storeTmpl, effAddr_shared32 hr, hs, elemAcc, bind, Except.bind] at h
  have hal' : (truncBits 32 (truncBits 32 x)).toNat % 16 = 0 := by simpa using hal
  simp [hal', readValue, readReg, hv, storeValue_of_bytes (w := 128) hb, pure, Except.pure] at h

/-- A chunk's address is 16-byte aligned. -/
theorem chunk_al (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) (s : Fin 8) :
    (smLoc L g (chunkW L g b r s) 0).addr % 16 = 0 := by
  have h := congrArg Loc.addr (store_loc (L := L) hp g b r s)
  simp only [wsLoc, Region.lo] at h
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  have h3 := MemRow.dqChunk_al (i := g % 128) (r := r.val) (s := s.val) (Nat.mod_lt _ (by decide))
  have := (slotF b).isLt
  omega

/-- The register a store site stores. -/
def chunkRegOf (d : D) : Nat :=
  match d.site with
  | .store r s => chunkReg r.val s.val
  | _ => 0

theorem store_nonub (hp : Pre P L m) (b : Bool) (r : Fin 4) (s : Fin 8) {t : TState}
    {base src pc : Nat} {v : Value} {e : Event} {o : Option TState}
    (hr : t.regs base = some (.bits 32 (chunkW L g b r s))) (hs : t.sub = 0)
    (hv : t.regs src = some v) (hb : v.bytes = 16)
    (hf : Fires pc (storeTmpl L g t .shared 128 base 0 [.reg src]) e o) :
    ∀ f, e.kind ≠ .ub f :=
  st128_nonub hr hs (chunk_al hp g b r s) hv hb hf

theorem noUbAt_store (hp : Pre P L m) (d : D) (hs : ∃ r i, d.site = .store r i) :
    ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
      (code P L g w).AtD d t → (code P L g w).inv d →
      kernel.code[(code P L g w).pc d]? = some ins →
      Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o →
      (∃ v, t.regs (chunkRegOf d) = some v ∧ v.bytes = 16) → ∀ f, e.kind ≠ .ub f := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  obtain ⟨r, i, hs⟩ := hs
  cases hs
  fin_cases r <;> fin_cases i <;> dq_open <;>
  (rintro ⟨v, hv, hb⟩
   have h0 : t.sub = 0 := hsub.trans (by change el < 1 at hi; omega)
   change Fires _ (storeTmpl L g t .shared _ _ 0 _) e o at hf
   try simp only [chunkRegOf] at hv)
  · exact store_nonub hp sb 0 0 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 1 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 2 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 3 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 4 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 5 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 6 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 0 7 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 0 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 1 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 2 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 3 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 4 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 5 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 6 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 1 7 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 0 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 1 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 2 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 3 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 4 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 5 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 6 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 2 7 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 0 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 1 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 2 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 3 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 4 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 5 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 6 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf
  · exact store_nonub hp sb 3 7 (regs_of_factsFrom hF (by decide +kernel)) h0 hv hb hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
