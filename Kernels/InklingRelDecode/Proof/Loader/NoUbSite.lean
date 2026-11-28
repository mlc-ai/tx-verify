-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.NoUbStep
public import Kernels.InklingRelDecode.Proof.Loader.Ref
import Kernels.InklingRelDecode.Proof.Loader.Steps
import Kernels.InklingRelDecode.Proof.Loader.StepsRead
public import Kernels.InklingRelDecode.Proof.Loader.Shape
import Kernels.InklingRelDecode.Proof.Loader.PageAddr
import Kernels.InklingRelDecode.Proof.Loader.TileRing
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.CopyOk
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.NoUbSites
import Lemmas.Flow.UbStop
import Lemmas.Flow.UbFree
import Lemmas.Flow.LoadAl
import Lemmas.Flow.SharedSymOk
import Lemmas.Flow.TmplOkSync
import Lemmas.Flow.TcTmpl
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Flow.TensorStoreOrigin
import Lemmas.Flow.Events
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.Step.LoadVec
import Lemmas.Flow.Next
import Lemmas.Flow.ReadLive

@[expose] public section

/-! # The sites of the loader are not undefined behaviour: strict steps, templates, no death. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {w : Value}
  {rest : Nat → Value} {t : TState}

/-- **Every site of the loader steps strictly** along the reference. -/
theorem stepFor_site {lo hi : Nat} {d : D} (hr : Ref lo hi d) (e : Event)
    (typed : (∃ u, d.site = .page u) → ∀ x bs, e.kind = .rd x bs → ∀ v, rebuild 3 bs = .ok v →
      ∃ p, v = .bits 32 p) :
    (code L g w (inputs Q L g rest)).StepFor d e := by
  obtain ⟨s, i, n, a, b⟩ := d
  cases s with
  | dec => exact (dec_step i n a b).stepFor e
  | first => exact (first_step i n a b).stepFor e
  | second => exact (second_step i n a b).stepFor e
  | beginBar =>
    obtain ⟨rfl, rfl⟩ := hr
    exact beginBar_for _ _ a b e
  | poll => exact (poll_step i n a b).stepFor e
  | readyBar => exact (readyBar_step i n a b).stepFor e
  | arrive => exact (arrive_step i n a b).stepFor e
  | page u => exact page_for u i n a b e (typed ⟨u, rfl⟩)
  | warpBar p => exact (warpBar_step i n a b p).stepFor e
  | elect p =>
    by_cases h : p.val < 3
    · exact (elect_pair_step i n a b p h).stepFor e
    · obtain rfl : p = 3 := Fin.ext (by omega)
      obtain ⟨j, -, -, rfl, rfl⟩ := ref_loop hr rfl
      exact elect_for _ _ a b e
  | copy p u =>
    cases u with
    | false => exact (copy_first_step i n a b p).stepFor e
    | true =>
      by_cases h : p.val < 3
      · exact (copy_second_step i n a b p h).stepFor e
      · obtain rfl : p = 3 := Fin.ext (by omega)
        obtain ⟨j, -, -, rfl, rfl⟩ := ref_loop hr rfl
        exact copy_for _ _ a b e
  | endBar => exact (endBar_step i n a b).stepFor e
  | inc => exact (inc_step i n a b).stepFor e
  | dispatch => exact fun _ _ _ _ _ => .inl (.inl rfl)

theorem b32_trunc (x : BitVec 64) :
    Value.bits 32 (truncBits 32 x) = b32 (truncBits 32 x).toNat := by
  unfold b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat]
  omega

theorem trunc_lt (x : BitVec 64) : (truncBits 32 x).toNat < 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]; omega

theorem col_al0 {c0 : BitVec 64} (h : c0.toNat % 8 = 0) (c : BitVec 64) :
    (mul32 c0 c).toNat % 8 = 0 := by
  simp only [mul32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_mul]
  have hF : c0.toNat % 2 ^ 32 % 2 ^ 64 % 8 = 0 := by omega
  have hP : c0.toNat % 2 ^ 32 % 2 ^ 64 * (c.toNat % 2 ^ 32 % 2 ^ 64) % 8 = 0 := by
    rw [Nat.mul_mod, hF]; simp
  generalize c0.toNat % 2 ^ 32 % 2 ^ 64 * (c.toNat % 2 ^ 32 % 2 ^ 64) = P at *
  omega

theorem col_al8 {c0 : BitVec 64} (h : c0.toNat % 8 = 0) (c : BitVec 64) (k : Nat)
    (hk : k % 8 = 0) : (addi (mul32 c0 c) k).toNat % 8 = 0 := by
  simp only [addi, mul32, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_ofInt]
  have hF : c0.toNat % 2 ^ 32 % 2 ^ 64 % 8 = 0 := by omega
  have hP : c0.toNat % 2 ^ 32 % 2 ^ 64 * (c.toNat % 2 ^ 32 % 2 ^ 64) % 8 = 0 := by
    rw [Nat.mul_mod, hF]; simp
  generalize c0.toNat % 2 ^ 32 % 2 ^ 64 * (c.toNat % 2 ^ 32 % 2 ^ 64) = P at *
  omega


/-- The tile of the ring at a counter. -/
def tileOf (L : Launch) (i : BitVec 64) :=
  add32 (r32 (BitVec.ofNat 64 L.sharedBase)) (mad32 (quotient i) (i32 (-98304)) (shl i 15))


/-- **A loader copy is not undefined behaviour**: its destination is the tile at offset `off` of
the slot of a counter below `2 ^ 31`, its column a multiple of 8. -/
theorem copy_ok_at (hp : Pre Q L m) (hg : g < L.threads) {i : Value}
    (small : (bits i).toNat < 2 ^ 31) {dr cr rr off : Nat} {D C R : BitVec 64}
    (hoff : off ≤ 122880 ∧ off % 128 = 0)
    (hD : D.toNat = L.sharedBase + 32768 * ((bits i).toNat % 3) + off)
    (hmap : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0))
    (hd : t.regs dr = some (.bits 32 D))
    (hc : t.regs cr = some (.bits 32 C)) (hCl : C.toNat < 2 ^ 32) (hC8 : C.toNat % 8 = 0)
    (hr : t.regs rr = some (.bits 32 R)) (hRl : R.toNat < 2 ^ 32)
    (hb : t.regs 580 = some (.bits 32 (readyWord L i))) (f : Fault) :
    eventTmpl Assumptions.all L g t (.cpTensor false false dr 0 (.reg 1949) [.reg cr, .reg rr] 580
      0 none .tile none) ≠ .ub f := by
  have hcta : g / L.block < L.grid := by
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  have hsa := hp.sharedAlignment
  have hsr := hp.sharedRange
  have loc := ready_location (g := g) hp small hb
  have hbv (x : BitVec 64) : Value.bits 32 x = b32 x.toNat := by unfold b32; congr 1; simp
  rw [hbv] at hd hc hr
  exact Lib.cp_ok hp hcta hmap hd hc hr (by change L.sharedBase + 213340 ≤ 2 ^ 18 at hsr; omega)
    hCl hRl (by omega) hC8 (by rw [loc]; rfl) f

theorem addi_zero (v : BitVec 64) : addi (r32 v) ((0 : Nat) : Int) = r32 v := by
  rw [Nat.cast_zero, show v = BitVec.ofNat 64 v.toNat by simp]
  nf_simp [addi, add32, r32, i32]
  omega

/-- The column of a loader copy's box: the head's column of the key-value row. -/
def colBase (Q : Params) (L : Launch) (g : Nat) (rest : Nat → Value) : BitVec 64 :=
  mul32 (bits (inputs Q L g rest 531)) (r32 (BitVec.ofNat 64 ((L.ctaidOf (g / L.block)).get .y)))

/-- The registers of the eight copies: the destination, the column and the row. -/
theorem copy_pack (p : Fin 4) (half : Bool) :
    ∃ dr cr rr off k : Nat, ∃ guard, kernel.code[(Site.copy p half).pc]? = some ⟨guard,
        .cpTensor false false dr 0 (.reg 1949) [.reg cr, .reg rr] 580 0 none .tile none⟩ ∧
      off ≤ 122880 ∧ off % 128 = 0 ∧ k % 8 = 0 ∧
      (∀ i n a b, valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ dr =
        .bits 32 (addi (tileOf L (bits i)) off)) ∧
      (∀ i n a b, valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ cr =
        .bits 32 (addi (colBase Q L g rest) k)) ∧
      (∀ i n a b, ∃ R, valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ rr =
        .bits 32 (truncBits 32 R)) ∧
      dr ∈ Flow.live (Site.copy p half).pc ∧ cr ∈ Flow.live (Site.copy p half).pc ∧
      rr ∈ Flow.live (Site.copy p half).pc := by
  have z (i : BitVec 64) : Value.bits 32 (tileOf L i) = .bits 32 (addi (tileOf L i) 0) :=
    congrArg _ (addi_zero _).symm
  have zc : Value.bits 32 (colBase Q L g rest) = .bits 32 (addi (colBase Q L g rest) 0) :=
    congrArg _ (addi_zero _).symm
  fin_cases p <;> cases half
  · exact ⟨582, 583, 584, 0, 0, _, Flow.code_2389, by decide, by decide, by decide,
      fun i _ _ _ => z _, fun _ _ _ _ => zc, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨585, 586, 584, 16384, 64, _, Flow.code_2391, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨587, 588, 584, 98304, 128, _, Flow.code_2394, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨589, 590, 584, 114688, 192, _, Flow.code_2396, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨592, 583, 593, 8192, 0, _, Flow.code_2404, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => zc, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨594, 586, 593, 24576, 64, _, Flow.code_2406, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨595, 588, 593, 106496, 128, _, Flow.code_2410, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · exact ⟨596, 590, 593, 122880, 192, _, Flow.code_2412, by decide, by decide, by decide,
      fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => ⟨_, rfl⟩, by decide +kernel,
      by decide +kernel, by decide +kernel⟩

/-- The eight copies of a loader packet. -/
theorem copy_safe (hp : Pre Q L m) (hg : g < L.threads) {p : Fin 4} {half : Bool}
    {i n a b : Value} (small : (bits i).toNat < 2 ^ 31)
    (hmap : inputs Q L g rest 1949 = .ptr 64 true (.param (param "1")) 0)
    (hat : (code L g w (inputs Q L g rest)).AtD ⟨.copy p half, i, n, a, b⟩ t) {ins : Instr}
    (hc : kernel.code[(Site.copy p half).pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  obtain ⟨-, -, -, -, hF⟩ := hat
  have reg (r : Nat) (hr : r ∈ Flow.live (Site.copy p half).pc) :
      t.regs r = some (valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ r) :=
    holds_mem hF (mem_factsFrom hr)
  have ptr := reg 1949 (by fin_cases p <;> cases half <;> decide +kernel)
  rw [show valueOf L g w (inputs Q L g rest) ⟨.copy p half, i, n, a, b⟩ 1949 =
    inputs Q L g rest 1949 from rfl, hmap] at ptr
  have hb : t.regs 580 = some (.bits 32 (readyWord L i)) :=
    reg 580 (by fin_cases p <;> cases half <;> decide +kernel)
  have hH : (bits (inputs Q L g rest 531)).toNat % 8 = 0 := by
    have := hp.scalarsRange
    have := hp.headColsAlign
    rw [show inputs Q L g rest 531 = b32 (Q.headCols % 2 ^ 32) from rfl, bits_b32 (by omega),
      BitVec.toNat_ofNat]
    omega
  obtain ⟨dr, cr, rr, off, k, guard, hcode, ho1, ho2, hk, hvd, hvc, hvr, ld, lc, lr⟩ :=
    copy_pack (Q := Q) (L := L) (g := g) (w := w) (rest := rest) p half
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨R, hR⟩ := hvr i n a b
  have h : (addi (tileOf L (bits i)) off).toNat =
      L.sharedBase + 32768 * ((bits i).toNat % 3) + off :=
    tile_slot L (bits i) off ho1 hp.sharedRange small
  exact copy_ok_at hp hg small (D := addi (tileOf L (bits i)) off) ⟨ho1, ho2⟩ h ptr
    ((hvd i n a b) ▸ reg dr ld) ((hvc i n a b) ▸ reg cr lc) (trunc_lt _)
    (col_al8 hH _ k hk) (hR ▸ reg rr lr) (trunc_lt _) hb f

/-- **The template of a site of the loader is not undefined behaviour**, at a state that holds
its facts and whose counter and limit follow the reference. -/
theorem safe_site (hp : Pre Q L m) (hg : g < L.threads)
    (hmap : inputs Q L g rest 1949 = .ptr 64 true (.param (param "1")) 0) {lo hi : Nat}
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hhi : hi < 2 ^ 31) {d : D} {ins : Instr}
    (hr : Ref lo hi d) (hat : (code L g w (inputs Q L g rest)).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  obtain ⟨s, i, n, a, b⟩ := d
  cases s
  case dec =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2344)
    exact plainOk_tmpl hb (by decide) f
  case first | second =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2345)
    have := hp.sharedAlignment
    have := hp.sharedRange
    refine ldSharedSym_ok (o := 0) rfl rfl rfl rfl rfl rfl (by decide) rfl (by decide) ?_ f
    simp only [wrapAddr, truncBits, DType.width]
    simp
    omega
  case beginBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2346)
    exact barSync_imm_ok (by decide) f
  case poll =>
    have hc' : kernel.code[2374]? = some ins := hc
    have small := ref_counter_lt hr (by rfl) hhi
    refine not_ub_of_fires (pc := 2374) (fun f' hf => ?_) f
    obtain ⟨_, h⟩ := poll_slot (e := ⟨2374, .ub f'⟩) hp small hat hc' hf
    cases h
  case readyBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2377)
    exact warpBar_ok f
  case arrive =>
    have hc' : kernel.code[2378]? = some ins := hc
    have small := ref_counter_lt hr (by rfl) hhi
    refine not_ub_of_fires (pc := 2378) (fun f' hf => ?_) f
    have := arrive_slot (e := ⟨2378, .ub f'⟩) hp small hat hc' hf
    cases this
  case page u =>
    cases u
    · exact page_safe hp hg hat hc hh hr (Or.inl rfl) f
    · exact page_safe hp hg hat hc hh hr (Or.inr rfl) f
  case warpBar p =>
    fin_cases p
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2387)
      exact warpBar_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2392)
      exact warpBar_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2401)
      exact warpBar_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2407)
      exact warpBar_ok f
  case elect p =>
    fin_cases p
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2388)
      exact elect_imm_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2393)
      exact elect_imm_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2403)
      exact elect_imm_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2409)
      exact elect_imm_ok f
  case copy p u =>
    have small := ref_counter_lt hr (by rfl) hhi
    cases u
    · exact copy_safe hp hg small hmap hat hc f
    · exact copy_safe hp hg small hmap hat hc f
  case endBar =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2419)
    exact barSync_imm_ok (by decide) f
  case inc =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2420)
    exact plainOk_tmpl hb (by decide) f
  case dispatch =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2337)
    exact plainOk_tmpl hb (by decide) f


/-- **The loader dies only on the exit**: at a state of the reference, an event that is not
undefined behaviour has a successor (the words read are those of a 32-bit word, the poll waits,
the election elects). -/
theorem live_site (hp : Pre Q L m) (hg : g < L.threads) {lo hi : Nat}
    (hh : hi = Lib.blocksOf Q L (g / L.block)) (hhi : hi < 2 ^ 31) {d : D} {ins : Instr}
    {o : Option TState} {v : Event} (hr : Ref lo hi d)
    (hat : (code L g w (inputs Q L g rest)).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f)
    (rebuilds : (d.site = .first ∨ d.site = .second ∨ ∃ u, d.site = .page u) →
      ∀ ac bs, v.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x) :
    next L g d v ≠ none := by
  obtain ⟨s, i, n, a, b⟩ := d
  have rd (hq : ∃ ac bs, v.kind = .rd ac bs ∧ (rebuild 3 bs).toOption.isSome = true)
      (f : Value → D) : readResult v f ≠ none := by
    obtain ⟨ac, bs, hk, hs⟩ := hq
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    simp [readResult, hk, hx]
  cases s
  case first =>
    have hop := congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_2345))
    exact rd (read_live hop rfl rfl rfl hf hu (rebuilds (.inl rfl))) _
  case second =>
    have hop := congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_2345))
    exact rd (read_live hop rfl rfl rfl hf hu (rebuilds (.inr (.inl rfl)))) _
  case page u =>
    obtain ⟨ac, bs, hk⟩ := page_rd hp hg hat hc hh hr (by cases u <;> simp [Site.pc]) hf hu
    obtain ⟨x, hx⟩ := rebuilds (.inr (.inr ⟨u, rfl⟩)) ac bs hk
    cases u <;> exact rd ⟨ac, bs, hk, by rw [hx]; rfl⟩ _
  case poll =>
    have hc' : kernel.code[2374]? = some ins := hc
    have small := ref_counter_lt hr (by rfl) hhi
    obtain ⟨ok, h⟩ := poll_slot hp small hat hc' hf
    simp [next, h]
  case elect p =>
    have key (pc : Nat) (op : Op)
        (hel : ∀ {u}, Fires pc (eventTmpl Assumptions.all L g t op) v (some u) →
        ∃ mk inst ld, v.kind = .elect mk inst ld) (hop : op ≠ .ret ∧ op ≠ .exit)
        (hf' : Fires pc (eventTmpl Assumptions.all L g t op) v o) :
        ∃ mk inst ld, v.kind = .elect mk inst ld :=
      shape_cont (P := fun e => (∀ f, e.kind ≠ .ub f) → ∃ mk inst ld, e.kind = .elect mk inst ld)
        hf' hop (fun u hf => fun _ => hel hf) (fun f hu' => absurd rfl (hu' f)) hu
    have hel : ∀ {pc op},
        (∃ dst p ty mask, op = Op.warp ⟨.elect, ty, [dst, some p], [], some mask⟩) →
        ∀ {u}, Fires pc (eventTmpl Assumptions.all L g t op) v (some u) →
          ∃ mk inst ld, v.kind = .elect mk inst ld := by
      intro pc op hex u hf
      obtain ⟨dst, p, ty, mask, rfl⟩ := hex
      obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf
      exact ⟨mk, inst, ld, rfl⟩
    have shape : ∃ dst p ty mask, ins.op = Op.warp ⟨.elect, ty, [dst, some p], [], some mask⟩ := by
      fin_cases p
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2388); exact ⟨_, _, _, _, rfl⟩
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2393); exact ⟨_, _, _, _, rfl⟩
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2403); exact ⟨_, _, _, _, rfl⟩
      · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2409); exact ⟨_, _, _, _, rfl⟩
    obtain ⟨dst, q, ty, mask, hop⟩ := shape
    obtain ⟨mk, inst, ld, hk⟩ := key _ ins.op (hel ⟨dst, q, ty, mask, hop⟩)
      (by rw [hop]; exact ⟨nofun, nofun⟩) hf
    simp only [next, hk]
    split <;> simp [finishPair]
  case copy p u => cases u <;> simp [next]
  all_goals simp [next]

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
