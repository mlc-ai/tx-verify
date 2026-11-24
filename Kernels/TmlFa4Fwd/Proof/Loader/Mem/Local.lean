-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
public import Kernels.TmlFa4Fwd.Proof.Lib.Start
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Lemmas.Kernel.Followed
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Lemmas.Kernel.Source.LocalSrc
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A packet's address load returns a multiple of 16

A pointer round stores a row's global address (`ptS`): the K or V head base (`%rd12`, `%rd13`)
plus twice the row stride times the row plus the page stride times the page. The bases are
multiples of 16 and the strides of 8 (`Pre.alignment`), so the address is a multiple of 16 for
every page and row word, modulo `2 ^ 64` (`pt_m16`). A packet's address load at sub-step 0 reads
the low word of such an address: its first byte is byte 0 of a pointer round's 8-byte store at the
loaded offset (no other store of the lane covers it, `wr_pt`), so the word it rebuilds is a
multiple of 16 (`lw_low`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-! ### 64-bit words that are multiples of 8 and 16 -/

theorem toNat_tb64 (x : BitVec 64) : (truncBits 64 x).toNat = x.toNat := by
  simp [truncBits, x.isLt]

theorem mul64_m8 {s : Nat} (hs : s % 8 = 0) (y : BitVec 64) :
    (mul64 (BitVec.ofNat 64 s) y).toNat % 8 = 0 := by
  simp only [mul64, r64, toNat_tb64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
  apply Nat.mod_eq_zero_of_dvd
  apply Dvd.dvd.mul_right
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
  exact hs

theorem mad64_m8 {s : Nat} (hs : s % 8 = 0) (y z : BitVec 64) (hz : z.toNat % 8 = 0) :
    (mad64 (BitVec.ofNat 64 s) y z).toNat % 8 = 0 := by
  have h1 : (BitVec.ofNat 64 s * y).toNat % 8 = 0 := by
    have := mul64_m8 hs y
    simpa only [mul64, r64, truncBits64, toNat_tb64] using this
  simp only [mad64, r64, truncBits64, toNat_tb64, BitVec.toNat_add] at h1 ⊢
  rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
  omega

theorem shl1_m16 {x : BitVec 64} (h : x.toNat % 8 = 0) : (shl64 x 1).toNat % 16 = 0 := by
  have h1 : (i32 1).toNat = 1 := by decide
  simp only [shl64, h1, show ¬ (1 ≥ 64) by decide, ↓reduceIte, r64, toNat_tb64,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  omega

theorem add64_m16 {x y : BitVec 64} (hx : x.toNat % 16 = 0) (hy : y.toNat % 16 = 0) :
    (add64 x y).toNat % 16 = 0 := by
  simp only [add64, r64, toNat_tb64, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  omega

/-- A K or V head base of the setup is a multiple of 16. -/
theorem rd12_m16 (hp : Pre p L m) (v : V) : (setup p L g v).rd12.toNat % 16 = 0 := by
  obtain ⟨hk, -, -, hh, -⟩ := hp.alignment
  simp only [setup]
  refine add64_m16 ?_ (shl1_m16 (mul64_m8 hh _))
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  exact hk

theorem rd13_m16 (hp : Pre p L m) (v : V) : (setup p L g v).rd13.toNat % 16 = 0 := by
  obtain ⟨-, hk, -, -, -, -, hh, -⟩ := hp.alignment
  simp only [setup]
  refine add64_m16 ?_ (shl1_m16 (mul64_m8 hh _))
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]
  exact hk

/-- The address a pointer round stores. -/
theorem rv_ptAd (p : Params) (L : Launch) (g w : Nat) (per : Per) (b : Bool) (it : Fin 2) (v : V)
    (kk : Fin 2) :
    ∃ base : BitVec 64, ∃ lay : CacheLayout,
      ((base = v.su.rd12 ∧ lay = p.kLayout) ∨ (base = v.su.rd13 ∧ lay = p.vLayout)) ∧
      rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).ad =
        add64 base (shl64 (mad64 (BitVec.ofNat 64 lay.rowStride) (sx32 v.lr)
          (mul64 (BitVec.ofNat 64 lay.pageStride) (sx32 v.lp))) 1) := by
  cases per <;> cases b <;>
    first
      | exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, rfl⟩
      | exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, rfl⟩

/-- **A pointer round's stored address is a multiple of 16** at a state with the page-table
facts. -/
theorem pt_m16 (hp : Pre p L m) {per : Per} {b : Bool} {it : Fin 2} {v : V} {kk : Fin 2}
    (hP : PgOk p L g ⟨.ptS per b it, v, kk⟩) :
    (rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).ad).toNat % 16 = 0 := by
  obtain ⟨⟨v₀, hsu, -, -⟩, -⟩ := hP
  obtain ⟨-, -, hk1, -, hk2, hv1, -, hv2, -⟩ := hp.alignment
  obtain ⟨base, lay, hbl, he⟩ := rv_ptAd p L g w per b it v kk
  rw [he]
  rcases hbl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine add64_m16 ?_ (shl1_m16 (mad64_m8 hk1 _ _ (mul64_m8 hk2 _)))
    simp only at hsu
    rw [hsu]; exact rd12_m16 hp v₀
  · refine add64_m16 ?_ (shl1_m16 (mad64_m8 hv1 _ _ (mul64_m8 hv2 _)))
    simp only at hsu
    rw [hsu]; exact rd13_m16 hp v₀

set_option maxHeartbeats 4000000 in
/-- **An 8-byte store of a loader state with its reference values** is a pointer round's: byte 0
of its bytes is byte 0 of an address that is a multiple of 16. -/
theorem wr8_ev (hp : Pre p L m) {d : D} {e : Event} {ns nv nc : Nat}
    (hF : LFits p L g d ns nv nc) (hev : Ev p L g w d e) {a : Acc} {bs : List Byte}
    (hk : e.kind = .wr a bs) (hsz : a.size = 8) :
    ∃ y : BitVec 64, y.toNat % 16 = 0 ∧ bs[0]? = some (.bits 64 y, 0) := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases s
  case ptS per b it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      have hv : v' = .bits 64 (rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).ad) := by
        simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
      subst hv
      have hb : Site.blk (.ptS per b it) = true := by cases per <;> rfl
      obtain ⟨-, -, -, -, hP⟩ := lfits_blk_of (d := ⟨.ptS per b it, v, kk⟩) hb hF
      exact ⟨_, pt_m16 hp hP, rfl⟩
    · cases hk
  case pgSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      simp [lacc] at hsz
    · cases hk
  case rwSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      simp [lacc] at hsz
    · cases hk
  all_goals
    simp only [Ev, Epilogue.Ev, Site.toE] at hev
    shape_destruct hev
    all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

/-- **The 8-byte writes of a followed loader lane before an event** are pointer rounds' stores
of multiples of 16. -/
theorem wr_pt (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L w) X (g, j)) {j : Nat} (hj : j < k)
    {dst : Acc} {bytes : List Byte} (hw : X.MemWrites (.thread (g, j)) dst bytes)
    (hsz : dst.size = 8) :
    ∃ y : BitVec 64, y.toNat % 16 = 0 ∧ bytes[0]? = some (.bits 64 y, 0) := by
  have hG : Good p L w X g j :=
    Frame.followedAt_of_noBad ref_init j fun i hi => hnb i (by omega)
  obtain ⟨f, hf, hk⟩ : ∃ f, X.get (g, j) = some f ∧
      (f.kind = .wr dst bytes ∨ ∃ old, f.kind = .rmw dst old (some bytes)) := by
    rcases hw with ⟨pc, h⟩ | ⟨old, pc, h⟩
    · exact ⟨_, h, .inl rfl⟩
    · exact ⟨_, h, .inr ⟨old, rfl⟩⟩
  have hub : ∀ pc f', f ≠ ⟨pc, .ub f'⟩ := by
    rintro pc f' rfl
    rcases hk with h | ⟨_, h⟩ <;> cases h
  rcases good_cases hp hX hf hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨b, d, n, hσ, hb, -, -, hF⟩
  · exact (start_no_wr (start_fired hp hX hf hσ).1 hS hk).elim
  · have hev := (lfired hp hX hf hσ).1
    rw [hb] at hev
    rcases hk with h | ⟨old, h⟩
    · exact wr8_ev hp hF hev h hsz
    · exact absurd h ((wr_ev hp hev).2 _ _ _)

/-- Four bytes of integers whose first is byte 0 of a 64-bit word `y` rebuild to a word with the
low bits of `y`. -/
theorem rebuild_low {b0 : Option Byte} {rest : List (Option Byte)} {y x : BitVec 64}
    (h0 : b0 = some (.bits 64 y, 0)) (hl : (b0 :: rest).length = 4)
    (hall : ∀ b ∈ b0 :: rest, ∃ z, b = some z ∧ SByte z)
    (h : rebuild 3 (b0 :: rest) = .ok (.bits 32 x)) : x.toNat % 16 = y.toNat % 16 := by
  subst h0
  have hnone : none ∉ (some ((Value.bits 64 y), 0) :: rest) := by
    intro hm; obtain ⟨z, hz, -⟩ := hall none hm; cases hz
  have hint : (some ((Value.bits 64 y), 0) :: rest).all intByte = true := by
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨z, rfl, wd, x', i, rfl, -, -⟩ := hall b hb
    rfl
  have hrl : rest.length = 3 := by simpa using hl
  obtain ⟨n, hn⟩ : ∃ n, littleEndianBits rest = some n := by
    have hall' : ∀ b ∈ rest, ∃ z, b = some z ∧ SByte z := fun b hb =>
      hall b (List.mem_cons_of_mem _ hb)
    clear hall hnone hint hrl hl h
    induction rest with
    | nil => exact ⟨0, rfl⟩
    | cons b bs ih =>
      obtain ⟨z, rfl, wd, x', i, rfl, hwd, hi⟩ := hall' b (List.mem_cons_self ..)
      obtain ⟨n, hn⟩ := ih fun b hb => hall' b (List.mem_cons_of_mem _ hb)
      have hb : (Value.bits wd x').bytes = wd / 8 := by
        rcases hwd with rfl | rfl <;> rfl
      simp [littleEndianBits, byteBits, hn, hb, hi, Value.bitPattern]
  have hle : littleEndianBits (some ((Value.bits 64 y), 0) :: rest) =
      some (y.toNat % 256 + 256 * n) := by
    simp [littleEndianBits, byteBits, hn, Value.bitPattern, Value.bytes]
  have hh : rebuild.halves 2 (some ((Value.bits 64 y), 0) :: rest) =
      .ok (.bits 32 (BitVec.ofNat 64 (y.toNat % 256 + 256 * n))) := by
    unfold rebuild.halves
    simp only [hnone, ↓reduceIte, hint, true_or, rebuildBits, hle, hl]
    rfl
  have hr : rebuild 3 (some ((Value.bits 64 y), 0) :: rest) =
      .ok (.bits 32 (BitVec.ofNat 64 (y.toNat % 256 + 256 * n))) := by
    unfold rebuild
    simp only [Value.bytes, hl, show ¬ (64 / 8 = 4) by decide, false_and, ↓reduceIte]
    exact hh
  rw [hr] at h
  simp only [Except.ok.injEq, Value.bits.injEq, true_and] at h
  subst h
  simp only [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 2000000 in
/-- **A packet's address load at sub-step 0 returns a multiple of 16**: the low word of a row
address that a pointer round of the lane stored. -/
theorem lw_low (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hJ : Loader.Ref p L g (wOf b) (d, lcn n))
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L (wOf b)) X (g, j))
    {per : Per} {v : Bool} {h : Fin 2} (hs : d.site = .lw per v h) (hk0 : d.k = 0)
    {a : Acc} {bs : List (Option Byte)} {x : BitVec 64} (hk : e.kind = .rd a bs)
    (hx : rebuild 3 bs = .ok (.bits 32 x)) : x.toNat % 16 = 0 := by
  have hev := (lfired hp hX he hσ).1
  have hsl : d.site.loc = true := by rw [hs]; rfl
  -- the read's location
  set o := (if per ≠ .prime ∧ v = false then 32 else 0) + 8 * h.val with ho
  have hl : a.loc = ⟨.local, g, L.localBase + o⟩ ∧ a.size = 4 := by
    obtain ⟨s, vv, kk⟩ := d
    simp only at hs hk0
    subst hs hk0
    simp only [Ev] at hev
    obtain ⟨bs', hk'⟩ := hev
    rw [hk] at hk'
    simp only [Kind.rd.injEq] at hk'
    obtain ⟨rfl, -⟩ := hk'
    have hx' : rv p L g (wOf b) ⟨.lw per v h, vv, 0⟩ (lwBase (pk per v)) =
        BitVec.ofNat 64 (L.localBase + (if per ≠ .prime ∧ v = false then 32 else 0)) := by
      cases per <;> cases v <;> rfl
    have hlb := hp.localMemory.2.1
    refine ⟨?_, rfl⟩
    rw [hx']
    cases per <;> cases v <;> fin_cases h <;>
      simp [ho, lacc, Loc.at, lwOff, wrapAddr, truncBits, BitVec.toNat_add, BitVec.toNat_ofInt] <;>
      omega
  obtain ⟨hla, hsz⟩ := hl
  -- an earlier store at the offset
  obtain ⟨k0, A0, -, hC⟩ := hJ.refE
  have hlst := hC.lst o (by
    rw [ho]; cases per <;> cases v <;> fin_cases h <;> simp [lstOffs])
  have hpos : 1 ≤ lstAt d.site k0 A0 o := by rw [hs, ho]; exact lst_lw per v h k0 A0
  have hoff : o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40 := by
    rw [ho]; cases per <;> cases v <;> fin_cases h <;> simp
  clear_value o
  have h0 : 0 < n (.load (.lst o)) := by simp only [lcn] at hlst; omega
  obtain ⟨j0, hj0, f0, hf0, hc0⟩ := exists_of_count hσ h0
  obtain ⟨pc0, kind0⟩ := f0
  obtain ⟨a0, bs0, rfl, hl0⟩ : ∃ a0 bs0, kind0 = .wr a0 bs0 ∧
      a0.loc = ⟨.local, g, L.localBase + o⟩ := by
    cases kind0 <;> simp [Proof.cls, Loader.cls] at hc0
    exact ⟨_, _, rfl, hc0⟩
  have hw0 : X.Writes (g, j0) a0 bs0 := ⟨pc0, hf0⟩
  obtain ⟨-, -, o', hl0', hz0⟩ := wr_before hp hX hnb hj0 (.inl hw0)
  have ho' : o' = o := by
    rw [hl0] at hl0'
    simp only [Loc.mk.injEq] at hl0'
    omega
  subst o'
  have hr : X.Reads (g, k) a bs := by
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    exact ⟨pc, he⟩
  have hlen := (hX.rf (.thread (g, k)) a bs (Or.inl hr)).1
  have hq : (o = 96 ∨ o = 100 ∨ o = 64 ∨ o = 68) ∧ 0 = 0 ∨
      (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ 0 ≤ 4 := by
    right; refine ⟨?_, by omega⟩
    rw [ho]; cases per <;> cases v <;> fin_cases h <;> simp
  have hla' : a.loc = ⟨.local, g, L.localBase + o + 0⟩ := by rw [hla, Nat.add_zero]
  -- every byte is a byte of an integer
  have hbytes : ∀ z ∈ bs, ∃ y, z = some y ∧ SByte y := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := List.getElem_of_mem hz
    have hi4 : i < a.size := by omega
    obtain ⟨j, dst, bytes, hj, hmw, hcov, hval⟩ := Frame.local_read_src hX hr (by rw [hla])
      (by rw [hla]) hi4 hw0 hj0 (by rw [hla']; exact cover_of hl0' hz0 hq (by omega))
    obtain ⟨hb, hbl, -⟩ := wr_before hp hX hnb hj hmw
    rw [List.getElem?_eq_getElem hi, hzi, Option.some.injEq] at hval
    rw [hval]
    unfold wbyte
    have hin : (a.loc.at i).addr - dst.loc.addr < bytes.length := by
      simp only [Acc.Covers, Loc.InRange] at hcov
      omega
    exact ⟨_, List.getElem?_eq_getElem hin, hb _ (List.getElem_mem hin)⟩
  -- byte 0 is byte 0 of a pointer round's store
  obtain ⟨j, dst, bytes, hj, hmw, hcov, hval⟩ := Frame.local_read_src hX hr (by rw [hla])
    (by rw [hla]) (show 0 < a.size by omega) hw0 hj0
    (by rw [hla']; exact cover_of hl0' hz0 hq (by omega))
  obtain ⟨-, -, o2, hl2, hz2⟩ := wr_before hp hX hnb hj hmw
  have hcv := hcov
  simp only [Acc.Covers, Loc.InRange, Loc.at, hla, hl2, true_and] at hcv
  have hd8 : dst.size = 8 ∧ o2 = o := by
    rcases hq with ⟨hq1, -⟩ | ⟨hq1, -⟩ <;> rcases hz2 with ⟨hz1, hz2'⟩ | ⟨hz1, hz2'⟩ <;>
      rw [hz2'] at hcv <;> omega
  obtain ⟨y, hy, hb0⟩ := wr_pt hp hX hnb hj hmw hd8.1
  have hidx : (a.loc.at 0).addr - dst.loc.addr = 0 := by
    simp only [Loc.at, hla, hl2, hd8.2]; omega
  unfold wbyte at hval
  rw [hidx, hb0] at hval
  obtain ⟨b0, rest, rfl⟩ : ∃ b0 rest, bs = b0 :: rest := by
    cases bs with
    | nil => simp at hlen; omega
    | cons b0 rest => exact ⟨b0, rest, rfl⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hval
  rw [rebuild_low hval (by omega) hbytes hx]
  exact hy

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
