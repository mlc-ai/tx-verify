-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Mem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.RowAddr
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Lemmas.Flow.AllocTmpl
import Lemmas.Kernel.Source.LocalOwned

@[expose] public section

/-! # A local load of the loader reads the lane's last store

The stores of a loader lane write a page word (96, 100), a row word (64, 68) or the address of a
row (0, 8, 32, 40), as `StoreOk` says; stores at different offsets do not overlap. So a local load
returns the word of the lane's last store at its offset (`load_last`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- What a store of a loader lane writes. -/
def StoreOk (p : Params) (L : Launch) (g : Nat) (a : Acc) (bs : List Byte) : Prop :=
  ∃ o, a.loc = ⟨.local, g, L.localBase + o⟩ ∧
    ((o = 96 ∨ o = 100) ∧ a.size = 4 ∧ (∃ x, PageW p x ∧ bs = (Value.bits 32 x).toBytes) ∨
      (o = 64 ∨ o = 68) ∧ a.size = 4 ∧ (∃ x, RowV x ∧ bs = (Value.bits 32 x).toBytes) ∨
      (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ a.size = 8 ∧
        ∃ y, RowA p y ∧ bs = (Value.bits 64 y).toBytes)

/-- The lane's last store at offset `o` before position `k` is at `j`. -/
def LastAt (L : Launch) (X : Execution) (g k o j : Nat) (a : Acc) (bs : List Byte) : Prop :=
  j < k ∧ X.Writes (g, j) a bs ∧ a.loc = ⟨.local, g, L.localBase + o⟩ ∧
    ∀ j', j < j' → j' < k → ∀ a' bs', X.Writes (g, j') a' bs' →
      a'.loc ≠ ⟨.local, g, L.localBase + o⟩

/-- A lane with a store at an offset has a last one. -/
theorem exists_last {k o j0 : Nat} {a0 : Acc} {bs0 : List Byte} (hj : j0 < k)
    (hw : X.Writes (g, j0) a0 bs0) (hl : a0.loc = ⟨.local, g, L.localBase + o⟩) :
    ∃ j a bs, LastAt L X g k o j a bs := by
  classical
  let P : Nat → Prop := fun j => j < k ∧ ∃ a bs, X.Writes (g, j) a bs ∧
    a.loc = ⟨.local, g, L.localBase + o⟩
  have hP : P (Nat.findGreatest P k) := Nat.findGreatest_spec (P := P) hj.le ⟨hj, a0, bs0, hw, hl⟩
  obtain ⟨h1, a, bs, h2, h3⟩ := hP
  refine ⟨_, a, bs, h1, h2, h3, fun j' hj' hk a' bs' hw' hl' => ?_⟩
  exact Nat.findGreatest_is_greatest (P := P) hj' hk.le ⟨hk, a', bs', hw', hl'⟩

theorem LastAt.mono {k o j : Nat} {a : Acc} {bs : List Byte} (h : LastAt L X g k o j a bs)
    (hk : ∀ a' bs', ¬ X.Writes (g, k) a' bs') : LastAt L X g (k + 1) o j a bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, h2, h3, fun j' hj hk' a' bs' hw => ?_⟩
  rcases Nat.lt_or_ge j' k with h | h
  · exact h4 j' hj h a' bs' hw
  · obtain rfl : j' = k := by omega
    exact (hk _ _ hw).elim

/-- Two last stores at an offset are one. -/
theorem LastAt.unique {k o j j' : Nat} {a a' : Acc} {bs bs' : List Byte}
    (h : LastAt L X g k o j a bs) (h' : LastAt L X g k o j' a' bs') : a = a' ∧ bs = bs' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  obtain rfl : j = j' := by
    rcases Nat.lt_trichotomy j j' with hlt | rfl | hlt
    · exact (h4 j' hlt h1' _ _ h2' h3').elim
    · rfl
    · exact (h4' j hlt h1 _ _ h2 h3).elim
  obtain ⟨pc, e⟩ := h2
  obtain ⟨pc', e'⟩ := h2'
  rw [e] at e'
  cases e'
  exact ⟨rfl, rfl⟩

/-- **A local load of the loader returns bytes of the lane's last store at its offset.** -/
theorem load_last (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hall : ∀ j < k, ∀ a bs, X.Writes (g, j) a bs → StoreOk p L g a bs)
    {a a' : Acc} {bs : List (Option Byte)} {bs' : List Byte} {o q j : Nat}
    (hr : X.Reads (g, k) a bs) (hl : a.loc = ⟨.local, g, L.localBase + o + q⟩) (hz : a.size = 4)
    (hL : LastAt L X g k o j a' bs')
    (hq : q = 0 ∨ q = 4 ∧ (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40)) :
    ∀ i < 4, bs[i]? = some (bs'[q + i]?) := by
  obtain ⟨hjk, hw, hl', hmax⟩ := hL
  obtain ⟨o1, ho1, hsz⟩ := hall j hjk _ _ hw
  have ho : o1 = o := by
    rw [hl'] at ho1
    simp only [Loc.mk.injEq] at ho1
    omega
  subst o1
  intro i hi
  have hcov : a'.Covers (a.loc.at i) := by
    simp only [Acc.Covers, Loc.InRange, Loc.at, hl, hl', true_and]
    omega
  have h := Frame.local_read_byte hX hr hw (k := i) (by omega) hcov (by rw [hl]) hjk ?_
  · rw [h]
    simp only [wbyte, Loc.at, hl, hl']
    congr 2
    omega
  · intro j' d hacc hd
    by_contra hcon
    have hj1 : j < j' := by omega
    have hj2 : j' ≤ k := by omega
    rcases hacc with ⟨_, -, hf⟩ | ⟨bs2, hw2, -⟩ | ⟨_, _, hrm⟩
    · cases hf
    · rcases Nat.lt_or_ge j' k with hlt | hge
      · obtain ⟨o2, ho2, hsz2⟩ := hall j' hlt _ _ hw2
        have hne := hmax j' hj1 hlt _ _ hw2
        refine hne ?_
        rw [ho2]
        simp only [Acc.Covers, Loc.InRange, Loc.at, hl, ho2, true_and] at hd
        simp only [Loc.mk.injEq, true_and]
        omega
      · obtain rfl : j' = k := by omega
        obtain ⟨pc, e⟩ := hr
        obtain ⟨pc', e'⟩ := hw2
        rw [e] at e'
        cases e'
    · exact noActualRmw hX hrm

theorem rebuild_bits32 (y : BitVec 64) :
    rebuild 3 ((Value.bits 32 y).toBytes.map some) = .ok (.bits 32 y) := by
  have h := rebuild_b32 y.toNat
  have e : b32 y.toNat = .bits 32 y := by simp [b32]
  rwa [e] at h

/-- Four bytes of a 32-bit or 64-bit integer, in order. -/
theorem rebuild_part {wd q : Nat} {y x : BitVec 64} {bs : List (Option Byte)}
    (hwd : wd = 32 ∧ q = 0 ∧ y.toNat < 2 ^ 32 ∨ wd = 64 ∧ (q = 0 ∨ q = 4)) (hl : bs.length = 4)
    (hb : ∀ i < 4, bs[i]? = some ((Value.bits wd y).toBytes[q + i]?))
    (hx : rebuild 3 bs = .ok (.bits 32 x)) : x.toNat = y.toNat / 256 ^ q % 2 ^ 32 := by
  have hbs : bs = [some (.bits wd y, q), some (.bits wd y, q + 1), some (.bits wd y, q + 2),
      some (.bits wd y, q + 3)] := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 4
    · rw [hb i hi]
      rcases hwd with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl | rfl⟩ <;> interval_cases i <;> rfl
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  subst hbs
  rcases hwd with ⟨rfl, rfl, hy⟩ | ⟨rfl, hq⟩
  · have h1 : rebuild 3 ([some (.bits 32 y, 0), some (.bits 32 y, 0 + 1), some (.bits 32 y, 0 + 2),
        some (.bits 32 y, 0 + 3)] : List (Option Byte)) = .ok (.bits 32 y) := rebuild_bits32 y
    rw [h1] at hx
    simp only [Except.ok.injEq, Value.bits.injEq, true_and] at hx
    subst hx
    omega
  · have hle : littleEndianBits [some (.bits 64 y, q), some (.bits 64 y, q + 1),
        some (.bits 64 y, q + 2), some (.bits 64 y, q + 3)] =
        some (y.toNat / 256 ^ q % 256 + 256 * (y.toNat / 256 ^ (q + 1) % 256 + 256 *
          (y.toNat / 256 ^ (q + 2) % 256 + 256 * (y.toNat / 256 ^ (q + 3) % 256 + 256 * 0)))) := by
      rcases hq with rfl | rfl <;> rfl
    have hh : rebuild.halves 2 [some (.bits 64 y, q), some (.bits 64 y, q + 1),
        some (.bits 64 y, q + 2), some (.bits 64 y, q + 3)] =
        .ok (.bits 32 (BitVec.ofNat 64 (y.toNat / 256 ^ q % 256 + 256 *
          (y.toNat / 256 ^ (q + 1) % 256 + 256 * (y.toNat / 256 ^ (q + 2) % 256 + 256 *
            (y.toNat / 256 ^ (q + 3) % 256 + 256 * 0)))))) := by
      unfold rebuild.halves
      simp [intByte, rebuildBits, hle]
      rfl
    have hr : rebuild 3 [some (.bits 64 y, q), some (.bits 64 y, q + 1),
        some (.bits 64 y, q + 2), some (.bits 64 y, q + 3)] =
        rebuild.halves 2 [some (.bits 64 y, q), some (.bits 64 y, q + 1),
        some (.bits 64 y, q + 2), some (.bits 64 y, q + 3)] := by
      unfold rebuild
      rcases hq with rfl | rfl
      · simp [Value.bytes]
      · rfl
    rw [hr, hh] at hx
    simp only [Except.ok.injEq, Value.bits.injEq, true_and] at hx
    subst hx
    rw [BitVec.toNat_ofNat]
    rcases hq with rfl | rfl <;> norm_num <;> omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
