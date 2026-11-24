-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Lib.Start
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Lemmas.Kernel.Followed
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Lemmas.Kernel.Source.LocalSrc
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The words of the loader's local loads

A pointer round's page and row loads and a packet's address loads read the lane's local memory.
Each returns a 32-bit word: the lane stored at the loaded offset before (the ledger's count `lst o`
is positive there, `Loader/Local.lean`), so by `Frame.local_read_src` every byte comes from an
earlier store of the lane that covers it, and every store of a loader lane writes the bytes of a
32-bit word (the page-table rounds) or of a 64-bit address (the pointer rounds), as many bytes as
the store's size, `wr_ev`; so every loaded byte is a byte of such an integer (`SByte`), and four
such bytes rebuild to a 32-bit word (`rebuild4_ok`). The page-table loads read the launch's page
table (`Page.lean`). -/

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

/-- A byte of a 32-bit or 64-bit integer, with its index below the integer's size. -/
def SByte (b : Byte) : Prop := ∃ wd x i, b = (.bits wd x, i) ∧ (wd = 32 ∨ wd = 64) ∧ i < wd / 8

/-- **Four bytes of 32-bit or 64-bit integers rebuild to a 32-bit word.** -/
theorem rebuild4_ok {bs : List (Option Byte)} (hl : bs.length = 4)
    (h : ∀ b ∈ bs, ∃ y, b = some y ∧ SByte y) : ∃ x, rebuild 3 bs = .ok (.bits 32 x) := by
  have hw : ∀ b ∈ bs, WordByte b := by
    intro b hb
    obtain ⟨y, rfl, wd, x, i, rfl, hwd, -⟩ := h b hb
    exact .inr ⟨wd, x, i, rfl, hwd⟩
  have hle : ∃ n, littleEndianBits bs = some n := by
    clear hl hw
    induction bs with
    | nil => exact ⟨0, rfl⟩
    | cons b bs ih =>
      obtain ⟨y, rfl, wd, x, i, rfl, hwd, hi⟩ := h b (List.mem_cons_self ..)
      obtain ⟨n, hn⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hb : (Value.bits wd x).bytes = wd / 8 := by
        rcases hwd with rfl | rfl <;> rfl
      simp [littleEndianBits, byteBits, hn, hb, hi, Value.bitPattern]
  rcases rebuild_word4 hl hw with h1 | ⟨er, her⟩
  · exact h1
  · exfalso
    obtain ⟨n, hn⟩ := hle
    have hnone : none ∉ bs := by
      intro hm; obtain ⟨y, hy, -⟩ := h none hm; cases hy
    have hall : bs.all intByte = true := by
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨y, rfl, wd, x, i, rfl, -, -⟩ := h b hb
      rfl
    have hh : rebuild.halves 2 bs = .ok (.bits 32 (BitVec.ofNat 64 n)) := by
      unfold rebuild.halves
      simp only [hnone, ↓reduceIte, hall, true_or, rebuildBits, hn, hl]
      rfl
    revert her
    unfold rebuild
    split
    · split
      · intro h'; cases h'
      · rw [hh]; intro h'; cases h'
    · rw [hh]; intro h'; cases h'

/-- The bytes of a store of a 32-bit or 64-bit integer: as many as its size. -/
theorem store_bytes {wd : Nat} {x : BitVec 64} {v' : Value} (hwd : wd = 32 ∨ wd = 64)
    (h : storeValue wd (.bits wd x) = .ok v') :
    (∀ b ∈ v'.toBytes, SByte b) ∧ v'.toBytes.length = wd / 8 := by
  have hv : v' = .bits wd x := by
    rcases hwd with rfl | rfl <;> simp [storeValue, Value.bytes, pure, Except.pure] at h <;>
      exact h.symm
  subst hv
  have hb : (Value.bits wd x).bytes = wd / 8 := by rcases hwd with rfl | rfl <;> rfl
  refine ⟨fun b hb' => ?_, by simp [Value.toBytes, hb]⟩
  simp only [Value.toBytes, List.mem_map, List.mem_range] at hb'
  obtain ⟨i, hi, rfl⟩ := hb'
  exact ⟨wd, x, i, rfl, hwd, hb ▸ hi⟩

/-- The local offsets of a loader lane's stores and their sizes. -/
def StoreAt (L : Launch) (g : Nat) (a : Acc) : Prop :=
  ∃ o, a.loc = ⟨.local, g, L.localBase + o⟩ ∧
    ((o = 96 ∨ o = 100 ∨ o = 64 ∨ o = 68) ∧ a.size = 4 ∨
      (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ a.size = 8)

set_option maxHeartbeats 4000000 in
/-- **Every store of a loader lane** writes the bytes of a 32-bit word to one of the page-table
rounds' offsets, or the bytes of a 64-bit address to one of the pointer rounds' offsets; no loader
site makes an atomic access. -/
theorem wr_ev (hp : Pre p L m) {d : D} {e : Event} (hev : Ev p L g w d e) :
    (∀ a bs, e.kind = .wr a bs → (∀ b ∈ bs, SByte b) ∧ bs.length = a.size ∧ StoreAt L g a) ∧
      ∀ a old new, e.kind ≠ .rmw a old new := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case pgSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · subst hk
      refine ⟨fun a bs h => ?_, fun _ _ _ h => (by cases h)⟩
      simp only [Kind.wr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(store_bytes (.inl rfl) hv').1, (store_bytes (.inl rfl) hv').2, 96 + 4 * it.val, ?_,
        .inl ⟨?_, rfl⟩⟩
      · have hx : rv p L g w ⟨.pgSt per it, v, kk⟩ (pgStA per) =
            add64 (BitVec.ofNat 64 (L.localBase + 96)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
          cases per <;> rfl
        rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc]
        exact lacc_loc hp (by omega) 4
      · fin_cases it <;> simp
    · subst hk; exact ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  case rwSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · subst hk
      refine ⟨fun a bs h => ?_, fun _ _ _ h => (by cases h)⟩
      simp only [Kind.wr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(store_bytes (.inl rfl) hv').1, (store_bytes (.inl rfl) hv').2, 64 + 4 * it.val, ?_,
        .inl ⟨?_, rfl⟩⟩
      · have hx : rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStA per) =
            add64 (BitVec.ofNat 64 (L.localBase + 64)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
          cases per <;> rfl
        rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc]
        exact lacc_loc hp (by omega) 4
      · fin_cases it <;> simp
    · subst hk; exact ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  case ptS per b it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    · subst hk
      refine ⟨fun a bs h => ?_, fun _ _ _ h => (by cases h)⟩
      simp only [Kind.wr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(store_bytes (.inr rfl) hv').1, (store_bytes (.inr rfl) hv').2,
        ptOff per b + 8 * it.val, ?_, .inr ⟨?_, rfl⟩⟩
      · have hx : rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).u =
            add64 (BitVec.ofNat 64 (L.localBase + ptOff per b))
              (shl64 (m64 ((it.val : Nat) : Int)) 3) := by
          cases per <;> cases b <;> rfl
        rw [hx, shl64_fin3, add64_ofNat, Nat.add_assoc]
        exact lacc_loc hp (by cases per <;> cases b <;> simp [ptOff] <;> omega) 8
      · cases per <;> cases b <;> fin_cases it <;> simp [ptOff]
    · subst hk; exact ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  all_goals
    simp only [Ev, Epilogue.Ev, Site.toE] at hev
    shape_destruct hev
    all_goals subst_vars
    all_goals exact ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

/-- The sites of the lane's local loads. -/
def _root_.PTX.Kernels.TmlFa4Fwd.Proof.Loader.Site.loc : Site → Bool
  | .ptP _ _ _ | .ptR _ _ _ | .lw _ _ _ => true
  | _ => false

/-- **The writes of a followed loader lane before an event**: each writes the bytes of an integer
at a store offset (`wr_ev`); the startup writes nothing. -/
theorem wr_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L w) X (g, j)) {j : Nat} (hj : j < k)
    {dst : Acc} {bytes : List Byte} (hw : X.MemWrites (.thread (g, j)) dst bytes) :
    (∀ b ∈ bytes, SByte b) ∧ bytes.length = dst.size ∧ StoreAt L g dst := by
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
  rcases good_cases hp hX hf hub hG with ⟨s, n, hσ, hS, -⟩ | ⟨b, d, n, hσ, hb, -, -, -⟩
  · exact (start_no_wr (start_fired hp hX hf hσ).1 hS hk).elim
  · have hev := (lfired hp hX hf hσ).1
    obtain ⟨h1, h2⟩ := wr_ev hp hev
    rcases hk with h | ⟨old, h⟩
    · exact h1 _ _ h
    · exact absurd h (h2 _ _ _)

/-- The location of a local load of a loader lane: an element of four bytes inside one store
offset's word. -/
theorem loc_read (hp : Pre p L m) {d : D} {e : Event} (hev : Ev p L g w d e)
    (hs : d.site.loc = true) :
    ∃ a bs o q, e.kind = .rd a bs ∧ a.size = 4 ∧ a.loc = ⟨.local, g, L.localBase + o + q⟩ ∧
      ((o = 96 ∨ o = 100 ∨ o = 64 ∨ o = 68) ∧ q = 0 ∨ (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ q ≤ 4) ∧
      (∀ k A, 1 ≤ lstAt d.site k A o) := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Site.loc, Bool.false_eq_true] at hs
  case ptP per b it =>
    obtain ⟨a, bs, hk, hl, hz⟩ := ptP_loc hp hev
    exact ⟨a, bs, 96 + 4 * it.val, 0, hk, hz, by rw [hl]; rfl,
      .inl ⟨by fin_cases it <;> simp, rfl⟩, fun k A => lst_ptP per b it k A⟩
  case ptR per b it =>
    obtain ⟨a, bs, hk, hl, hz⟩ := ptR_loc hp hev
    exact ⟨a, bs, 64 + 4 * it.val, 0, hk, hz, by rw [hl]; rfl,
      .inl ⟨by fin_cases it <;> simp, rfl⟩, fun k A => lst_ptR per b it k A⟩
  case lw per b h =>
    simp only [Ev] at hev
    obtain ⟨bs, hk⟩ := hev
    refine ⟨_, bs, (if per ≠ .prime ∧ b = false then 32 else 0) + 8 * h.val, 4 * kk.val, hk, rfl,
      ?_, .inr ⟨by cases per <;> cases b <;> fin_cases h <;> simp, by omega⟩,
      fun k A => lst_lw per b h k A⟩
    have hx : rv p L g w ⟨.lw per b h, v, kk⟩ (lwBase (pk per b)) =
        BitVec.ofNat 64 (L.localBase + (if per ≠ .prime ∧ b = false then 32 else 0)) := by
      cases per <;> cases b <;> rfl
    have hlb := hp.localMemory.2.1
    rw [hx]
    cases per <;> cases b <;> fin_cases h <;> fin_cases kk <;>
      simp [lacc, Loc.at, lwOff, wrapAddr, truncBits, BitVec.toNat_add, BitVec.toNat_ofInt] <;>
      omega

theorem cover_of {o q i : Nat} {a' : Acc} (hl : a'.loc = ⟨.local, g, L.localBase + o⟩)
    (hz : (o = 96 ∨ o = 100 ∨ o = 64 ∨ o = 68) ∧ a'.size = 4 ∨
      (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ a'.size = 8)
    (hq : (o = 96 ∨ o = 100 ∨ o = 64 ∨ o = 68) ∧ q = 0 ∨ (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40) ∧ q ≤ 4)
    (hi : i < 4) : a'.Covers (Loc.at ⟨.local, g, L.localBase + o + q⟩ i) := by
  simp only [Acc.Covers, Loc.InRange, Loc.at, hl, true_and]
  omega

set_option maxHeartbeats 2000000 in
/-- **A local load of a loader lane reads bytes that rebuild to a 32-bit word**: each loaded byte
is a byte of an earlier store of the lane that covers it, inside that store's bytes. -/
theorem local_rebuild (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hJ : Loader.Ref p L g (wOf b) (d, lcn n))
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L (wOf b)) X (g, j))
    (hs : d.site.loc = true) :
    ∃ a bs x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (.bits 32 x) := by
  have hev := (lfired hp hX he hσ).1
  obtain ⟨a, bs, o, q, hk, hz, hl, hq, hpos⟩ := loc_read hp hev hs
  -- an earlier store at the loaded offset
  obtain ⟨k0, A0, -, hC⟩ := hJ.refE
  have hlst := hC.lst o (by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [lstOffs] <;> omega)
  have h0 : 0 < n (.load (.lst o)) := by
    have := hpos k0 A0; simp only [lcn] at hlst; omega
  obtain ⟨j0, hj0, f0, hf0, hc0⟩ := exists_of_count hσ h0
  obtain ⟨pc0, kind0⟩ := f0
  obtain ⟨a0, bs0, rfl, hl0⟩ : ∃ a0 bs0, kind0 = .wr a0 bs0 ∧
      a0.loc = ⟨.local, g, L.localBase + o⟩ := by
    cases kind0 <;> simp [Proof.cls, Loader.cls] at hc0
    exact ⟨_, _, rfl, hc0⟩
  have hw0 : X.Writes (g, j0) a0 bs0 := ⟨pc0, hf0⟩
  obtain ⟨-, -, o', hl0', hz0⟩ := wr_before hp hX hnb hj0 (.inl hw0)
  have ho : o' = o := by
    rw [hl0] at hl0'
    simp only [Loc.mk.injEq] at hl0'
    omega
  subst ho
  -- every byte comes from an earlier store of the lane, inside its bytes
  have hr : X.Reads (g, k) a bs := by
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    exact ⟨pc, he⟩
  have hlen := (hX.rf (.thread (g, k)) a bs (Or.inl hr)).1
  have hbytes : ∀ x ∈ bs, ∃ y, x = some y ∧ SByte y := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi4 : i < a.size := by omega
    obtain ⟨j, dst, bytes, hj, hmw, hcov, hval⟩ := Frame.local_read_src hX hr (by rw [hl])
      (by rw [hl]) hi4 hw0 hj0 (by rw [hl]; exact cover_of hl0' hz0 hq (by omega))
    obtain ⟨hb, hbl, -⟩ := wr_before hp hX hnb hj hmw
    rw [List.getElem?_eq_getElem hi, hxi, Option.some.injEq] at hval
    rw [hval]
    unfold wbyte
    have hin : (a.loc.at i).addr - dst.loc.addr < bytes.length := by
      simp only [Acc.Covers, Loc.InRange] at hcov
      omega
    exact ⟨_, List.getElem?_eq_getElem hin, hb _ (List.getElem_mem hin)⟩
  obtain ⟨x, hx⟩ := rebuild4_ok (by omega) hbytes
  exact ⟨a, bs, x, hk, hx⟩

/-- **A local load of a loader lane returns a 32-bit word.** -/
theorem local_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hJ : Loader.Ref p L g (wOf b) (d, lcn n))
    (hnb : ∀ j < k, ¬ Frame.Bad (thread p L) (Ref p L (wOf b)) X (g, j))
    (hs : d.site.loc = true) : (ret d).accepts e := by
  have hret : ret d = .word 32 := by
    obtain ⟨s, v, kk⟩ := d; cases s <;> simp_all [Site.loc, ret]
  rw [hret]
  obtain ⟨a, bs, x, hk, hx⟩ := local_rebuild hp hX he hσ hJ hnb hs
  intro v hv
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  simp only [recvAll, recv, hx, Option.toList_some, List.mem_singleton] at hv
  exact ⟨_, hv⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
