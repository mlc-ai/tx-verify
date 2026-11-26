-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.OutDest
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Global
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.MmaPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Lse

@[expose] public section

/-! # The accesses outside shared memory, by kind

An access that covers a byte outside shared memory is one of three kinds (`GlobalAt`): the LSE
store of a lane of warpgroup 0 (one word per CTA and thread, `64 (s_q ctaid.y + ctaid.x) + t`), a
slot of an output tensor store (an element of the output tensor of the store's CTA tile, the
slot's column a column of its warp and chunk), or a tensor load's read of a byte that is neither
in the output nor in the LSE output (the query and the caches are apart from them, `Pre`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A byte of the output tensor. -/
def OutByte (P : Params) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P

/-- A byte of the LSE output. -/
def LseByte (P : Params) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P

/-- **The kinds of an access of a global byte `l`** (by its stage and direction). -/
inductive GlobalAt (P : Params) (L : Launch) (X : Execution) (l : Loc) :
    Accessor → Bool → Prop where
  /-- The LSE store of lane `g`: its word is `64 ctaOf + tid` of the LSE output. -/
  | lse {g k pc : Nat} {a : Acc} {bs : List Byte} : X.get (g, k) = some ⟨pc, .wr a bs⟩ →
      tidOf L g < 64 → LseByte P l →
      P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) ≤ l.addr →
      l.addr < P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) + 4 →
      GlobalAt P L X l (.thread (g, k)) true
  /-- Slot `(x, y, z)` of the output tensor store of warp `w` and chunk `c` of CTA `ctaOf`. -/
  | store {i : EvId} {x y z addr c : Nat} {s : TensorStore.Spec} : X.TensorStoreIssue i addr s →
      MbarRow.warp L i.1 < 2 → c < 4 →
      s.origin 0 = ((128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c 0 : Nat) : Int) →
      x < 64 → y < 64 → z < 2 →
      l = ⟨.global, 0, P.outBase + 2 * ((ctaOf L i.1 * 64 + y) * 512 +
        (128 * MbarRow.warp L i.1 + [0, 64, 256, 320].getD c 0 + x)) + z⟩ → OutByte P l →
      GlobalAt P L X l (.async i (.write (.store x y z))) true
  /-- A tensor load's read of a byte of an input. -/
  | load {i : EvId} {x y z : Nat} : ¬ OutByte P l → ¬ LseByte P l →
      GlobalAt P L X l (.async i (.read (.load x y z))) false

/-- The LSE word of a lane of warpgroup 0 is inside the LSE output. -/
private theorem lse_cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k pc : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (hget : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hat : MbarRow.Wg0At L g pc)
    (hl : MemRow.Wg0Lse P L g pc a) (hc : a.Covers l) : GlobalAt P L X l (.thread (g, k)) true := by
  have hg := Frame.lt_of_get hX hget
  have ht := wg0_lseLane hp hX hFw hget hat rfl hl.1
  have h128 := MemRow.wg0_tid hat.1
  have hrow := ctaOf_row hp hg
  have hcta : ctaOf L g < P.s_q * P.b := by
    rw [← hp.grid]
    exact (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).mpr hg
  obtain ⟨-, hloc, hsz⟩ := hl
  have hN : lseBytes P = 256 * (P.s_q * P.b) := by unfold lseBytes; ring
  obtain ⟨-, -, hr⟩ := hp.tensorRange
  have ht' : (L.tidOf g).x % 128 = (L.tidOf g).x := Nat.mod_eq_of_lt h128
  have htid : tidOf L g < 64 := by
    show (L.tidOf g).x < 64
    omega
  have hA : a.loc.addr = P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) := by
    rw [hloc]
    change (P.lseBase + 4 * ((ctaidY L g * P.s_q + ctaidX L g) * 64 + (L.tidOf g).x % 128)) %
      2 ^ 64 = _
    rw [← hrow, ht']
    unfold lseBytes at hr hN
    exact Nat.mod_eq_of_lt (by omega)
  have hcl : a.loc.cta = 0 := by rw [hloc]
  have hsp : a.loc.space = .global := by rw [hloc]
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have hb : P.lseBase + 4 * (ctaOf L g * 64 + tidOf L g) + 4 ≤ P.lseBase + lseBytes P := by
    unfold lseBytes at hN ⊢
    omega
  refine .lse hget htid ⟨c1.trans hsp, c2.trans hcl, ?_, ?_⟩ ?_ ?_
  · omega
  · omega
  · omega
  · omega

/-- A tensor store's slot is an output byte of its CTA tile. -/
private theorem store_cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {g k x y z addr : Nat} {s : TensorStore.Spec}
    {a : Acc} {l : Loc} (hi : X.TensorStoreIssue (g, k) addr s)
    (hl : TensorStore.writeLoc s x y z = some a.loc) (hsz : a.size = 1) (hc : a.Covers l) :
    GlobalAt P L X l (.async (g, k) (.write (.store x y z))) true := by
  obtain ⟨hw2, hrows, c, hc4, -, ho⟩ := tensor_store_origin hp hX hFw hnu hi
  obtain ⟨hx, hy, hz, hxo, hq, he, hloc⟩ := out_dest (tensor_store_map hp hX hFw hi) ho hrows hl
  have hg := Frame.lt_of_get hX (Exists.choose_spec hi)
  have hrow := ctaOf_row hp hg
  have hlc : l = a.loc := cover_one hc hsz
  have hv := view_lt he hq hy hxo hz
  refine .store hi hw2 hc4 (boxOrigin_zero ho) hx hy hz ?_ ?_
  · rw [hlc, hloc, hrow]
  · rw [hlc, hloc]
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [tensorBytes] <;> omega

/-- A byte of a range apart from the output and the LSE output is neither. -/
private theorem load_apart {base n ad : Nat} (hlo : base ≤ ad) (hhi : ad < base + n)
    (hO : base + n ≤ P.outBase ∨ P.outBase + tensorBytes P ≤ base)
    (hL : base + n ≤ P.lseBase ∨ P.lseBase + lseBytes P ≤ base) :
    ¬ OutByte P ⟨.global, 0, ad⟩ ∧ ¬ LseByte P ⟨.global, 0, ad⟩ := by
  constructor
  · rintro ⟨-, -, h1, h2⟩
    simp only at h1 h2
    omega
  · rintro ⟨-, -, h1, h2⟩
    simp only at h1 h2
    omega

/-- A tensor load reads a byte of an input, apart from the output and the LSE output. -/
private theorem load_cls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k x y z addr : Nat} {s : TensorCopy.Spec} {a : Acc} {l : Loc}
    (hi : X.TensorIssue (g, k) addr s) (hl : TensorCopy.readLoc s x y z = some a.loc)
    (hsz : a.size = 1) (hc : a.Covers l) :
    GlobalAt P L X l (.async (g, k) (.read (.load x y z))) false := by
  obtain ⟨coord, byte, ad, hlk, hloc⟩ := readLoc_lookup hl
  rw [cover_one hc hsz, hloc]
  suffices h : ¬ OutByte P ⟨.global, 0, ad⟩ ∧ ¬ LseByte P ⟨.global, 0, ad⟩ from
    .load h.1 h.2
  rcases tensor_load_map hp hX hFw hi with hq | ⟨d0, hd, hK⟩
  · obtain ⟨e, he, q, hq', hh, hhh, t, ht, y', hy', rfl⟩ := tiled_in (d := s.descriptor) hq hlk
    have hv := view_lt he hq' hhh ht hy'
    exact load_apart (n := tensorBytes P) (by omega) (by unfold tensorBytes; omega)
      hp.qApartO hp.inputApartLse
  · rw [hd, fourRows_geometry] at hlk
    rcases hK with hK | ⟨hne, hK⟩
    · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
      have hv := kv_lt hr hy'
      exact load_apart (n := cacheBytes P.numBlocks P.blockStride) (by omega)
        (by unfold cacheBytes; omega) hp.kvApartO hp.kvApartLse
    · obtain ⟨r, hr, y', hy', rfl⟩ := kv_in (d := d0) hK hlk
      have hv := kv_lt hr hy'
      exact load_apart (n := cacheBytes P.extraNumBlocks P.extraBlockStride) (by omega)
        (by unfold cacheBytes; omega) (hp.extraKvApartO.resolve_left hne)
        (hp.extraKvApartLse.resolve_left hne)

/-- **The kinds of a global access**: an access of a byte outside shared memory is the LSE store
of a lane, a slot of an output tensor store, or a tensor load's read of an input byte. -/
theorem global_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : NoUbInner L X) {e : Accessor} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Intent e a w) (hc : a.Covers l) (hs : l.space ≠ .shared) :
    GlobalAt P L X l e w := by
  rcases e with ⟨g, k⟩ | ⟨⟨g, k⟩, p⟩
  · have hgl : a.loc.space = .global := by
      rcases access_place hp hX hFw hi with h | ⟨h, -⟩
      · exact h
      · exact absurd (hc.1.trans h) hs
    obtain ⟨rfl, pc, bs, hget, hat, hl⟩ := global_access hp hX hFw hi hgl
    exact lse_cls hp hX hFw hget hat hl hc
  · rcases async_ref hX hi with href | ⟨x, y, z, s, addr, hp', hi', hl, hsz⟩ |
      ⟨x, y, z, s, addr, rfl, hi', hl, hsz⟩
    · exact absurd (async_shRef_shared hp hX hFw href hc) hs
    · rcases hp' with rfl | rfl
      · obtain ⟨rfl, -⟩ := hi
        exact store_cls hp hX hFw hnu hi' hl hsz hc
      · obtain ⟨-, s', addr', ⟨pc', he'⟩, hred, -⟩ := hi
        obtain ⟨pc, he⟩ := hi'
        rw [he] at he'
        simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at he'
        obtain ⟨-, -, rfl⟩ := he'
        rw [(tensorStoreForm hX ⟨pc, he⟩).2.2] at hred
        cases hred
    · obtain ⟨rfl, -⟩ := hi
      exact load_cls hp hX hFw hi' hl hsz hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
