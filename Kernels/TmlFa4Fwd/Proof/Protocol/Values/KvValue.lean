-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.KvSource
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.CpSize
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Source
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Protocol.AsyncSrc
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.CopySource
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Lemmas.Protocol.CpAsync
import Lemmas.Tcgen05.TcMmaF16Pair
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The K/V elements the row copies write

A row copy writes sixteen bytes of a row of a K/V page, or sixteen zero bytes when its key is past
the request's. So every element of a packet's block is a BF16 number (`kv_el_exists`): that of the
cache's element the copy reads (`kv_el_src`), or zero. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma Tm AsyncCopy

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **Element `(row, d)` of packet `t`** of a CTA is the number `x`: the two bytes its copy wrote
rebuild to it. -/
def KvEl (L : Launch) (X : Execution) (c t row d : Nat) (x : ℝ) : Prop :=
  ∃ jc sp bs, KvCp L X c t row d jc sp ∧
    (X.async.copies (kvLane L c row d, jc)).writeBytes = some bs ∧
    (rebuild 1 [bs[2 * (d % 64) % 16]?, bs[2 * (d % 64) % 16 + 1]?] >>= valFloat .bf16) = .ok x

/-- The two zero bytes are zero. -/
theorem rebuild_zero : (rebuild 1 [some zeroByte, some zeroByte] >>= valFloat .bf16) =
    .ok (0 : ℝ) := by
  have h : rebuild 1 [some zeroByte, some zeroByte] = .ok (.bits 16 0) := by
    simp [rebuild, rebuild.halves, zeroByte, Value.byteAt, Value.bytes, Value.toBytes, rebuildBits,
      intByte]
    rfl
  have hd : FloatFmt.bf16.decode 0 = some 0 := by decide +kernel
  rw [h]
  change bitsAsFloat .bf16 (.bits 16 0) = _
  rw [bitsAsFloat_eq (fun f => by simp)]
  simp [Value.bitPattern, Value.bytes, FloatFmt.bytes, hd]
  rfl

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **What a row copy writes**: the launch bytes of its source, and zeros. -/
theorem kv_copy_bytes (hIn : InputsUnwritten p X) {c t row d jc : Nat} {sp : AsyncCopy.Spec}
    {bs : List Byte} (hC : KvCp L X c t row d jc sp)
    (hbs : (X.async.copies (kvLane L c row d, jc)).writeBytes = some bs) :
    bs = initialBytes m X sp.src ++ List.replicate (16 - sp.src.size) zeroByte := by
  have hi : X.Copy (kvLane L c row d, jc) sp := hC.get
  have hs := actualCopyShape hX hi
  have hin := cpInputs hp (cpSrc hp hX hFw) _ _ hi
  have h := whole_copy_write_initial hX hi hC.ld.whole hs.noData hbs (fun k hk => (hin k hk).1)
    (fun k hk w dst bytes hw hc => by
      obtain ⟨-, r, hr, hl⟩ := hin k hk
      exact hIn r hr _ hl w dst bytes hw hc)
  rw [show sp.dst.size = 16 by rw [hC.dst]] at h
  exact h

omit hp hX hFw in
/-- Two bytes of the launch's value at a source. -/
private theorem initial_pair {src : Acc} {v : Value} {n : Nat} {l : Loc} (hv : HasValue m l v)
    (hb : v.bytes = 2) (hn : n + 1 < src.size) (hl : src.loc.at n = l) {z : Nat} (hz : z < 2) :
    (initialBytes m X src)[n + z]? = some (v.byteAt z) := by
  have hlz : src.loc.at (n + z) = l.at z := by rw [← hl]; simp [Loc.at, Nat.add_assoc]
  simp only [initialBytes, List.getElem?_map]
  rw [List.getElem?_range (by omega), Option.map_some, hlz, hv z (by omega)]
  rfl

/-- **The element a copy of sixteen bytes writes**, from the element of the cache it reads. -/
theorem kv_el_of_src (hIn : InputsUnwritten p X) {c t row d jc : Nat} {sp : AsyncCopy.Spec}
    {bs : List Byte} (hC : KvCp L X c t row d jc sp)
    (hbs : (X.async.copies (kvLane L c row d, jc)).writeBytes = some bs) {x : ℝ} {l : Loc}
    (hv : HasValue m l (.float .bf16 x)) (hl : sp.src.loc.at (2 * (d % 64) % 16) = l)
    (hz : sp.src.size = 16) : KvEl L X c t row d x := by
  refine ⟨jc, sp, bs, hC, hbs, ?_⟩
  have hb := kv_copy_bytes hp hX hFw hIn hC hbs
  rw [hz] at hb
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at hb
  have h0 := initial_pair (X := X) (src := sp.src) hv rfl (by omega) hl (z := 0) (by decide)
  have h1 := initial_pair (X := X) (src := sp.src) hv rfl (by omega) hl (z := 1) (by decide)
  rw [hb]
  rw [show 2 * (d % 64) % 16 = 2 * (d % 64) % 16 + 0 from rfl] at h0 ⊢
  rw [h0, Nat.add_zero, h1]
  exact rebuild_number (.inr rfl) x

/-- **Every element of a packet's block is a number.** -/
theorem kv_el_exists (hIn : InputsUnwritten p X) {t row d : Nat} (hR : KvRead L X g k t)
    (hrow : row < 128) (hd : d < 128) : ∃ x, KvEl L X (g / L.block) t row d x := by
  obtain ⟨jc, sp, hC, hw⟩ := kv_copy_exists hp hX hFw hR hrow hd
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hw
  obtain ⟨-, hyw, -⟩ := kvLane_spec (L := L) hp (c := g / L.block) (row := row) (d := d)
  obtain ⟨pc, hge⟩ := hC.get
  rcases ld_cp_size hp hX hFw hyw hge with hz | hz
  · refine ⟨0, jc, sp, bs, hC, hbs, ?_⟩
    have hb := kv_copy_bytes hp hX hFw hIn hC hbs
    rw [hz] at hb
    have : initialBytes m X sp.src = [] := by simp [initialBytes, hz]
    rw [this, List.nil_append] at hb
    have hg : ∀ n < 16, bs[n]? = some zeroByte := fun n hn => by
      rw [hb, List.getElem?_replicate]
      simp [hn]
    rw [hg _ (by omega), hg _ (by omega)]
    exact rebuild_zero
  · obtain ⟨lay, hl, page, hpg, h, hh, r, hr, c, hc2, tt, ht, hloc, -⟩ :=
      ld_cp_src hp hX hFw hyw hge
    obtain ⟨hkv, hvv⟩ := hp.kvBytes page hpg h hh r hr (8 * tt + 64 * c + d % 8) (by omega)
    have hll : sp.src.loc.at (2 * (d % 64) % 16) =
        lay.loc page h r (8 * tt + 64 * c + d % 8) := by
      rw [hloc]
      simp only [CacheLayout.loc, globalLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
    rcases hl with rfl | rfl
    · exact ⟨_, kv_el_of_src hp hX hFw hIn hC hbs hkv hll hz⟩
    · exact ⟨_, kv_el_of_src hp hX hFw hIn hC hbs hvv hll hz⟩

/-- **An element of a packet's block is one number.** -/
theorem KvEl.unique {c t row d : Nat} {x y : ℝ} (h : KvEl L X c t row d x)
    (h' : KvEl L X c t row d y) : x = y := by
  obtain ⟨jc, sp, bs, hC, hbs, hx⟩ := h
  obtain ⟨jc', sp', bs', hC', hbs', hy⟩ := h'
  obtain ⟨pc, hg⟩ := hC.get
  obtain ⟨pc', hg'⟩ := hC'.get
  have hjj : (kvLane L c row d, jc) = (kvLane L c row d, jc') := by
    refine kv_copy_unique hp hX hFw hg hg' (hC.covers hp (z := 0) (by decide)).1
      (hC'.covers hp (z := 0) (by decide)).1 ?_
    unfold pkt
    rw [hC.cnt, hC'.cnt]
  obtain rfl := (Prod.mk.injEq ..).mp hjj |>.2
  rw [hbs] at hbs'
  obtain rfl := Option.some.inj hbs'
  rw [hx] at hy
  exact Except.ok.inj hy

/-- **A K/V operand element is the block's element.** -/
theorem kv_elem16 {t row d idx dd : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {ops : AsyncCopy.MmaOperands} {x : ℝ} (hR : KvRead L X g k t)
    (hi : X.MmaIssue (g, k) dd s acc mask) (hops : X.async.mmaOperands (g, k) = some ops)
    (hrow : row < 128) (hd : d < 128) (hx : KvEl L X (g / L.block) t row d x)
    (hbl : ∀ z < 2, s.byteLoc .b (idx + z) =
      some (blockLoc (g / L.block) (kvBase L (t % 3)) row d z)) : Elem16 ops.b idx x := by
  obtain ⟨jc, sp, bs, hC, hbs, e0⟩ := kv_operand hp hX hFw hR hi hops hrow hd (z := 0) (by decide)
    (hbl 0 (by decide))
  obtain ⟨jc', sp', bs', hC', hbs', e1⟩ := kv_operand hp hX hFw hR hi hops hrow hd (z := 1)
    (by decide) (hbl 1 (by decide))
  obtain ⟨j2, sp2, bs2, hC2, hbs2, hx2⟩ := hx
  have huniq : ∀ {j j' : Nat} {a a' : AsyncCopy.Spec}, KvCp L X (g / L.block) t row d j a →
      KvCp L X (g / L.block) t row d j' a' → j = j' := by
    intro j j' a a' h h'
    obtain ⟨pc, hg⟩ := h.get
    obtain ⟨pc', hg'⟩ := h'.get
    have := kv_copy_unique hp hX hFw hg hg' (h.covers hp (z := 0) (by decide)).1
      (h'.covers hp (z := 0) (by decide)).1 (by unfold pkt; rw [h.cnt, h'.cnt])
    exact ((Prod.mk.injEq ..).mp this).2
  obtain rfl := huniq hC2 hC
  obtain rfl := huniq hC2 hC'
  rw [hbs2] at hbs hbs'
  obtain rfl := Option.some.inj hbs
  obtain rfl := Option.some.inj hbs'
  rw [Nat.add_zero, Nat.add_zero] at e0
  rw [show (2 * (d % 64) + 1) % 16 = 2 * (d % 64) % 16 + 1 by omega] at e1
  exact ⟨_, _, e0, e1, hx2⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
