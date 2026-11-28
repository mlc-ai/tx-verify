-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvOrder
public import Kernels.InklingRelDecode.Proof.Iface.KvCopyForm
public import Kernels.InklingRelDecode.Proof.Lib.KvFoot
import Kernels.InklingRelDecode.Proof.Protocol.Values.KvByte
import Kernels.InklingRelDecode.Proof.Lib.BoxCover
import Kernels.InklingRelDecode.Proof.Protocol.KV.Ready
import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Lemmas.Protocol.SingleTmaRing.ItemCopy

@[expose] public section

/-! # The copies of a use of a ring slot cover it

The ready barrier of a ring slot completes use `u` only when the eight copies of the use are
counted (`SingleTmaRing.consumer_observes`), and the eight boxes of 8192 bytes lie in the slot's
K and V tiles and are disjoint (two copies of one use that write one byte are one event), so they
cover the 65536 bytes of the two tiles. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared Lib

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A copy of the ready barrier of slot `σ` of CTA `c` writes bytes of that slot in that CTA.** -/
theorem copy_dest (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) {gl kl pc a sp x y z l c} {σ : Fin 3}
    (he : X.get (gl, kl) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = Iface.kvReadyLoc L c σ)
    (hw : TensorCopy.writeLoc sp x y z = some l) : l.cta = c ∧ Iface.InSlot L σ.val l.addr := by
  have intent : X.Intent (.async (gl, kl) (.write (.load x y z))) { loc := l, size := 1 } true :=
    ⟨rfl, sp, a, ⟨pc, he⟩, hw, rfl⟩
  have cov : ({ loc := l, size := 1 } : Acc).Covers l := by simp [Acc.Covers, Loc.InRange]
  obtain ⟨g, k, pc', a', sp', x', y', z', σ', heq, he', bar, lcta, lslot, -⟩ :=
    copy_write_facts hp hX hf intent cov (fun _ _ => nofun)
  cases heq
  obtain ⟨-, -, rfl⟩ := Event.mk.inj (Option.some.inj (he.symm.trans he'))
  obtain ⟨-, hc, hs⟩ := Loc.mk.inj (hm.symm.trans bar)
  have hσ : σ' = σ := Fin.ext (by
    have : L.sharedBase + Iface.kvReady σ = L.sharedBase + Iface.kvReady σ' := hs
    simp only [Iface.kvReady] at this
    omega)
  exact ⟨lcta.trans hc.symm, hσ ▸ lslot⟩

/-- **A copy item of a use of slot `σ` of CTA `c`** is a notified copy of the use, of a box of a
slab of a block that exists, into the CTA. -/
theorem item_facts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (form : Iface.KvCopyForm Q L X) {c u} {σ : Fin 3} (hcg : c < L.grid)
    {k : SingleTmaRing.Kind ((KV.decl Q L X c).slot σ)}
    (hx : (k, u) ∈ SingleTmaRing.SF X ((KV.decl Q L X c).slot σ)) (hk : k.val ≠ 0) :
    ∃ pc a sp o r sl kvh isV hh dst bar,
      X.get (SingleTmaRing.opF X ((KV.decl Q L X c).slot σ) k u) = some ⟨pc, .tensorIssue a sp⟩ ∧
      sp.mbar = Iface.kvReadyLoc L c σ ∧
      SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ)
        (SingleTmaRing.opF X ((KV.decl Q L X c).slot σ) k u) = u ∧
      X.tensor (SingleTmaRing.opF X ((KV.decl Q L X c).slot σ) k u) = some o ∧ o.spec = sp ∧
      o.effects.notified = true ∧ r < Q.b ∧ sl < 2 * Q.blocks r ∧ kvh < kvHeads ∧ isV ≤ 1 ∧
      hh ≤ 1 ∧ dst % 1024 = 0 ∧ sp = Lib.kvCopySpec Q c (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar := by
  have ring := KV.ready_slot hp hX hf rows init hcg σ
  obtain ⟨pc, a, sp, o, he, hm, hu, ho, hos, hn⟩ := SingleTmaRing.item_copy hX ring hx hk
  generalize SingleTmaRing.opF X ((KV.decl Q L X c).slot σ) k u = e at he hu ho ⊢
  obtain ⟨gl, kl⟩ := e
  obtain ⟨r, sl, kvh, isV, hh, dst, bar, hr, hs, hkvh, hV, hH, hal, hsp⟩ := form he
  obtain ⟨l0, h0⟩ := copy_first Q (gl / L.block) (kvh * Q.headCols + 128 * isV + 64 * hh)
    (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar
  have spec : sp = Lib.kvCopySpec Q (gl / L.block) (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar := hsp
  obtain ⟨-, hc1, -⟩ := Lib.copy_foot Q _ _ _ dst bar h0
  rw [← spec] at h0
  obtain ⟨hc0, -⟩ := copy_dest hp hX hf he hm h0
  rw [← hc1, hc0] at spec
  exact ⟨pc, a, sp, o, r, sl, kvh, isV, hh, dst, bar, he, hm, hu, ho, hos, hn, hr, hs, hkvh, hV,
    hH, hal, spec⟩

private theorem slot_range {a : Nat} {σ : Fin 3} (h : Iface.InSlot L σ.val a) :
    (L.sharedBase + 32768 * σ.val ≤ a ∧ a < L.sharedBase + 32768 * σ.val + 32768) ∨
    (L.sharedBase + 98304 + 32768 * σ.val ≤ a ∧
      a < L.sharedBase + 98304 + 32768 * σ.val + 32768) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, lt_of_lt_of_eq h2 (by ring)⟩
  · exact .inr ⟨h1, lt_of_lt_of_eq h2 (by ring)⟩

/-- **A byte of slot `σ` of CTA `c` is written by a copy of any use the ready barrier completed.**
The copy's box is of a slab of a block that exists. -/
theorem ring_copy_exists (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X) (words : RoleBytes L X)
    (hu : NoUbOutside L X) (form : Iface.KvCopyForm Q L X) {c u l} {σ : Fin 3} (hcg : c < L.grid)
    (hsp : l.space = .shared) (hc : l.cta = c) (hs : Iface.InSlot L σ.val l.addr)
    (hpoll : u < okPolls (KV.Ring.ready.obj L c σ) (X.tr (KV.leader L X c 7))) :
    ∃ gl kl pc a sp o x y z r sl kvh isV hh dst bar,
      X.get (gl, kl) = some ⟨pc, .tensorIssue a sp⟩ ∧ X.tensor (gl, kl) = some o ∧ o.spec = sp ∧
      o.effects.notified = true ∧ TensorCopy.writeLoc sp x y z = some l ∧
      copyUseOf X (ringSlot Q L X c σ) (.async (gl, kl) (.write (.load x y z))) = u ∧
      sp.mbar = Iface.kvReadyLoc L c σ ∧ r < Q.b ∧
      sl < 2 * Q.blocks r ∧ kvh < kvHeads ∧ isV ≤ 1 ∧ hh ≤ 1 ∧ dst % 1024 = 0 ∧
      sp = Lib.kvCopySpec Q c (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar := by
  have ring := KV.ready_slot hp hX hf rows init hcg σ
  have fits := KV.slot_fits (Q := Q) (X := X) (L := L) (c := c) (s := σ)
  let kind : Fin 8 → SingleTmaRing.Kind ((KV.decl Q L X c).slot σ) := fun i =>
    ⟨i.val + 1, by have := i.isLt; change _ < 8 + 1; omega⟩
  have mem : ∀ i, (kind i, u) ∈ SingleTmaRing.SF X ((KV.decl Q L X c).slot σ) := fun i =>
    (SingleTmaRing.consumer_observes hX ring fits (b := 0) hpoll (kind i)).1
  have nz : ∀ i, (kind i).val ≠ 0 := fun i => by simp [kind]
  choose pc a sp o r sl kvh isV hh dst bar he hm hu' ho hos hn hr hs' hk hV hH hal hspec using
    fun i => item_facts hp hX hf rows init form hcg (mem i) (nz i)
  let e : Fin 8 → EvId := fun i => SingleTmaRing.opF X ((KV.decl Q L X c).slot σ) (kind i) u
  have hui : ∀ i, SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (e i) = u := hu'
  have einj : ∀ i j, e i = e j → i = j := fun i j h => Fin.ext (by
    have := congrArg Fin.val (SingleTmaRing.item_inj ring (mem i) (mem j) (nz i) (nz j) h)
    simpa [kind] using this)
  have onto : ∀ i t, t < 8192 → ∃ x y z, TensorCopy.writeLoc (sp i) x y z =
      some ⟨.shared, c, dst i + t⟩ := fun i t ht => by
    rw [hspec i]
    exact copy_onto Q c _ _ (dst i) (bar i) rfl rfl (by simp) (by simp; omega)
  have inslot : ∀ i t, t < 8192 → Iface.InSlot L σ.val (dst i + t) := fun i t ht => by
    obtain ⟨x, y, z, hw⟩ := onto i t ht
    exact (copy_dest hp hX hf (he i) (hm i) hw).2
  have intent : ∀ i x y z l, TensorCopy.writeLoc (sp i) x y z = some l →
      X.Intent (.async (e i) (.write (.load x y z))) { loc := l, size := 1 } true :=
    fun i x y z l hw => ⟨rfl, sp i, a i, ⟨pc i, he i⟩, hw, rfl⟩
  have cover : ∀ l : Loc, ({ loc := l, size := 1 } : Acc).Covers l := fun l => by
    simp [Acc.Covers, Loc.InRange]
  have hd : ∀ i j, i ≠ j → dst i + 8192 ≤ dst j ∨ dst j + 8192 ≤ dst i := by
    intro i j ne
    by_contra hov
    push Not at hov
    have ti : max (dst i) (dst j) - dst i < 8192 := by omega
    have tj : max (dst i) (dst j) - dst j < 8192 := by omega
    obtain ⟨xi, yi, zi, wi⟩ := onto i _ ti
    obtain ⟨xj, yj, zj, wj⟩ := onto j _ tj
    rw [show dst i + (max (dst i) (dst j) - dst i) = max (dst i) (dst j) by omega] at wi
    rw [show dst j + (max (dst i) (dst j) - dst j) = max (dst i) (dst j) by omega] at wj
    have hsl : Iface.InSlot L σ.val (max (dst i) (dst j)) := by
      have := inslot i _ ti
      rwa [show dst i + (max (dst i) (dst j) - dst i) = max (dst i) (dst j) by omega] at this
    have reg : InRing L ⟨.shared, c, max (dst i) (dst j)⟩ := by
      unfold Iface.InSlot at hsl
      have := σ.isLt
      exact ⟨rfl, show L.sharedBase ≤ max (dst i) (dst j) by omega,
        show max (dst i) (dst j) < L.sharedBase + 196608 by omega⟩
    rcases copies_use_order hp hX hf rows init words hu (intent i _ _ _ _ wi) (intent j _ _ _ _ wj)
      (cover _) (cover _) reg (fun _ _ => nofun) (fun _ _ => nofun) rfl hsl with h | h | h
    · obtain ⟨hlt, -⟩ := h
      change SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (e i) <
        SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (e j) at hlt
      rw [hui, hui] at hlt
      exact lt_irrefl _ hlt
    · simp only [AsyncCopy.Ref.async.injEq] at h
      exact ne (einj _ _ h.1)
    · obtain ⟨hlt, -⟩ := h
      change SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (e j) <
        SingleTmaRing.copyUse X ((KV.decl Q L X c).slot σ) (e i) at hlt
      rw [hui, hui] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨i, lo, hi⟩ := Lib.boxes_cover (kb := L.sharedBase + 32768 * σ.val)
    (vb := L.sharedBase + 98304 + 32768 * σ.val) (by omega) dst
    (fun i t ht => slot_range (inslot i t ht)) hd (slot_range hs)
  obtain ⟨x, y, z, hw⟩ := copy_onto Q c _ _ (dst i) (bar i) hsp hc lo hi
  rw [← hspec i] at hw
  exact ⟨(e i).1, (e i).2, pc i, a i, sp i, o i, x, y, z, r i, sl i, kvh i, isV i, hh i, dst i,
    bar i, he i, ho i, hos i, hn i, hw, hu' i, hm i, hr i, hs' i, hk i, hV i, hH i, hal i, hspec i⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
