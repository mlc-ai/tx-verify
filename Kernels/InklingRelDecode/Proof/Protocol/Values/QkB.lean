-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
import Kernels.InklingRelDecode.Proof.Protocol.KV.ReadUse
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Lib.KvGeom
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns

@[expose] public section

/-! # The B element of a QK MMA is the key it names

The B operand of step `j` of the QK MMA of block `b` has, at row `r` and column `kk`, the cache
element of the key row `r % 64` of slab half `r / 64` of block `b`, column `16 (j % 4) + kk` of the
half `j / 4` of the K head: the copy that wrote it is the one of block `b` of its slot
(`kv_b_fact`, with the use counts of `qk_empty_count`), and the swizzle puts its bytes where the
copy wrote them (`qk_b_geom`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem qk_b_elem (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) {j : Fin 8} (hj : pc = Lib.qkIssue j)
    {row kk b : Nat} (hrow : row < 128) (hk : kk < 16)
    (hb : pollRound 2462 ((X.tr g).take k) = b + 1) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row kk =
        .ok (kvElem Q L (g / L.block) b 0 (row / 64) (j.val / 4) (16 * (j.val % 4) + kk)
          (row % 64)) := by
  obtain ⟨b', -, hq, -, warp, desc⟩ := Mma.Export.qk_block hp hX hf base he ⟨j, hj⟩
  have eb : b = b' := by omega
  subst eb
  have ne : ∀ j j' : Fin 8, Lib.qkIssue j ≠ Lib.pvIssue j' := by decide
  obtain ⟨-, -, hbd⟩ := desc j hj
  obtain ⟨-, -, -, b2, hd⟩ := Mma.Export.columns hp hX hf base he
  have hD : s.descriptor = Lib.qkDesc := by
    rcases hd with ⟨j', -, -, -, hd⟩ | ⟨j', hpc, -, -, -⟩
    · exact hd
    · exact absurd (hj.symm.trans hpc) (ne j j')
  obtain ⟨c, σ, n, isV, h, hh, x, y, l0, hcg, hg, hl0, hc0, hs0, hn3, hn, hV, hH, hhh, hx, hy,
    ⟨bar, hwl⟩, hel⟩ := kv_b_fact hp hX hf rows init words hu nub form base he hops hrow hk
  have hgc : g / L.block = c := by
    have := (KV.leader_warp (X := X) (L := L) (m := m) hp hcg (by omega : 7 < 8)).2.1
    rwa [← hg] at this
  obtain ⟨cta, hloc⟩ := Lib.qk_b_addr (rw := row) (kk := kk) (byte := 0) hD hbd hrow hk (by omega)
  obtain rfl := Option.some.inj (hl0.symm.trans hloc)
  have al := hp.sharedAlignment
  have rng := Lib.b128_range 0 (((L.sharedBase + 32768 * (b % 3)) / 16 + (2 * (j.val % 4) +
    1024 * (j.val / 4))) * 16 + (128 * (row % 8) + 1024 * (row / 8) + 2 * kk) + 0)
  have jb := j.isLt
  have hσ : σ.val = b % 3 := by
    unfold Iface.InSlot at hs0
    dsimp only at hs0
    have := σ.isLt
    omega
  have used := KV.qk_empty_count hp hX hf words hu base he ⟨j, hj⟩ hb hσ
  rw [hgc] at used
  have hn' : n = b := by
    have := hn.trans used
    omega
  rw [hn'] at hwl hel
  have hcta : cta = c := hc0
  subst hcta
  have est : ((L.sharedBase + 32768 * (b % 3)) / 16 + (2 * (j.val % 4) + 1024 * (j.val / 4))) *
      16 = L.sharedBase + 32768 * σ.val + 32 * (j.val % 4) + 16384 * (j.val / 4) := by omega
  rw [est] at hwl
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := Lib.qk_b_geom al jb hrow hk (by omega) hV hH hhh hx hy
    (by omega) hwl
  exact hgc ▸ hel

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
