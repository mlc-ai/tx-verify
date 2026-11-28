-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.KvElement
public import Kernels.InklingRelDecode.Proof.Lib.MmaPcs
import Kernels.InklingRelDecode.Proof.Protocol.KV.ReadUse
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Lib.KvGeom

@[expose] public section

/-! # The B element of a PV MMA is the value it names

The B operand of step `j` of the PV MMA of ordinal `b` (block `b - 1`) has, at row `r` (the output
column) and column `kk` (the token), the cache element of the V head column `64 (r / 64) + r % 64`
at the token row `16 (j % 4) + kk` of slab half `j / 4` of block `b - 1`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow Protocol Protocol.Shared

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

theorem pv_b_elem (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    {g k pc dst s acc mask ops} (he : X.get (g, k) = some ⟨pc, .tc (.mma dst s acc mask)⟩)
    (hops : X.async.mmaOperands (g, k) = some ops) {j : Fin 8} (hj : pc = Lib.pvIssue j)
    {row kk b : Nat} (hrow : row < 128) (hk : kk < 16)
    (hb : pollRound 2510 ((X.tr g).take k) = b) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row kk =
        .ok (kvElem Q L (g / L.block) (b - 1) 1 (j.val / 4) (row / 64) (row % 64)
          (16 * (j.val % 4) + kk)) := by
  obtain ⟨b', -, hp', h1, -⟩ := Mma.Export.pv_block hp hX hf base he ⟨j, hj⟩
  have eb : b = b' := by omega
  subst eb
  obtain ⟨b3, p3, hbd⟩ := Mma.Export.pv_desc hp hX hf base he ⟨j, hj⟩
  have e3 : b = b3 := by omega
  subst e3
  obtain ⟨-, -, -, b2, hd⟩ := Mma.Export.columns hp hX hf base he
  have ne : ∀ j j' : Fin 8, Lib.pvIssue j ≠ Lib.qkIssue j' := by decide
  have hD : s.descriptor = Lib.pvDesc := by
    rcases hd with ⟨j', hpc, -⟩ | ⟨j', -, -, -, hd⟩
    · exact absurd (hj.symm.trans hpc) (ne j j')
    · exact hd
  have hdesc := hbd j hj
  obtain ⟨c, σ, n, isV, h, hh, x, y, l0, hcg, hg, hl0, hc0, hs0, hn3, hn, hV, hH, hhh, hx, hy,
    ⟨bar, hwl⟩, hel⟩ := kv_b_fact hp hX hf rows init words hu nub form base he hops hrow hk
  have hgc : g / L.block = c := by
    have := (KV.leader_warp (X := X) (L := L) (m := m) hp hcg (by omega : 7 < 8)).2.1
    rwa [← hg] at this
  obtain ⟨cta, hloc⟩ := Lib.pv_b_addr (rw := row) (kk := kk) (byte := 0) hD hdesc hrow hk
    (by omega)
  obtain rfl := Option.some.inj (hl0.symm.trans hloc)
  have al := hp.sharedAlignment
  have rng := Lib.b128_range 0 (((L.sharedBase + 98304 + 32768 * ((b - 1) % 3)) / 16 +
    128 * j.val) * 16 + (2 * (row % 64) + 16384 * (row / 64) + 128 * kk) + 0)
  have jb := j.isLt
  have hσ : σ.val = (b - 1) % 3 := by
    unfold Iface.InSlot at hs0
    dsimp only at hs0
    have := σ.isLt
    omega
  have used := KV.pv_empty_count hp hX hf words hu base he ⟨j, hj⟩ hb hσ
  rw [hgc] at used
  have hn' : n = b - 1 := by
    have := hn.trans used
    omega
  rw [hn'] at hwl hel
  have hcta : cta = c := hc0
  subst hcta
  have est : ((L.sharedBase + 98304 + 32768 * ((b - 1) % 3)) / 16 + 128 * j.val) * 16 =
      L.sharedBase + 98304 + 32768 * σ.val + 2048 * j.val := by omega
  rw [est] at hwl
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := Lib.pv_b_geom al jb hrow hk (by omega) hV hH hhh hx hy
    (by omega) hwl
  exact hgc ▸ hel

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
