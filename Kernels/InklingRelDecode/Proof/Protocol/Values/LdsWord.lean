-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.QkResults
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdSource
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdCand
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderS
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Values.QkStoreRound
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # The words a score load returns are numbers

The cells of a score load are written by QK MMAs and by the probability store of earlier rounds. The
latest write before the load is a QK MMA: a probability store before the load is of an earlier round
than the load's, and the QK MMA that the load's poll observed is of a later block, written after it.
The QK results are numbers (`qk_float`), so the word the load returns is one. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A derived MMA result is one of a cell the MMA writes. -/
theorem result_cell {i : EvId} {cell : Cell} {v : Value}
    (h : Result L Assumptions.all X i cell v) : X.MmaCell i cell := by
  cases h with
  | overwrite issue position => exact ⟨_, _, _, _, _, _, issue, position⟩
  | accumulate issue position => exact ⟨_, _, _, _, _, _, issue, position⟩
  | accumulateStored issue position => exact ⟨_, _, _, _, _, _, issue, position⟩

/-- **A score load's word is a QK result**: its source and the number the source holds. -/
public theorem ld_s_result (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) {t k0 a vals sh j}
    (he : X.get (t, k0) = some ⟨1265, .tc (.ld a vals sh)⟩) (hj : j < vals.length) :
    ∃ src r, ReadSource L X .ld src (t, k0) (tcDataCell L t sh a j) ∧
      Result L Assumptions.all X src (tcDataCell L t sh a j) (.float .f32 r) ∧
      X.async.mmaDone src = true ∧ vals[j]? = some (.float .f32 r) := by
  have hl : LoadCell L X (t, k0) j (tcDataCell L t sh a j) := ⟨a, vals, sh, ⟨1265, he⟩, hj, rfl⟩
  obtain ⟨rl, hj64, lt, s1, s3, cellEq⟩ := ld_s_cell hp hX hf base he hj
  have qk_of : ∀ i, X.MmaCell i (tcDataCell L t sh a j) → QkIssue X i := by
    intro i hmc
    obtain ⟨pc1, d1, s1', acc1, mask1, he1, -, lo, hi1, -, -, kind⟩ :=
      mma_write_cell hp hX hf base hmc
    rcases kind with ⟨jq, hq, -⟩ | ⟨jp, -, hd1, -⟩
    · exact ⟨pc1, d1, s1', acc1, mask1, he1, jq, hq⟩
    · rw [cellEq] at lo hi1
      dsimp only at lo hi1
      split_ifs at lo hi1 <;> omega
  have hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask → X.MmaCell i (tcDataCell L t sh a j) →
      WriteBefore L X i (t, k0) → CompletedValues L Assumptions.all X i := by
    intro i d s acc mask hi hmc hwb hdi c ⟨d2, s2, a2, m2, r2, c2, hi2, hp2⟩
    obtain ⟨g, k⟩ := i
    obtain ⟨r, hr⟩ := qk_results hp hX hf hu safe base rows init hG hws ht
      hmd words nub form k g d2 s2 a2 m2 r2 c2 c
      (qk_of _ hmc) hi2 hp2 hdi
    exact ⟨_, hr⟩
  obtain ⟨src, value, hrs, hw, hdone⟩ :=
    ld_source_done hp hX hf hu safe base rows init hG hws ht hCV hl
  rcases hw with hres | hst | hcp | hsh
  · have hmc := result_cell hres
    obtain ⟨r, hv⟩ := qk_float hp hX hf hu safe base rows init hG words nub form hres
      (qk_of _ hmc) (hdone hmc)
    subst hv
    exact ⟨src, r, hrs, hres, hdone hmc, LoadReadOk.f32 hX.tcRead.1 ⟨1265, he⟩ hl hrs (.inl hres)⟩
  · exfalso
    obtain ⟨a', vals', sh', j', ⟨pc, hst⟩, hj', hc'⟩ := hst
    have hlen : j' < vals'.length := (List.getElem?_eq_some_iff.mp hj').1
    have hsc : StoreCell L X src (tcDataCell L t sh a j) :=
      ⟨a', vals', sh', j', ⟨pc, hst⟩, hlen, hc'⟩
    obtain ⟨-, -, h1 | h2⟩ := st_write_cell hp hX hf base hsc
    swap
    · obtain ⟨a2, vals2, w2, j2, g2, ha, hj2, hc2⟩ := h2
      have := (o_cols (L := L) (g := src.1) (w := w2) hj2).1
      rw [← ha, ← hc2, cellEq] at this
      dsimp only at this
      split_ifs at this <;> omega
    obtain ⟨a1, vals1, ba, w1, j1, hy, ha, hba, hj1, hc1⟩ := h1
    obtain ⟨r1, r2, s1', s2', par, ord⟩ := ld_s_pst hp hX hf safe base he hj hsc
    obtain ⟨hne, -, hwb, hstab, -⟩ := readSource_ld.mp hrs
    rcases ord with ⟨early, -⟩ | ⟨late, hrb⟩
    swap
    · exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep hrb hne).trans hwb.tcStep)
    obtain ⟨w, hw0, hwb0, rc, b, s1c, cnt, parb, dst, sc, acc, mask, gw, q1⟩ :=
      ld_s_cand hp hX hf hu safe base rows init he hj 0
    have hrc : rc = r1 := by omega
    subst hrc
    have hwe : w ≠ (t, k0) := fun h => by rw [h, he] at gw; cases gw
    rcases hstab w hw0 with heq | hws0 | hrb0
    · rw [heq, hy] at gw
      have := (Event.mk.inj (Option.some.inj gw)).1
      exact absurd this.symm (by decide : Lib.qkIssue 0 ≠ 1009)
    · rcases tmemWrite_of_no_copy (Lib.no_cp hX) (Tmem.no_shift hX) hw0 with hm | hs'
      swap
      · obtain ⟨ax, vx, shx, jx, ⟨pcx, hx⟩, -⟩ := hs'
        rw [hx] at gw
        cases gw
      obtain ⟨pc1, d1, s1'', acc1, mask1, he1, cw, lo, hi1, -, -, kind⟩ :=
        mma_write_cell hp hX hf base hm
      have he0 := he1.symm.trans gw
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he0
      obtain ⟨-, rfl, -, -, -⟩ := he0
      obtain ⟨c1, c2, c3⟩ := p_cols (L := L) (g := src.1) (w := w1) hba hj1
      rw [← ha, ← hc1] at c1 c2 c3
      rcases kind with ⟨jq, -, hd1, -⟩ | ⟨jp, -, hd1, -⟩
      swap
      · omega
      have hmod : (ba + w1 * 2 ^ 21) % 2 ^ 21 = ba := by omega
      obtain ⟨b', r'', q1', s2'', -, o⟩ := qk_store_round hp hX hf safe base rows init
        (x := w) (y := src) gw ⟨0, rfl⟩ hy
        (cw.symm.trans c3) (by rw [ha, hmod]; omega)
      rcases o with ⟨h1', -⟩ | ⟨-, sd⟩
      · omega
      · exact tcStep_acyclic hX hG _ (sd.tcStep.trans hws0.tcStep)
    · have hrb1 : ReadBefore L X .ld (t, k0) w := hrb0
      exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep hrb1 hwe).trans hwb0.tcStep)
  · obtain ⟨c, _, _, _, _, _, _, hp', -⟩ := hcp
    exact (Lib.no_cp hX _ _ hp').elim
  · obtain ⟨_, _, ⟨⟨sp, hp', -⟩, -⟩, -⟩ := hsh
    exact (Tmem.no_shift hX _ _ hp').elim

/-- **Every word a score load returns is a single-precision number.** -/
public theorem ld_s_word (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) {t k0 a vals sh j}
    (he : X.get (t, k0) = some ⟨1265, .tc (.ld a vals sh)⟩) (hj : j < vals.length) :
    ∃ r : ℝ, vals[j]? = some (.float .f32 r) :=
  let ⟨_, r, _, _, _, h⟩ := ld_s_result hp hX hf hu safe base rows init hG hws ht hmd words nub form
    he hj
  ⟨r, h⟩

/-- **Every word a score load returns is a typed number** (`SK.fl`). -/
public theorem ld_s_fl (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) (words : RoleBytes L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) (form : Iface.KvCopyForm Q L X) {t k0 a vals sh}
    (he : X.get (t, k0) = some ⟨1265, .tc (.ld a vals sh)⟩) : ∀ x ∈ vals, Flow.SK.fl.Has x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨r, hr⟩ := ld_s_word hp hX hf hu safe base rows init hG hws ht hmd words nub form he hj
  rw [List.getElem?_eq_getElem hj] at hr
  rw [Option.some.inj hr]
  exact Flow.has_float_fl r

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
