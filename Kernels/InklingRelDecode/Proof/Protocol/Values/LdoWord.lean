-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.Results
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteStore
import Kernels.InklingRelDecode.Proof.Protocol.Values.LdsWord
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # The words an accumulator load returns are numbers

The cells of the load of pc 2260 are written by PV MMAs and by the rescale store of earlier rounds
(a probability store writes the score columns). The MMAs before the load have numbers as results,
given the elements they read, and the stored words are numbers by hypothesis: both are claims
about events with a tcgen05 path to the load. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every word an accumulator load returns is a single-precision number**, given the elements
the MMAs before it read and the words of the rescale stores before it. -/
public theorem ld_o_word (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    (hmd : Tmem.AccessCp.AsyncDoneDealloc L X) {t k0 pc a vals sh j}
    (he : X.get (t, k0) = some ⟨pc, .tc (.ld a vals sh)⟩) (hpc : pc = 2260 ∨ pc = 2607)
    (hj : j < vals.length)
    (E : Elements (fun i => Relation.TransGen (TcStep L X) i (t, k0)) L X)
    (hW : ∀ src, Relation.TransGen (TcStep L X) src (t, k0) → ∀ {a vals sh},
      X.get src = some ⟨2328, .tc (.st a vals sh)⟩ → ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r) :
    ∃ r : ℝ, vals[j]? = some (.float .f32 r) := by
  have closed : ∀ i j cell, Relation.TransGen (TcStep L X) i (t, k0) → X.MmaReadCell i cell →
      X.MmaCell j cell → WriteBefore L X j i → Relation.TransGen (TcStep L X) j (t, k0) :=
    fun _ _ _ h _ _ hwb => hwb.tcStep.trans h
  have hl : LoadCell L X (t, k0) j (tcDataCell L t sh a j) := ⟨a, vals, sh, ⟨pc, he⟩, hj, rfl⟩
  obtain ⟨kk, -, -, -, -, -, cellEq⟩ := ld_o_cell hp hX hf base he hpc hj
  have hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask → X.MmaCell i (tcDataCell L t sh a j) →
      WriteBefore L X i (t, k0) → CompletedValues L Assumptions.all X i := by
    intro i d s acc mask hi hmc hwb hdi c ⟨d2, s2, a2, m2, r2, c2, hi2, hp2⟩
    obtain ⟨g, k⟩ := i
    obtain ⟨r, hr⟩ := results hp hX hf hu safe base rows init hG hws ht hmd E closed k g d2 s2 a2
      m2 r2 c2 c hwb.tcStep hi2 hp2 hdi
    exact ⟨_, hr⟩
  obtain ⟨src, value, hrs, hw, hdone⟩ :=
    ld_source_done hp hX hf hu safe base rows init hG hws ht hCV hl
  obtain ⟨hne, -, hwb, -, -⟩ := readSource_ld.mp hrs
  rcases hw with hres | hst | hcp | hsh
  · obtain ⟨r, hv⟩ := result_float hp hX hf base hG E closed hres hwb.tcStep
      (hdone (result_cell hres))
    subst hv
    exact ⟨r, LoadReadOk.f32 hX.tcRead.1 ⟨pc, he⟩ hl hrs (.inl hres)⟩
  · obtain ⟨a', vals', sh', j', ⟨pc, hst⟩, hj', hc'⟩ := hst
    have hlen : j' < vals'.length := (List.getElem?_eq_some_iff.mp hj').1
    have hsc : StoreCell L X src (tcDataCell L t sh a j) :=
      ⟨a', vals', sh', j', ⟨pc, hst⟩, hlen, hc'⟩
    obtain ⟨-, -, h1 | h2⟩ := st_write_cell hp hX hf base hsc
    · exfalso
      obtain ⟨a1, vals1, ba, w1, j1, hy, ha, hba, hj1, hc1⟩ := h1
      obtain ⟨c1, c2, -⟩ := p_cols (L := L) (g := src.1) (w := w1) hba hj1
      rw [← ha, ← hc1, cellEq] at c1 c2
      dsimp only at c1 c2
      split_ifs at c1 c2 <;> omega
    · obtain ⟨a2, vals2, w2, j2, g2, -⟩ := h2
      obtain rfl : pc = 2328 := (Event.mk.inj (Option.some.inj (hst.symm.trans g2))).1
      obtain ⟨r, hr⟩ := hW src hwb.tcStep hst _ (List.mem_of_getElem? hj')
      rw [hr] at hj'
      exact ⟨r, LoadReadOk.f32 hX.tcRead.1 ⟨pc, he⟩ hl hrs
        (.inr (.inl ⟨a', vals', sh', j', ⟨2328, hst⟩, hj', hc'⟩))⟩
  · obtain ⟨c, _, _, _, _, _, _, hp', -⟩ := hcp
    exact (Lib.no_cp hX _ _ hp').elim
  · obtain ⟨_, _, ⟨⟨sp, hp', -⟩, -⟩, -⟩ := hsh
    exact (Tmem.no_shift hX _ _ hp').elim

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
