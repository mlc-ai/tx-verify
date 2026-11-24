-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputBytes
public import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Ordered
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.InputBar
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Q.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every Q operand byte has a visible write

`q_visible`: a byte of the Q stage a QK MMA reads is written by the stage's copy into its box, which
has completed and precedes the read. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {gm k : Nat}

/-- **A Q operand byte has a visible write.** -/
theorem q_visible (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hIn : InputsUnwritten p X) {st u idx off : Nat} {j : Fin 8}
    (hR : Tm.Qk L X gm k st u j) (hst : st < 2) (ho : off < 32768)
    (hr : AsyncCovers X (gm, k) (.mmaRead false idx)
      ⟨.shared, gm / L.block, L.sharedBase + 3072 + 32768 * st + off⟩) :
    ∃ w a bs, X.MemWrites w a bs ∧
      a.Covers ⟨.shared, gm / L.block, L.sharedBase + 3072 + 32768 * st + off⟩ ∧
      modelCausality L X ⟨.shared, gm / L.block, L.sharedBase + 3072 + 32768 * st + off⟩ w
        (.async (gm, k) (.mmaRead false idx)) := by
  obtain ⟨pcm, da, db, hme⟩ := hR.issue
  have hgm := Frame.lt_of_get hX hme
  have hmma : X.MmaIssue (gm, k) (128 * st) _ _ _ := ⟨pcm, hme⟩
  have hwm := (Tm.mma_qkpv hp hX hFw ⟨_, _, _, _, hmma⟩).1
  obtain ⟨cm, hin, -, hcm, hfull, -⟩ := qHandoff hp hX hFw (tmaBytes hp hX hFw) gm hgm ⟨st, hst⟩
  have hcme : gm = cm := hcm hmma ⟨hgm, rfl, hwm⟩
  subst hcme
  have hpoll : 0 + 1 ≤ okPolls (qF L gm ⟨st, hst⟩) ((X.tr gm).take k) := by
    show 1 ≤ okPolls (obj L gm (8 * st)) _
    rw [show obj L gm (8 * st) = Tm.bar L (gm / L.block) (8 * st) from rfl, hR.q]
  obtain ⟨jw, pcw, par, acq, sc, hjk, hwe, hwo⟩ := nth_poll hpoll
  obtain ⟨q, hq⟩ : ∃ q : Fin 2, q.val = off / 16384 := ⟨⟨off / 16384, by omega⟩, rfl⟩
  obtain ⟨i, pci, al, sp, he, hm, hc, -, hW⟩ := hfull hwe hwo q
  obtain ⟨o, hot, hn⟩ := Life.observed_load hX hW
  obtain ⟨⟨addr, pco, hio⟩, -⟩ := hX.tensor _ o hot
  have hos : o.spec = sp := by
    rw [he] at hio
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at hio
    exact hio.2.2.symm
  obtain ⟨hyc, hyw⟩ := tmaLane_in (X := X) hp gm
  have hm' : sp.mbar = obj L (tmaLane L X gm) (8 * st) := by rw [obj_cta hyc]; exact hm
  obtain ⟨-, -, jw', pcw', maskw, instw, -, hjw⟩ :=
    ld_tma_copy hp hX hFw (.inl hyw) (q_tmaOff ⟨st, hst⟩) he hm'
  obtain ⟨j', org', hs', hoff'⟩ := ld_q_copy hp hX hFw (.inl hyw)
    (fun k pc mask inst ld hk => tmaLane_won hX hjw hk) ⟨st, hst⟩ he hm'
  simp only at hoff'
  rw [obj_cta hyc, show obj L gm (8 * st) = qF L gm ⟨st, hst⟩ from rfl, hc] at hoff'
  have hoff2 : (Loader.inputSite j').sharedOffset = 3072 + 32768 * st + 16384 * q.val := by
    have := q.isLt
    omega
  rw [hyc] at hs'
  obtain ⟨x, y, hwl, -, -⟩ := input_box_byte (p := p) (L := L) (j := j') (org := org')
    (mb := sp.mbar) (c := gm / L.block)
    (l := ⟨.shared, gm / L.block, L.sharedBase + 3072 + 32768 * st + off⟩) rfl rfl
    (by rw [hoff2]; simp only; omega) (by rw [hoff2]; simp only; omega)
  rw [← hs'] at hwl
  have hw := input_written hp hX hIn hot hn (c := gm / L.block) (j := j') (org := org')
    (mb := sp.mbar) (by rw [hos]; exact hs') (by rw [hos]; exact hwl)
  refine ⟨_, _, _, hw, ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩, ?_⟩
  exact q_copy_read hp hX hFw he hwl hR hst hr rfl (by simp only; omega) (by simp only; omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof
