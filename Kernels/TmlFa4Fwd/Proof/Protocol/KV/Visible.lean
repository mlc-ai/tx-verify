-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Order
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Rows
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Bound
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Lifetime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every K/V operand byte has a visible write

`kv_visible`: a byte of the slot an MMA reads is written by a row copy of its packet, which has
written and precedes the read. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem rowCol_surj : ∀ c < 64, ∃ t < 64, Loader.rowCol t = c := by decide +kernel

/-- **A K/V operand byte has a visible write.** -/
theorem kv_visible (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {t idx off : Nat} (hR : KvRead L X g k t) (ho : off < 32768)
    (hcb : AsyncCovers X (g, k) (.mmaRead true idx)
      ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (t % 3) + off⟩) :
    ∃ w a bs, X.MemWrites w a bs ∧
      a.Covers ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (t % 3) + off⟩ ∧
      modelCausality L X ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (t % 3) + off⟩ w
        (.async (g, k) (.mmaRead true idx)) := by
  have hb := hp.block
  have h3 := Nat.mod_lt t (show 0 < 3 by decide)
  obtain ⟨hin, hpoll, -⟩ := hR.slot hp hX hFw
  obtain ⟨-, -, d, s, acc, mask, hi⟩ := hR.use
  obtain ⟨c, hc, -, hcm, hfull, -⟩ := kvHandoff hp hX hFw g hin.1 ⟨t % 3, h3⟩
  obtain rfl := hcm hi hin
  obtain ⟨j, pcj, par, acq, sc, hjk, hje, hjn⟩ := nth_poll hpoll
  -- the lane and the copy that cover the byte
  obtain ⟨t0, ht0, hcol⟩ := rowCol_surj (off % 1024 / 16) (by omega)
  obtain ⟨i, pci, hie, hin', harr, -⟩ := hfull hje hjn ⟨t0, ht0⟩
  have hyc : ldProd L g ⟨t0, ht0⟩ / L.block = g / L.block := by simp only [ldProd, hb]; omega
  have hyw : Prologue.warpIndex L (ldProd L g ⟨t0, ht0⟩) = 14 ∨
      Prologue.warpIndex L (ldProd L g ⟨t0, ht0⟩) = 15 := by
    simp only [Prologue.warpIndex, ldProd, hb]
    have : (g / 512 * 512 + 448 + t0) % 512 = 448 + t0 := by omega
    rw [this]; omega
  have hy64 : ldProd L g ⟨t0, ht0⟩ % L.block % 64 = t0 := by
    simp only [ldProd, hb]; omega
  generalize ldProd L g ⟨t0, ht0⟩ = y at hie hin' harr hyc hyw hy64
  have hie' : X.get (y, i) = some ⟨pci, .asyncArrive (obj L y (32 + 8 * (t % 3))) true⟩ := by
    rw [obj_cta hyc]; exact hie
  have hcnt' : ((X.tr y).take i).countP (arriveOnTo (obj L y (32 + 8 * (t % 3)))) = t / 3 := by
    rw [obj_cta hyc]; exact hin'
  have hx32 : 2 * (off % 16384 / 1024) + off / 16384 < 32 := by omega
  obtain ⟨jc, pcc, sp, hjc, hcp, hcnt⟩ := ld_arr_rows hp hX hFw hyw ⟨t % 3, h3⟩ hie' hcnt' hx32
  have htt : 3 * (t / 3) + t % 3 = t := by omega
  simp only [htt] at hcnt
  obtain ⟨-, hC⟩ := copy_row hp hX hFw ⟨_, hcp⟩
  have hpkt : pkt X y jc = t := by unfold pkt; rw [hcnt]; omega
  obtain ⟨i', j', hij, hdst⟩ := hC.dst
  rw [hcnt] at hij
  rw [hpkt] at hdst
  have hii : i'.val = off % 16384 / 1024 ∧ j'.val = off / 16384 := by
    have h1 := i'.isLt
    have h2 := j'.isLt
    have hA : off % 16384 / 1024 < 16 := by omega
    have hC : off / 16384 < 2 := by omega
    generalize off % 16384 / 1024 = A at hij hA ⊢
    generalize off / 16384 = C at hij hC ⊢
    generalize i'.val = a at hij h1 ⊢
    generalize j'.val = b at hij h2 ⊢
    clear * - hij h1 h2 hA hC
    omega
  have hcov : sp.dst.Covers
      ⟨.shared, g / L.block, L.sharedBase + 68608 + 32768 * (t % 3) + off⟩ := by
    rw [hdst]
    refine ⟨rfl, hyc.symm, ?_, ?_⟩ <;> simp only [Loader.cpAddr, hy64, hcol, hii.1, hii.2] <;> omega
  have htr : TracksCpAsync X (y, jc) (y, i) :=
    ⟨rfl, hjc, ⟨sp, ⟨_, hcp⟩, hC.grp⟩, _, true, ⟨_, hie⟩⟩
  obtain ⟨-, -, -, harrOk⟩ := hX.tma
  have hwr : (X.async.copies (y, jc)).writeBytes.isSome := (harrOk (y, i) harr).2 _ htr
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hwr
  have hmw : X.MemWrites (.async (y, jc) (.write .copy)) sp.dst bs :=
    ⟨sp, ⟨_, hcp⟩, hC.whole, rfl, hbs⟩
  exact ⟨_, _, _, hmw, hcov, kv_copy_read hp hX hFw hcp hyw hC hR hyc (by rw [hpkt])
    (by rw [hpkt]) ⟨_, _, Execution.MemWrites.intent hmw, hcov⟩ hcb⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
