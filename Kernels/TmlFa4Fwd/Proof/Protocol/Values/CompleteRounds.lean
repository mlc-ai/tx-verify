-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.LinksAll
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatLast
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Correction.Export.RescaleBallot
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Lemmas.Kernel.FrameEnd

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h : Nat} {t : Tile}

/-- A softmax lane assigned a tile in a complete execution reaches its final named arrival.
The arrival's ordinal is the number of blocks of that tile. -/
theorem complete_soft_arrival (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow p L X) (hC : Complete L X) (hh : h < L.threads)
    (hw : Prologue.warpIndex L h < 8) (ht : tileOf p L (h/L.block) = some t) :
    SoftRounds p L h t.n ∧ ∃ i pc, X.get (h,i) =
      some ⟨pc,.bar (Prologue.warpIndex L h + 3) (some 64) .arrive⟩ ∧
      barOrd X h i (Prologue.warpIndex L h + 3) = t.n := by
  have exits {g : Nat} (hg : g < L.threads) : ∃ k pc, X.get (g,k) = some ⟨pc,.exit⟩ := by
    obtain ⟨k,pc,_,he⟩ := Frame.Complete.exit_last hC hg (by
      rintro ⟨_,_,hc⟩
      obtain ⟨_,_,_,_,hi,_⟩ := hX.clc.canceled_has_issue hc
      exact noClcIssue hX hi)
    exact ⟨k,pc,he⟩
  obtain ⟨hc,b,hW,_⟩ := tileOf_some ht
  let y := h/L.block * L.block + 256
  have cta : y/L.block = h/L.block := by simp only [y,hp.block]; omega
  have hy : y < L.threads := by
    have := Nat.mul_le_mul_right 512 (Nat.succ_le_of_lt hc)
    simp only [hp.block] at this
    simp only [Launch.threads,y,hp.block]
    omega
  have wy : Prologue.warpIndex L y = 8 := by simp only [Prologue.warpIndex,y,hp.block]; omega
  obtain ⟨k,pc,he⟩ := exits hy
  obtain ⟨R,hr,_⟩ := Correction.corr_exit_ballots hp hX hf (noUb_of_complete hX hC)
    (by omega : 8 ≤ Prologue.warpIndex L y) (by omega) hW.1 (by rw [cta]; exact hW.2.2) he
  obtain ⟨t',ht',hn⟩ := tile_rounds hp hy (hr.mma hp hy)
  rw [cta,ht] at ht'
  cases ht'
  obtain ⟨x,px,hx⟩ := exits hh
  have pick : ∃ r bal, Epilogue.Picked p L h r bal := by
    obtain ⟨r,bal,hp',_⟩ := hr
    exact ⟨r,bal,by simpa only [Epilogue.Picked,cta] using hp'⟩
  have hN := (soft_exit_rounds hp hX hf hw pick hx).1
  have eq := hN.corr hp hy cta.symm hr
  rw [eq,← hn] at hN
  have count := soft_exit_count hp hX hf hw hx hy cta.symm hr
  obtain ⟨i,pi,cnt,md,_,hi,ord⟩ := exists_bar (X := X) (g := h) (x := x)
    (id := Prologue.warpIndex L h + 3) (c := t.n) (by omega)
  rcases soft_bar hp hX hf hw hi with ⟨bad,_⟩ | ⟨bad,_⟩ | ⟨bad,_,_⟩ | ⟨_,rfl,rfl,_⟩
  · omega
  · omega
  · rcases bad with h | h <;> omega
  · exact ⟨hN,i,pi,hi,ord⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Values
