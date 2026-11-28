-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.WriteOrder
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.StoreMma
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PstDone
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BlockCounts
public import Kernels.InklingRelDecode.Proof.Lib.BcastWord
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LastBar
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits
import Lemmas.Kernel.Frame
import Lemmas.Kernel.Safety.TableU
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.PeerBar
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section

/-! # A QK MMA and a probability store of one score buffer are ordered, by the rounds

The QK MMA of block `b` and the probability store of round `r` with `b % 2 = r % 2` (the same
buffer): if `b / 2 ≤ r / 2` the store's thread's round polled the score slot, and lane zero's poll
of the round (before the round's rendezvous, which the store follows) observes a commit of
the slot after the MMA; otherwise the MMA lane's poll of the probability slot observes the
publication that follows the store. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow PTX.MbarRing PTX.TcMma Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The address of a probability store of round `r`**: the buffer `r % 2`. -/
theorem pst_address {a vals sh r w c} {L : Launch}
    (sta : tcStatic (.st a vals sh) = Lib.opStatic L c 1009 r w) : a % 2^21 = r%2*128 := by
  simp only [tcStatic,Lib.opStatic,Lib.bcastOffset] at sta
  simp at sta
  obtain ⟨rfl,-⟩ := sta
  omega

/-- **A QK MMA and a probability store of one buffer are ordered, by the rounds**: the MMA of
block `b` is done before the store of round `r` if `b / 2 ≤ r / 2`, and the store is done before the
MMA otherwise. -/
theorem qk_store_round (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    {x y : EvId} {pc d a : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat}
    {vals : List Value} {sh : TcShape}
    (hx : X.get x = some ⟨pc, .tc (.mma d s acc mask)⟩) (qk : ∃ j : Fin 8, pc = Lib.qkIssue j)
    (hy : X.get y = some ⟨1009, .tc (.st a vals sh)⟩) (cta : x.1 / L.block = y.1 / L.block)
    (hd : d = a % 2 ^ 21) :
    ∃ b r, pollRound 2462 ((X.tr x.1).take x.2) = b + 1 ∧
      pollRound 1257 ((X.tr y.1).take y.2) = r + 1 ∧ b % 2 = r % 2 ∧
      ((b / 2 ≤ r / 2 ∧ DoneBefore L X x y) ∨ (r / 2 < b / 2 ∧ StoreDoneBefore L X y x)) := by
  obtain ⟨g,k⟩ := x
  obtain ⟨t,sk⟩ := y
  simp only at cta
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have hg := Frame.lt_of_get hX hx
  obtain ⟨b,hdb,q1,q2,warp,-⟩ := Mma.Export.qk_block hp hX hf base hx qk
  have qkl : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498] := by
    obtain ⟨j,rfl⟩ := qk
    fin_cases j <;> decide
  obtain ⟨lead,-⟩ := mma_leader hp hX hf hx
  simp only at lead warp
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : g/L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 hg
  have hz : g/L.block*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : g/L.block*L.block/L.block = g/L.block := by simp [hp.block]
  have lp : g/L.block*L.block%L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have lt := Export.tc_data_lane hp hX hf hy (by rfl)
  have tc : isTcColl ⟨1009,.tc (.st a vals sh)⟩ = true := rfl
  obtain ⟨r,w,s1,-,s3,sta⟩ := Export.st_round hp hX hf base hy tc (.inl rfl)
  have haddr := pst_address sta
  have par : b%2 = r%2 := by omega
  have lent : sk < (X.tr t).length := (List.getElem?_eq_some_iff.mp hy).1
  rcases Nat.lt_or_ge (r/2) (b/2) with big | small
  · refine ⟨b, r, q1, s1, par, .inr ⟨big, ?_⟩⟩
    have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hx).1
    have cnt := Protocol.Scalar.count rows hg (Object.prob (MbarRow.slot2 r)) k
    change okPolls ((Object.prob (MbarRow.slot2 r)).loc L (g/L.block)) ((X.tr g).take k) =
      (Object.prob (MbarRow.slot2 r)).visits (pollRound 2510 ((X.tr g).take k)) at cnt
    rw [q2] at cnt
    have vis : (Object.prob (MbarRow.slot2 r)).visits (b-1) = (b-1+2-1-r%2)/2 := rfl
    have := store_before_mma hp hX hf safe base rows init words hc hy (.inl rfl) lt
      (by rw [cta]) s1 (k := k) (by rw [lead]; exact hk) (by
        rw [lead]; rw [cnt,vis]; omega)
    rw [lead] at this
    exact this
  · refine ⟨b, r, q1, s1, par, .inl ⟨small, ?_⟩⟩
    simp only [ite_true] at s3
    have few := qk_commits_before hp hX hf rows words (c := g/L.block) (s := MbarRow.slot2 r)
      hg hx qkl warp q1 (by show r%2 = b%2; omega)
    exact mma_before_pst hp hX hf safe rows init words hx hy lt cta s1 s3 (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Tmem
