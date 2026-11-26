-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.EpiPe

@[expose] public section

/-! # The epilogue's stores with the peer's row sum read off the trace

`w0_ost2_value` and `w0_lse_value` take the peer's row-sum word as a number `p` that the block in
progress holds (`w0EpiPe`), at least zero, and (for the staging stores) zero when the true maximum
is `-inf` (`hrp`). Here the word is read off the trace: the lane's load at pc 1157 (`kp`) returned
a word that reads as `w0ESum rP lP` (`lP` at least zero) and the finished blocks of the lane carry
the maximum `rP` (the partner's, `rmax_carry_eq`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem w0ESum_nonneg {r : EReal} {l : ℝ} (h : 0 ≤ l) : 0 ≤ w0ESum r l := by
  unfold w0ESum
  split_ifs <;> simp [h]

theorem w0ESum_bot {l : ℝ} : w0ESum ⊥ l = 0 := by simp [w0ESum]

open Wg0 Wg0.Data in
/-- **The staging stores** with the peer's row sum read off the trace (`w0_ost2_value`, no
`hp0`, no `hrp`). -/
theorem w0_ost2_value_free (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hvt : W0Trace P X g)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Fin 4} {j : Fin 8}
    (hpc : e.pc = ost2Base c + j.val) {sk : EReal} {O : Nat → ℝ}
    (hsk : Rd (w0SkWord ((X.tr g).take k)) sk)
    (hlen : (w0EpiO (w0Scan ((X.tr g).take k)).2).length = 64)
    (hO : ∀ i < 64, Rd ((w0EpiO (w0Scan ((X.tr g).take k)).2).getD i (.pred false)) (O i))
    {kp : Nat} {f : Event} {a' : Acc} {bs' : List (Option Byte)}
    (hf : X.get (g, kp) = some f) (hf1157 : f.pc = 1157) (hfk : f.kind = .rd a' bs')
    (hkp : kp < k)
    (hfirst : ∀ q, kp < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122)
    {rP : EReal} {lP : ℝ} (hl : 0 ≤ lP)
    (hrd : Rd ((rebuild 3 bs').toOption.getD (.pred false)) ((w0ESum rP lP : ℝ) : EReal))
    (hcar : w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 = rP) :
    ∀ a bs, e.kind = .wr a bs → ∃ q < 4, a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
        (65536 + 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) +
          16 * (j.val ^^^ tidOf L g % 8) + MemRow.wg0OutOff c.val + 4 * q) ∧
      bs = (Assumptions.bf16Pair
      (O (2 * (4 * j.val + q)) * w0EpiF P.scale ((X.tr g).take k) (w0ESum rP lP) sk)
      (O (2 * (4 * j.val + q) + 1) *
        w0EpiF P.scale ((X.tr g).take k) (w0ESum rP lP) sk)).toBytes := by
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hpe, -⟩ := w0_epiPe_fin hp hX hFw hw hvt hf hf1157 hfk hkp hKl hfirst
  exact w0_ost2_value hp hX hFw hw he hpc (hvt.take k) (by rw [hpe]; exact hrd)
    (w0ESum_nonneg hl) hsk (fun h => by rw [hcar] at h; rw [h]; exact w0ESum_bot) hlen hO

open Wg0 Wg0.Data in
/-- **The log-sum-exp store** with the peer's row sum read off the trace (`w0_lse_value`). -/
theorem w0_lse_value_free (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hvt : W0Trace P X g)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) (hpc : e.pc = 1178)
    {kp : Nat} {f : Event} {a' : Acc} {bs' : List (Option Byte)}
    (hf : X.get (g, kp) = some f) (hf1157 : f.pc = 1157) (hfk : f.kind = .rd a' bs')
    (hkp : kp < k)
    (hfirst : ∀ q, kp < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122)
    {rP : EReal} {lP : ℝ} (hl : 0 ≤ lP)
    (hrd : Rd ((rebuild 3 bs').toOption.getD (.pred false)) ((w0ESum rP lP : ℝ) : EReal)) :
    ∀ a bs, e.kind = .wr a bs →
      bs = (w0EpiLse P.scale ((X.tr g).take k) (w0ESum rP lP)).toBytes := by
  have hKl : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hpe, -⟩ := w0_epiPe_fin hp hX hFw hw hvt hf hf1157 hfk hkp hKl hfirst
  exact w0_lse_value hp hX hFw hw he hpc (hvt.take k) (by rw [hpe]; exact hrd)
    (w0ESum_nonneg hl)

/-- **The finished blocks at a later event**: no closing event between the row-sum read (index
`kp`, pc 1157) and the event at `k`, so the blocks finished at `k` are those at the read. -/
theorem w0_fin_epi (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) (hvt : W0Trace P X g)
    {kp k : Nat} {f : Event} {a' : Acc} {bs' : List (Option Byte)}
    (hf : X.get (g, kp) = some f) (hf1157 : f.pc = 1157) (hfk : f.kind = .rd a' bs')
    (hkp : kp < k) (hKl : k < (X.tr g).length)
    (hfirst : ∀ q, kp < q → q < k → ∀ ev, X.get (g, q) = some ev → ev.pc ≠ 1122) :
    (w0Fin ((X.tr g).take k)).1 = (w0Fin ((X.tr g).take kp)).1 :=
  (w0_epiPe_fin hp hX hFw hw hvt hf hf1157 hfk hkp hKl hfirst).2

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
