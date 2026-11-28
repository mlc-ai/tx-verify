-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.RefWords
import Kernels.InklingRelDecode.Proof.Prologue.QueryInput
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # Which query rows load

Once the two request words are read, the length register is the length of the request, and a row
group is on exactly when its row is a row of the tile and its token a valid token. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Proof PTX.Flow Arith32 Control

/-- **The length register** after the request words are read. -/
theorem qlen_known {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) {d : Control.D} {r : Nat}
    (hr : r < Q.b) (known : Known Q r d) (late : 37 < d.site.pc) : qlen d = W (Q.qLen r) := by
  have first := known.first (by omega)
  have last := known.last late
  have mono := hp.cuMono r hr
  have fine := Lib.qStart_mono hp (r := r + 1) (r' := Q.b) (by omega) le_rfl
  have := hp.cuEnd
  have := hp.nTokRange
  exact qlen_word first last mono (by omega)

/-- **A row group is on** exactly when it loads. -/
theorem queryOn_iff {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) {d : Control.D}
    {tid gp r : Nat} (hr : r < Q.b) (hgp : gp < 4) (hq : qlen d = W (Q.qLen r)) :
    queryOn tid gp d = true ↔
      tid / 8 % 16 + 16 * gp < 60 ∧ (tid / 8 % 16 + 16 * gp) / 6 < Q.qLen r := by
  have tokle : qTok tid gp ≤ 10 := by unfold qTok qRow; omega
  have qle := hp.qLenLe r hr
  have eq : BitVec.ofNat 64 ((tid / 8 % 16 + 16 * gp) * 10923 / 65536) = W (qTok tid gp) := rfl
  unfold queryOn
  dsimp only
  rw [hq, eq, scmp_gt_W (by omega) (by omega)]
  simp [qTok_eq _ _ hgp]

end PTX.Kernels.InklingRelDecode.Proof.Prologue
