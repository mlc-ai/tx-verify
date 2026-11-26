-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Source.Main
public import Kernels.FlashKdaFwd.Proof.Protocol.ReadBack
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract

@[expose] public section

/-! # The content theorems fit their consumers

`Main.lean: stage_content` and `init_content` are stated in the shape of the hypotheses `hsb`
and `hic` of the read-back theorems of the protocol layer (`Proof/Protocol/ReadBack.lean`). This
file applies those theorems to them, so the fit is checked by the compiler, and it states the
results in the shape the value layer asks for:

* `readBack_stage`: the statement of the field `stage` of `Values.ReadBack`
  (`Proof/Values/Contract.lean`), word for word: a read by a compute thread of bytes of the input
  stage of tile `b`, after `b / 3 + 1` successful polls of the stage's "full" mbarrier, returns
  the bytes `Values.stageByte P mem0 seq head b`.
* `initContent`: `Values.Ends.InitContent P L X c` for every block `c`
  (`Proof/Values/Ends/Contract.lean`): the definition is the conclusion of `init_content`.
* `earlyRead_init`: `Values.Ends.EarlyRead P L X`, by the value layer's own `earlyRead`: a read
  of bytes of the FP32 state buffer with at most five `bar.sync 0` before it returns the bytes
  `Values.Ends.initBuf P L c`.

Their hypotheses are the contracts of the protocol layer (`UnionFacts`, `LifeFacts`,
`LoadFacts`, `StoreFacts`, `StateFacts`, `InitFacts`, `BarFacts`, `NoEvents`, `SyncGuarded`),
the precondition, consistency, and the three hypotheses of this directory (`TileIssues` or
`StateIssues`, and `WriteFrame`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
open PTX PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Proof.Values (stageByte)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {T : Nat → Nat} {O : Owners}

/-- **The field `stage` of `Values.ReadBack`**: a read by a compute thread `g` of bytes at
offset `o` of the input stage of tile `b`, after `b / 3 + 1` successful polls of the stage's
"full" mbarrier and outside the 64-byte hole, returns the bytes the tile's loads wrote. -/
theorem readBack_stage (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hT : TileIssues P L X) (hW : WriteFrame P X) (U : UnionFacts L X T O)
    (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents kernel X)
    (hg : SyncGuarded L kernel X) :
    ∀ g k pc a bs b o, g < L.threads → g % L.block < 128 →
      X.get (g, k) = some ⟨pc, .rd a bs⟩ →
      okPolls (Values.fullBar L g b) ((X.tr g).take k) = b / 3 + 1 →
      a.loc = ⟨.shared, g / L.block, P.sharedBase + (32768 + 18048 * (b % 3) + o)⟩ →
      (o + a.size ≤ 4160 ∨ (4224 ≤ o ∧ o + a.size ≤ 18048)) →
      bs = (List.range a.size).map fun i =>
        stageByte P mem0 (Values.seqOf P L g) (Values.headOf P L g) b (o + i) := by
  intro g k pc a bs b o hgl hga hrd hpolls hloc hfree
  have hb := hpre.block
  have hc : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hgl
  have hthr : computeThread L (g / L.block) ⟨g % L.block, hga⟩ = g := by
    unfold computeThread thr
    exact Nat.div_add_mod' g L.block
  have hrd' : X.get (computeThread L (g / L.block) ⟨g % L.block, hga⟩, k) =
      some ⟨pc, .rd a bs⟩ := by rw [hthr]; exact hrd
  have e : 3 * (b / 3) + b % 3 = b := by omega
  have h := U.stage_read hF hLd hSt hS hI hB hN hX hb hg hc hrd'
    ⟨b % 3, Nat.mod_lt _ (by decide)⟩ (b / 3) o _ (by rw [hthr]; exact hpolls)
    (by rw [hloc, hpre.sharedBase]) hfree
    (stage_content hpre hX hT hW (g / L.block) ⟨b % 3, Nat.mod_lt _ (by decide)⟩ (b / 3))
  simpa only [e, Values.seqOf, Values.headOf] using h

/-- **`Values.Ends.InitContent`** for every block: the content of the sixteen loads of the
initial state, in the value layer's own definition. -/
theorem initContent (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hSI : StateIssues P L X) (hW : WriteFrame P X) : ∀ c, Values.Ends.InitContent P L X c :=
  fun c => init_content hpre hX hSI hW c

/-- **`Values.Ends.EarlyRead P L X`**: a read, with at most five `bar.sync 0` before it, of
bytes at offset `o` of the FP32 state buffer of the reading thread's block returns the bytes
the sixteen loads of the initial state wrote (`Values.Ends.earlyRead` on `initContent`). -/
theorem earlyRead_init (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hSI : StateIssues P L X) (hW : WriteFrame P X) (U : UnionFacts L X T O)
    (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents kernel X)
    (hg : SyncGuarded L kernel X) : Values.Ends.EarlyRead P L X :=
  Values.Ends.earlyRead U hF hLd hSt hS hI hB hN hX hpre.block hg (initContent hpre hX hSI hW)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Source
