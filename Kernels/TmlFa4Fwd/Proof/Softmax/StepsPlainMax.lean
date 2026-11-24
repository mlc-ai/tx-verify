-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.LdWait
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Kernels.TmlFa4Fwd.Proof.Lib.MulEReal
public import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
public import Kernels.TmlFa4Fwd.Proof.Softmax.PlainMaxK
public import Kernels.TmlFa4Fwd.Proof.Softmax.Scales
public import Lemmas.Flow.Step.TcSteps
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # A plain round's maximum after its fourth score load

The implicit wait of a plain round's fourth score load continues into the packs of the loaded
registers and the round's maximum from the maximum before the round (`mxVal`): the fold
(`foldPT`, `foldPF`), the test whether to keep the maximum before the round (`keepP`), the
maximum the exponents subtract and the row sum's rescaling factor (`maxP`, `facP`), up to the
statistics store. The proof runs once for each kind of the maximum before the round (finite or
`-∞`), so that every value the walks read has one form: a walk over the packs of the fourth load
to pc 6747, the generated run of the fold (`maxP_mid`) to the cut pc 6877, and a walk from the
fold's value to the statistics store. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option seg_sym.decideHeartbeats 40000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A segment from facts `F` that also start with a register value the facts give. -/
theorem seg_start_cons {s b r : Nat} {v : Value} {F G : List (Nat × Value)}
    (hr : ∀ R, Holds R F → R r = some v)
    (h : ∃ n, Seg kernel Assumptions.all L g n s ((r, v) :: F) b G) :
    ∃ n, Seg kernel Assumptions.all L g n s F b G := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.weaken_start fun R hR => ⟨hr R hR, hR⟩⟩

/-- The implicit wait of a plain round's fourth score load from the state with values `v`
(an override) and the maximum before the round as the value `X` the walks read: the packs are
walked to pc 6747, the fold is the generated run to pc 6877, where it is stated as its term
(`foldP`, from the table of the statistics store), and the rest is walked from there. -/
syntax "soft_sldw3 " term:max term:max term:max term:max term:max : tactic
macro_rules
  | `(tactic| soft_sldw3 $p $L $g $v $X) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
      refine PTX.Flow.Code.step_tcLdWait (by code_lookup)
        (by ld_wait) (fun _ => rfl)
        rfl rfl ?_
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub => rfl
      case acc => rfl
      case seg =>
        intro _
        site_norm
        refine PTX.Flow.Seg.comp_ex (q := 6747)
          (H := (7255, $X) ::
            PTX.Flow.factsFrom (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.liveCut 6747)
              (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.valueOfD $p $L $g
                (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.D.mk' (.stat true) $v))) ?_ ?_
        · refine PTX.Kernels.TmlFa4Fwd.Proof.Softmax.seg_start_cons (r := 7255) (v := $X)
            (fun R hR => PTX.Proof.holds_mem hR (PTX.Flow.mem_factsFrom (by lit_mem))) ?_
          seg_sym using (soft_seg)
        refine PTX.Flow.Seg.comp_ex (q := 6877)
          (PTX.Kernels.TmlFa4Fwd.Proof.Softmax.maxP_mid $v
            ((PTX.Kernels.TmlFa4Fwd.Proof.Softmax.statP_mx $v).trans rfl)) ?_
        seg_sym using (soft_seg)
      case inv => site_norm; soft_inv))

/-- The implicit wait of a plain round's fourth score load when the maximum before the round is
`-∞`. -/
theorem stepAt_sldw3F (hp : Pre p L m) (sc ukw nb bt bpar spar ppar pl sv bk br mr rs) :
    (codeD p L g).StepAt ⟨.sldw 3,
      ⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩, 1, []⟩ := by
  have hparams := params hp
  obtain ⟨hw, hs⟩ := scl_word hp
  have hm := mulEReal_coe_bot_pos hs
  soft_sldw3 p L g (⟨sc, ukw, nb, bt, bpar, spar, ppar, pl, sv, bk, br, false, mr, rs⟩ : V) ninf32

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
