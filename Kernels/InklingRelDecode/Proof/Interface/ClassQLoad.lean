-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Thread.ClassQNext

@[expose] public section

/-!
# The prologue's query loads return the request's query elements

A prologue state at query load `k` whose guard holds (the invariant of every state) reads the two
bytes of element `(token, head, col)` of `Q` (`ProA.ldq_spec`: the address in `Spec`'s terms),
which are launch bytes (`read_launch_byte`) of the `bf16` value `Pre.qInput` gives, so the bytes
rebuild into that value and the machine stores it as `q k` and continues (`ldq_loaded`, from
`ldq_loaded_at`). The
elements are those of the thread's tile row `m = (tid / 8) % 16 + 16 (k / 16)` (token `m / 6`,
head `6 kv_head + m % 6`) and column `8 (tid % 8) + 64 ((k % 16) / 8) + k % 8`. This is the
thread layer's half of `Out.Inputs.qTile` (the packed stores and the order are not covered), and
with it no query load of the prologue stops the machine.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem ldq_loaded (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g k0 k : Nat} (hk : k < 64) {dt : ProA.Dat} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k0) = some e)
    (hσ : St Q L X g k0 = some (some (.d (.pro ⟨ProA.ldqSite k, dt⟩)))) :
    ∃ d', ProA.next L g ⟨ProA.ldqSite k, dt⟩ e = some (some d') ∧
      d'.dt.q k = Value.float .bf16 (Q.q (Q.qStart (ProA.cta L g .z) +
        (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) / 6)
        (ProA.cta L g .y * 6 + (ProA.tidOf L g / 8 % 16 + 16 * (k / 16)) % 6)
        (8 * (ProA.tidOf L g % 8) + 64 * (k % 16 / 8) + k % 8)) :=
  ldq_loaded_at hpre hX hf.sound (tmplOk hpre) hk hg he hσ (Mbar.good_before hpre hX hf hσ)
    (Mbar.launchRead_of_facts hpre hX hf _)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
