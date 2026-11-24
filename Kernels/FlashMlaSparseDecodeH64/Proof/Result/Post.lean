-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

/-! # From the output bytes to `Post`

The result layer's last step: once the final memory holds the bytes of the ideal attention in
`O`, the bytes of `ln Z` (or the `+inf` pattern on an empty row) in `lse`, and nothing else in
the global space changes, `Post` holds. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX

/-- The byte-level statement that implies `Post`. -/
structure PostBytes (P : Params) (mem0 : Mem0) (m : FinalMem) : Prop where
  /-- Every O element's two bytes are the bf16 bytes of the attention output. -/
  o : ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, ∀ d < 512, ∀ k < 2,
    m ((oLoc P e q h d).at k) =
      some (some ((Value.float .bf16 (attn P e q h d)).byteAt k))
  /-- A non-empty row's four LSE bytes are the f32 bytes of its natural-log row sum. -/
  lse : ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h ≠ 0 → ∀ k < 4,
    m ((lseLoc P e q h).at k) = some (some ((Value.float .f32 (lse P e q h)).byteAt k))
  /-- An empty row's four LSE bytes are the f32 bytes of `+inf`. -/
  lseEmpty : ∀ e < P.b, ∀ q < P.s_q, ∀ h < 64, rowSum P e q h = 0 → ∀ k < 4,
    m ((lseLoc P e q h).at k) = some (some (infByte k))
  /-- Every other global byte is the launch byte. -/
  frame : ∀ l, l.space = .global →
    ¬ (P.outBase ≤ l.addr ∧ l.addr < P.outBase + tensorBytes P) →
    ¬ (P.lseBase ≤ l.addr ∧ l.addr < P.lseBase + lseBytes P) → m l = mem0 l

/-- The output-byte statement implies the specification's `Post`. -/
theorem post_of_bytes {P : Params} {mem0 : Mem0} {m : FinalMem} (hb : PostBytes P mem0 m) :
    Post P mem0 m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he q hq h hh d hd
    rw [memFloat_float]
    intro k hk
    exact hb.o e he q hq h hh d hd k hk
  · intro e he q hq h hh hne
    rw [memFloat_float]
    intro k hk
    exact hb.lse e he q hq h hh hne k hk
  · intro e he q hq h hh hzero k hk
    exact hb.lseEmpty e he q hq h hh hzero k hk
  · intro l hg hO hL
    exact hb.frame l hg hO hL

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
