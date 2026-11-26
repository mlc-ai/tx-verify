-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Spec
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

/-! # Reading the postcondition as numbers

`Post` states the results byte by byte, as float payloads (the form in which `Pre` asks for the
initial state). Read as a load and a floating-point instruction read memory (`memFloat`), these
bytes are the real numbers of the recurrence. -/

namespace PTX.Kernels.FlashKdaFwd
open PTX

/-- Two bytes that are a bfloat16 payload read as its number. -/
theorem bf16At.memFloat {m : Mem0} {l : Loc} {x : ℝ} (h : bf16At m l x) :
    memFloat .bf16 m l = .ok x :=
  memFloat_float fun k hk => h k hk

/-- Four bytes that are a binary32 payload read as its number. -/
theorem f32At.memFloat {m : Mem0} {l : Loc} {x : ℝ} (h : f32At m l x) :
    memFloat .f32 m l = .ok x :=
  memFloat_float fun k hk => h k hk

/-- **The postcondition, read as numbers**: every output of every token and every entry of the
final state reads as the real number of the recurrence. -/
theorem Post.reads {P : Params} {mem0 : Mem0} {m : FinalMem} (h : Post P mem0 m) :
    (∀ s < P.sequences, ∀ hd < P.heads, ∀ t < P.length s, ∀ v : Fin 128,
      memFloat .bf16 m (P.outLoc s hd t v) = .ok (P.output s hd t v)) ∧
    (∀ s < P.sequences, ∀ hd < P.heads, ∀ v k : Fin 128,
      memFloat .f32 m (P.stateLoc s hd v k) = .ok (P.state s hd v (P.length s) k)) :=
  ⟨fun s hs hd hh t ht v => (h.1 s hs hd hh t ht v).memFloat,
    fun s hs hd hh v k => (h.2.1 s hs hd hh v k).memFloat⟩

end PTX.Kernels.FlashKdaFwd
