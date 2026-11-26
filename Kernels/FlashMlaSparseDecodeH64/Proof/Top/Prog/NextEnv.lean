-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.Guard
public import Lemmas.Quiet.Progress.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaLayout
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticStrong
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaFoot
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Followed

@[expose] public section

/-! # The execution facts of a released lane's step (`Descent.NextEnvQ`)

The quiet rows (`NextRow.Quiet`, `Common/Export/Next.lean`) step a released lane by
`Descent.released_stepsUQ`, whose execution facts are `Descent.NextEnvQ`. In a maximal execution
of a safe launch the static and safety ones hold (`Prog.nextEnv`): no undefined behaviour
(`Sched.safe_noUb`), the quiet extension keeps the assumptions (`wfQuiet_all`), synchronization
is guarded (`Prog.guarded`), no releasing store, atomic or thread fence (`Lib/Guarded.lean`), the
MMAs' layouts are injective (`mmaLayoutInjective`, `cta_group::1`), every Tensor Memory word is
4 bytes wide (`tmem_words`: the MMAs are `kind::f16` with an f32 accumulator by their
instruction descriptor words, `Prog.mmaKind`), and the read bytes' conflicting accesses are
ordered (`ReadsOrdered.of_safe`: no race, no mixed-size conflict, and no strong operation,
`strongOrdered`), and a new weak read keeps the assumptions (`wf_snoc_read`: the read-only
constraint is about the `ld.global.nc` reads only). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **Every MMA is `kind::f16` with bf16 inputs and an f32 accumulator**: the MMA warp's QK and
PV instruction descriptor words (`TmemRow.MmaTc`) decode to `qkD` and `pvD`. -/
theorem Prog.mmaKind (hp : Pre P L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) :
    ∀ i d s acc mask, X.MmaIssue i d s acc mask → s.descriptor.kind = .f16 .bf16 .f32 := by
  rintro ⟨g, k⟩ d s acc mask ⟨pc, he⟩
  have hR := tmem_rows hp hX (follow_of hp X hX)
  rcases TmRace.tc_role hR (Frame.lt_of_get hX he) he rfl with ⟨-, h⟩ | ⟨-, h⟩ | ⟨_, _, _, h⟩
  · simp [TmemRow.Wg0Tc] at h
  · rcases h with h | ⟨_, _, -, -, h, -⟩ | ⟨_, h, -⟩ | ⟨s', _, -, -, h, -, hd, -⟩ |
      ⟨s', _, _, -, -, h, -, -, hd, -⟩ <;>
      simp only [Kind.tc.injEq, reduceCtorEq, TcKind.mma.injEq] at h
    · obtain ⟨-, rfl, -, -⟩ := h
      rw [MmaFoot.qkD_eq hd]
      rfl
    · obtain ⟨-, rfl, -, -⟩ := h
      rw [MmaFoot.pvD_eq hd]
      rfl
  · cases h

/-- The read bytes' conflicting accesses are ordered in a maximal execution of a safe launch. -/
theorem Prog.readsOrdered (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hmax : Maximal L kernel Assumptions.all m X) : ReadsOrdered L X :=
  have hu := hs.2 X hmax.1
  ReadsOrdered.of_safe (fun h => hu (.inr (.inr (.inr (.inl h)))))
    (fun h => hu (.inr (.inr (.inl h)))) (strongOrdered hmax.1)

/-- **The execution facts of a released lane's step**, from safety. -/
theorem Prog.nextEnv (hp : Pre P L m) (hs : SafeGoal kernel Assumptions.all L m)
    {X : Execution} (hmax : Maximal L kernel Assumptions.all m X) :
    Descent.NextEnvQ L kernel Assumptions.all m X where
  max := hmax
  noUb := Sched.safe_noUb (hs.2 X hmax.1)
  wf := wfQuiet_all
  readWf _ _ _ _ _ _ := wf_snoc_read hmax.1
  reads := Prog.readsOrdered hs hmax
  guard := Prog.guarded hs hmax.1
  no_release _ _ _ _ h := noReleasingStore hmax.1 h
  no_release_rmw _ _ _ _ _ h := (noAtomicEvent hmax.1 h).elim
  no_fence _ _ _ := noThreadFence hmax.1
  layout := mmaLayoutInjective hmax.1
  words := tmem_words hmax.1 (Prog.mmaKind hp hmax.1)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
