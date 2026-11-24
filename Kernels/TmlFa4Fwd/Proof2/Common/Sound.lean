-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Common.Roles
public import Kernels.TmlFa4Fwd.Proof2.Startup.Steps
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Steps
public import Kernels.TmlFa4Fwd.Proof2.Mma.Startup
public import Kernels.TmlFa4Fwd.Proof2.Correction.Steps
public import Kernels.TmlFa4Fwd.Proof2.Correction.Handoff

@[expose] public section

/-! # The thread machine is sound

`thread_sound`: for every launched thread, the glued machine of `Common/Roles.lean` obeys its
step obligations from the thread's first state. Its parts are the ABI prefix to the first
shuffle (`start`, from the decoded parameter loads), the startup's steps (`Startup.stepAt`), the
roles' steps (`frag_steps`: the MMA warp's `Mma.stepAt_G`, the output warp's `Epilogue.stepAt`,
the correction and loader warps' steps, and the stubs, which stop at their first event) and one
hand-off per migrated role (`handoff`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The ABI prefix reaches the first shuffle with the startup's first facts. -/
theorem start (hp : Pre p L m) : ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} t ∧
    (Startup.code p L g).AtD (Startup.code p L g).init t ∧ (Startup.code p L g).inv
      (Startup.code p L g).init := by
  obtain ⟨t, hrun, hpc, hs, ha, hf, hF⟩ := Prologue.startWith (A := Assumptions.all) hp g
  refine ⟨t, run_rtg hrun, ⟨hpc, hs, ha, hf, ?_⟩, trivial⟩
  apply holds_of_pointwise
  intro r hr
  change r ∈ Flow.live 25 at hr
  have hl : Flow.live 25 = [1663, 1665, 7289, 7290, 7291, 7292, 7293, 7294, 7295, 7492, 7493,
      7494, 7495, 7496, 7497, 7498, 7499, 7500, 7501, 7502, 7503, 7504, 7505, 7506] := by
    rfl
  rw [hl] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact holds_mem hF (by simp [Startup.valueOf, Startup.values, Prologue.abiFacts, List.lookup])

/-- The startup's steps at every state that is not an exit. -/
theorem startup_steps (hp : Pre p L m) (hg : g < L.threads) (d : Startup.D)
    (hx : exit L g d = none) : (Startup.code p L g).StepAt d := by
  cases hs : d.site with
  | sh j => exact Startup.stepAt_sh hp hg d ⟨j, hs⟩
  | elect j => exact Startup.stepAt_elect hp hg d ⟨j, hs⟩
  | init n => exact Startup.stepAt_init hp hg d ⟨n, hs⟩
  | fence => exact Startup.stepAt_fence hp hg d (.inl hs)
  | bar => exact Startup.stepAt_fence hp hg d (.inr hs)
  | enter r => simp [exit, hs] at hx

/-- A stub stops at its first event, an event instruction with no guard. -/
theorem stop_steps (r : Startup.Entry) (d : Unit) : (stop L g r.pc).StepAt d where
  site := fun _ => by
    cases r
    · exact ⟨_, Flow.code_179, rfl, trivial⟩
    · exact ⟨_, Flow.code_1907, rfl, trivial⟩
    · exact ⟨_, Flow.code_2769, rfl, trivial⟩
    · exact ⟨_, Flow.code_3102, rfl, trivial⟩
    · exact ⟨_, Flow.code_7746, rfl, trivial⟩
    · exact ⟨_, Flow.code_9205, rfl, trivial⟩
  step := fun _ _ _ _ _ => .inl (.inl rfl)

theorem frag_steps (hp : Pre p L m) (hg : g < L.threads) (i : Role) (d : (frag p L g i).D) :
    (frag p L g i).StepAt d := by
  cases i with
  | mma => exact Mma.stepAt_G hp hg d
  | epilogue => exact Epilogue.stepAt hp hg d
  | correction => exact Correction.stepAt hp hg d
  | loader b => exact Loader.steps hp hg b d
  | stub r => exact stop_steps r d
  | softmax => exact SmWarp.stepAt hp hg d

/-- A shared-memory address below `2 ^ 18` plus an offset, as the code's `add.s32` computes it. -/
theorem addi_sb {b n : Nat} (h : b + n < 2 ^ 31) :
    Epilogue.addi (BitVec.ofNat 64 b) n = BitVec.ofNat 64 (b + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Epilogue.addi, Epilogue.r32, Epilogue.i32, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt]
  have h1 : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n := by omega
  rw [h1]
  simp only [Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b + n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b + n < 2 ^ 32 by omega)]

/-- The CTA index the dispatch reads is the thread's CTA. -/
theorem cta_word (hp : Pre p L m) (hg : g < L.threads) :
    Startup.sreg (Startup.ctaX p L g) = BitVec.ofNat 64 (g / L.block) := by
  simp only [Startup.ctaX, Epilogue.params hp]
  have hcta : (L.ctaidOf (g / L.block)).get .x = g / L.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hblock : 0 < L.block := by rw [hp.block]; decide
  have hgrid : g / L.block < L.grid :=
    (Nat.div_lt_iff_lt_mul hblock).2 (show g < L.grid * L.block from hg)
  have hCta32 : g / L.block < 2 ^ 32 := by have := hp.grid.2.2; omega
  rw [hcta]
  exact truncBits_ofNat hCta32 (by decide)

/-- The batch size as the dispatch's parameter load reads it. -/
theorem batch_word (hp : Pre p L m) : Startup.sreg p.batch = BitVec.ofNat 64 p.batch :=
  truncBits_ofNat (hp.values (19, p.batch) (by simp [Params.scalarWords])).1 (by decide)

/-- **The hand-offs**: a concrete state of the startup's exit is one of its role's first state;
for the MMA and the output warp, given the gate's shared base and warp index. -/
theorem handoff (hp : Pre p L m) (hg : g < L.threads) :
    Code.Handoff (Startup.code p L g) (frag p L g) (exit L g) := by
  intro d i t hx ⟨hpc, hs, ha, hf, hF⟩ _
  obtain ⟨site, x1, x2, x3⟩ := d
  cases site with
  | sh _ | elect _ | init _ | fence | bar => simp [exit] at hx
  | enter r =>
    simp only [exit, Option.some.injEq] at hx
    subst hx
    have stub : ∀ r' : Startup.Entry, r'.pc = r.pc →
        (frag p L g (.stub r')).AtD (frag p L g (.stub r')).init t ∧
          (frag p L g (.stub r')).inv (frag p L g (.stub r')).init :=
      fun r' h => ⟨⟨hpc.trans h.symm, hs, ha, hf, by simp [Holds]⟩, trivial⟩
    have hb := hp.shared.2.1
    have e1 := addi_sb (b := L.sharedBase) (n := 192) (by omega)
    have e2 := addi_sb (b := L.sharedBase) (n := 68608) (by omega)
    have e3 := addi_sb (b := L.sharedBase) (n := 208) (by omega)
    have e4 := addi_sb (b := L.sharedBase) (n := 144) (by omega)
    have e5 := addi_sb (b := L.sharedBase) (n := 224) (by omega)
    simp only [Nat.cast_ofNat] at e1 e2 e3 e4 e5
    have e6 := cta_word hp hg
    have e7 := batch_word hp
    cases r with
    | mma =>
      by_cases hgate : Gate L g .mma ⟨.enter .mma, x1, x2, x3⟩ = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgate)]
        simp only [roleOf]
        simp only [Gate, Bool.and_eq_true, beq_iff_eq] at hgate
        obtain ⟨rfl, rfl⟩ := hgate
        refine ⟨⟨hpc, hs, ha, hf, ?_⟩, trivial, rfl⟩
        apply holds_of_pointwise
        intro r hr
        change r ∈ Flow.live 1907 at hr
        rw [Mma.live_1907] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
          refine (holds_mem hF (mem_factsFrom (by
            change _ ∈ Flow.live 1907; rw [Mma.live_1907]; simp))).trans ?_ <;>
          simp [Startup.valueOf, Startup.values, Prologue.abiFacts, Mma.valueOf, Mma.values,
            Mma.valuesRole, Mma.valuesStart, Mma.ent, Epilogue.ctaW, b32, List.lookup, e1, e2, e3,
            e4, e5, e6, e7]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgate)]
        exact stub _ rfl
    | epilogue =>
      by_cases hgate : Gate L g .epilogue ⟨.enter .epilogue, x1, x2, x3⟩ = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgate)]
        simp only [roleOf]
        simp only [Gate, Bool.and_eq_true, beq_iff_eq] at hgate
        obtain ⟨rfl, rfl⟩ := hgate
        refine ⟨⟨hpc, hs, ha, hf, ?_⟩, trivial⟩
        apply holds_of_pointwise
        intro r hr
        change r ∈ Flow.live 2769 at hr
        rw [Epilogue.live_2769] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
          refine (holds_mem hF (mem_factsFrom (by
            change _ ∈ Flow.live 2769; rw [Epilogue.live_2769]; simp))).trans ?_ <;>
          simp [Startup.valueOf, Startup.values, Prologue.abiFacts, Epilogue.valueOf,
            Epilogue.values, Epilogue.valuesStart, Epilogue.ent, Epilogue.ctaW, b32, List.lookup,
            e1, e2, e3, e4, e5, e6, e7]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgate)]
        exact stub _ rfl
    | correction =>
      by_cases hgate : Gate L g .correction ⟨.enter .correction, x1, x2, x3⟩ = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgate)]
        simp only [roleOf]
        simp only [Gate, Bool.and_eq_true, beq_iff_eq] at hgate
        obtain ⟨rfl, rfl⟩ := hgate
        refine ⟨⟨hpc, hs, ha, hf, ?_⟩, by simp⟩
        show Holds t.regs ((Correction.code p L g).facts (Correction.code p L g).init)
        rw [Correction.facts_init]
        have hv : ∀ r ∈ Flow.live 7746, t.regs r = some
            (Startup.valueOf p L g ⟨.enter .correction, BitVec.ofNat 64 L.sharedBase, x2,
              BitVec.ofNat 64 (g % L.block / 32)⟩ r) := fun r hr => holds_mem hF (mem_factsFrom hr)
        simp only [Correction.live_7746, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hv
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hv
        simp only [Holds]
        refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_, h6.trans ?_,
          h7.trans ?_, h8.trans ?_, h9.trans ?_, h10.trans ?_, h11.trans ?_, h12.trans ?_,
          trivial⟩ <;>
          simp [Startup.valueOf, Startup.values, Prologue.abiFacts, b32, List.lookup, e1, e2, e3,
            e4, e5, e6, e7]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgate)]
        exact stub _ rfl
    | loader =>
      by_cases hgate : Gate L g .loader ⟨.enter .loader, x1, x2, x3⟩ = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgate)]
        simp only [roleOf]
        simp only [Gate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hgate
        obtain ⟨rfl, h3⟩ := hgate
        have hw : x3 = BitVec.ofNat 64 (Loader.wOf (x3 == BitVec.ofNat 64 15)) := by
          rcases h3 with rfl | rfl <;> decide
        rw [hw] at hF
        exact ⟨⟨hpc, hs, ha, hf, Loader.handoff hp hg _ hF⟩, Or.inl trivial⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgate)]
        exact stub _ rfl
    | softmax =>
      by_cases hgate : Gate L g .softmax ⟨.enter .softmax, x1, x2, x3⟩ = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hgate)]
        simp only [roleOf]
        simp only [Gate, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgate
        obtain ⟨⟨rfl, rfl⟩, hw⟩ := hgate
        exact ⟨⟨hpc, hs, ha, hf, Softmax.handoff hp hg hF⟩,
          by simp [Softmax.Site.first], hw, .inr rfl⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hgate)]
        exact stub _ rfl
    | _ => exact stub _ rfl

/-- **The thread machine of every launched thread is sound.** -/
theorem thread_sound (hp : Pre p L m) (hg : g < L.threads) : (thread p L g).Sound :=
  Code.counted_sound
    (Code.glue_sound (start hp) (startup_steps hp hg) (frag_steps hp hg) (handoff hp hg))

end
end PTX.Kernels.TmlFa4Fwd.Proof2
