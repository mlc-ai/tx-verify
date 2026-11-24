-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Lemmas.Flow.TcTmpl
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Prologue

noncomputable section

/-- Each correction warp meets its softmax producer on a separate named barrier for each stage. -/
def statsBarrierId (l : Launch) (g : Nat) (stage : Fin 2) : Nat :=
  warpIndex l g % 4 + 3 + 4 * stage.val

def statsBarrierReg (stage : Fin 2) : Nat := 1625 + stage.val

def statsBarrierPc (stage : Fin 2) (rescale : Bool) : Nat :=
  (statsPc stage (if rescale then .alpha else .sum)) - 1

private def statsBarrierFields (ins : Instr) : Option (Option (Nat × Bool) × Opnd × Opnd × Bool) :=
  match ins.op with
  | .barSyncN target count aligned => some (ins.guard, target, count, aligned)
  | _ => none

/-- Both correction statistics routes use their stage's 64-lane rendezvous. -/
theorem statsBarrierCode (stage : Fin 2) (rescale : Bool) :
    kernel.code[statsBarrierPc stage rescale]? =
      some ⟨none, .barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩ := by
  have hTable : ∀ (stage : Fin 2) (rescale : Bool),
      (kernel.code[statsBarrierPc stage rescale]?).bind statsBarrierFields =
        some (none, .reg (statsBarrierReg stage), .imm 64, true) := by decide +kernel
  have h := hTable stage rescale
  cases hCode : kernel.code[statsBarrierPc stage rescale]? with
  | none => simp [hCode] at h
  | some i =>
    obtain ⟨guard, op⟩ := i
    cases op <;> simp [hCode, statsBarrierFields] at h ⊢
    case barSyncN target count aligned =>
      exact h

variable {p : Params} {l : Launch} {m : Mem0}

/-- A decoded 64-lane correction rendezvous publishes the actual named-barrier event
and retains the same frame on its continuation. -/
theorem observeCorrectionNamedBarrierPrefix {X : Execution} {g pos pc : Nat} {t : TState}
    {o : Option TState} {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2) (ht : At t pc F)
    (hCode : kernel.code[pc]? =
      some ⟨none, .barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩)
    (hModel : out kernel Assumptions.all l g t = out kernel [] l g t)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    X.get (g, pos) = some ⟨pc, .bar (statsBarrierId l g stage) (some 64) .sync⟩ ∧
    At (next t) (pc + 1) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) o := by
  let id := statsBarrierId l g stage
  have hId : id < 16 := by
    have ha := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    have hs := stage.isLt
    dsimp [id, statsBarrierId]
    omega
  have hCount : 64 ≠ l.block := by rw [hp.block]; decide
  have hWord : readBits l g t 32 (.reg (statsBarrierReg stage)) =
      .ok (BitVec.ofNat 64 id) := readBits_b32 hBar (by omega)
  have hIdNat : (BitVec.ofNat 64 id).toNat = id := toNat_ofNat_lt (by omega)
  have hNum : readBits l g t 32 (.imm 64) = .ok (BitVec.ofNat 64 64) := rfl
  have hn : Next kernel Assumptions.all l g t t (.bar id (next t) (some 64) .sync) := by
    refine ⟨.refl, ?_⟩
    rw [hModel, out_event ht.2.2.2.1 (ht.1.symm ▸ hCode) rfl rfl]
    change Out.ev (barTmpl l g t (.reg (statsBarrierReg stage)) (some (.imm 64)) .sync) = _
    simp [barTmpl, hWord, hIdNat, hNum, hCount,
      show ¬16 ≤ id by omega]
  obtain ⟨_, _, he, hFire, hTail⟩ := hn.continuing_at_nonempty (by
    rintro _ ⟨_, hBad⟩
    cases hBad) hr hMore
  obtain ⟨rfl, hu⟩ := hFire
  obtain rfl := Option.some.inj hu
  rw [ht.1] at he
  exact ⟨he, ht.next, hTail⟩

/-- The actual statistics barrier is a 64-lane arrival with acquire/release synchronization.
On its continuation each correction lane is at the matching alpha or final-sum load. -/
theorem observeStatsBarrierPrefix {X : Execution} {g pos : Nat} {t : TState} {o : Option TState}
    {F : List (Nat × Value)} (hp : Pre p l m) (stage : Fin 2) (rescale : Bool)
    (ht : At t (statsBarrierPc stage rescale) F)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    X.get (g, pos) = some
      ⟨statsBarrierPc stage rescale, .bar (statsBarrierId l g stage) (some 64) .sync⟩ ∧
    At (next t) (statsPc stage (if rescale then .alpha else .sum)) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) o := by
  have hOut : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ (ht.1.symm ▸ statsBarrierCode stage rescale) rfl
    all_goals rw [ht.1]; cases rescale <;> fin_cases stage <;> decide
  obtain ⟨he, hu, hTail⟩ :=
    observeCorrectionNamedBarrierPrefix hp stage ht (statsBarrierCode stage rescale)
      hOut hBar hr hMore
  have hPc : statsBarrierPc stage rescale + 1 =
      statsPc stage (if rescale then .alpha else .sum) := by
    cases rescale <;> fin_cases stage <;> decide
  exact ⟨he, hPc ▸ hu, hTail⟩

/-- The actual statistics barrier is a 64-lane arrival with acquire/release synchronization.
On its continuation each correction lane is at the matching alpha or final-sum load. -/
theorem observeStatsBarrier {X : Execution} {g pos : Nat} {t : TState} {F : List (Nat × Value)}
    (hp : Pre p l m) (stage : Fin 2) (rescale : Bool) (ht : At t (statsBarrierPc stage rescale) F)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some
      ⟨statsBarrierPc stage rescale, .bar (statsBarrierId l g stage) (some 64) .sync⟩ ∧
    At (next t) (statsPc stage (if rescale then .alpha else .sum)) F ∧
    Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos + 1)) none :=
  observeStatsBarrierPrefix hp stage rescale ht hBar hr
    (by intro h; rw [h] at hr; cases hr)

end
end PTX.Kernels.TmlFa4Fwd.Correction
