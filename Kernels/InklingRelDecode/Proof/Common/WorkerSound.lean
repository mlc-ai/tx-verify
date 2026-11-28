-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Roles
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Dispatch.Sound
public import Kernels.InklingRelDecode.Proof.Loader.Sound
public import Kernels.InklingRelDecode.Proof.Mma.Sound
import Lemmas.Flow.StrictLift
import Kernels.InklingRelDecode.Proof.Lib.LoopGlueU
import Lemmas.Flow.Arith32Word

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {g : Nat} {w : Value} {x : BitVec 64} {m : Mem0}

local notation "regs" => dispatchRegs Q L g w x
local notation "headCode" => Dispatch.code L g (startRegs Q L g w x) x 0
local notation "frags" => workerFrag Q L g w x

private abbrev keys := [3,462,463,464,465,466,528,529,530,531,532,534,1949,2020]

private theorem loader_regs (r : Nat) (hr : r ∈ keys) :
    Loader.inherited w (Loader.inputs Q L g regs) r = regs r := by
  simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

private theorem mma_regs (hp : Pre Q L m) (d : Mma.D) (r : Nat) (hr : r ∈ keys) :
    Mma.valueOf L regs w d r = regs r := by
  simp only [keys, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> try rfl
  change b32 L.sharedBase = .bits 32 (Arith32.r32 (Arith32.W L.sharedBase))
  rw [Arith32.r32_W (by have := hp.sharedRange; omega)]
  rfl

private theorem agreement {f h : Nat → Value} (heq : ∀ r ∈ keys, f r = h r) :
    factsFrom keys f = factsFrom keys h := by
  unfold factsFrom
  apply List.map_congr_left
  intro r hr
  rw [heq r hr]

theorem worker_enter (hp : Pre Q L m) : Code.Handoff headCode frags workerEntry := by
  rintro ⟨s,n⟩ i t hs hat _
  cases s <;> simp only [workerEntry, reduceCtorEq, Option.some.injEq] at hs
  · subst i
    obtain ⟨a,b,c,d,h⟩ := hat
    refine ⟨⟨a,b,c,d,?_⟩, fun he => by cases he⟩
    change Holds _ (factsFrom keys (Loader.inherited w (Loader.inputs Q L g regs)))
    rw [agreement loader_regs]
    exact h
  · subst i
    obtain ⟨a,b,c,d,h⟩ := hat
    refine ⟨⟨a,b,c,d,?_⟩, rfl⟩
    change Holds _ (factsFrom keys (Mma.valueOf L regs w {}))
    rw [agreement (mma_regs hp {})]
    exact h

theorem worker_return (hp : Pre Q L m) :
    Code.Back headCode frags (workerBack Q L g w x) := by
  intro i d p t he hat _
  cases i with
  | loader n =>
    obtain ⟨s,i,n',a,b⟩ := d
    change (if s = .dispatch then some _ else none) = some p at he
    split at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst s
    subst p
    obtain ⟨a,b,c,d,h⟩ := hat
    refine ⟨⟨a,b,c,d,?_⟩, fun he => by cases he⟩
    change Holds _ (factsFrom keys (Loader.inherited w (Loader.inputs Q L g regs))) at h
    rw [agreement loader_regs] at h
    exact h
  | mma n =>
    obtain ⟨s,i,v⟩ := d
    change (if s = .dispatch then some _ else none) = some p at he
    split at he <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst s
    subst p
    obtain ⟨a,b,c,d,h⟩ := hat
    refine ⟨⟨a,b,c,d,?_⟩, fun he => by cases he⟩
    change Holds _ (factsFrom keys (Mma.valueOf L regs w ⟨.dispatch,i,v⟩)) at h
    rw [agreement (mma_regs hp _)] at h
    exact h

public theorem worker_steps (hp : Pre Q L m) (d : (workerCode Q L g w x).D) :
    (workerCode Q L g w x).StepAtU d := by
  apply Lib.loopGlue_stepsU (fun d _ => Dispatch.stepsU d) _
    (worker_enter hp) (worker_return hp) _ d
  · rintro (n | n) d _
    · exact Loader.stepsU d
    · exact Mma.stepsU hp w d
  · rintro (n | n) <;> rfl

/-- **Every state of the workers' machine steps strictly** along the reference: the base word
is zero, the loop bounds and the pages follow the table, the words delivered are integers. -/
public theorem worker_stepFor (hp : Pre Q L m) (hw0 : w = b32 0) {n : Cls → Nat}
    (d : (workerCode Q L g w x).D) (e : Event) (inv : workerInv Q L g w x d n)
    (page : ∀ r s, d = .inr ⟨.loader r, s⟩ → (∃ u, s.site = .page u) → ∀ a bs,
      e.kind = .rd a bs → ∀ v, rebuild 3 bs = .ok v → ∃ p, v = .bits 32 p)
    (shfl : ∀ r s, d = .inr ⟨.mma r, s⟩ → ∀ a b c y ok, (e = ⟨Flow.shfl_13, .shfl .idx a b c y ok⟩ ∨
      e = ⟨Flow.shfl_14, .shfl .idx a b c y ok⟩) → y.regBits.isSome) :
    (workerCode Q L g w x).StepFor d e := by
  have hinit : ∀ i, workerBack Q L g w x i (workerFrag Q L g w x i).init = none := by
    rintro (n | n) <;> rfl
  rcases d with dsite | ⟨i, s⟩
  · exact @Code.loopGlue_inl_stepFor _ _ L g (Dispatch.code L g (startRegs Q L g w x) x 0)
      Worker (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) dsite e
      (fun _ => (Dispatch.steps dsite).stepFor e) (worker_enter hp) hinit
  · cases i with
    | loader r =>
      exact @Code.loopGlue_inr_stepFor _ _ L g (Dispatch.code L g (startRegs Q L g w x) x 0)
        Worker (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) (.loader r) s e
        (fun _ => Loader.stepFor_site inv.2.1 e (fun h => page r s rfl h)) (worker_enter hp)
        (worker_return hp) hinit
    | mma r =>
      exact @Code.loopGlue_inr_stepFor _ _ L g (Dispatch.code L g (startRegs Q L g w x) x 0)
        Worker (workerFrag Q L g w x) workerEntry (workerBack Q L g w x) (.mma r) s e
        (fun _ => Mma.stepFor_site hp (by rw [hw0]; rfl) inv.2.1 e
          (fun a b c y ok h => shfl r s rfl a b c y ok h)) (worker_enter hp)
        (worker_return hp) hinit

/-- **The template of every state of the workers' machine is not undefined behaviour.** -/
public theorem worker_safe (hp : Pre Q L m) (hg : g < L.threads) (hw0 : w = b32 0)
    (hx : x.toNat < 8) {n : Cls → Nat} (d : (workerCode Q L g w x).D)
    (inv : workerInv Q L g w x d n) {t : TState} {ins : Instr}
    (hat : (workerCode Q L g w x).AtD d t)
    (hc : kernel.code[(workerCode Q L g w x).pc d]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hp.block]
  have hr := hp.sharedRange
  unfold sharedBytes at hr
  have hhi : iterCount Q L (g / L.block) < 2 ^ 31 := by
    exact Lib.blocksOf_lt hp hg
  rcases d with dsite | ⟨i, s⟩
  · exact Dispatch.safe_site (first := 0) hb hr hx (by subst hw0; exact ⟨_, rfl⟩) hat hc f
  · cases i with
    | loader r => exact Loader.safe_site hp hg rfl rfl hhi inv.2.1 hat hc f
    | mma r => exact Mma.safe_site hp hg hw0 ⟨_, rfl⟩ hat hc f

/-- **The workers' machine dies only on the exit.** -/
public theorem worker_live (hp : Pre Q L m) (hg : g < L.threads)
    (warp : 4 ≤ g % L.block / 32 ∧ g % L.block / 32 < 8) (initial : Bool)
    {n : Cls → Nat} (d : (workerCode Q L g w x).D) (inv : workerInv Q L g w x d n)
    {t : TState} {ins : Instr} {o : Option TState} {v : Event}
    (hat : (workerCode Q L g w x).AtD d t)
    (hc : kernel.code[(workerCode Q L g w x).pc d]? = some ins)
    (hf : Fires ((workerCode Q L g w x).pc d) (eventTmpl Assumptions.all L g t ins.op) v o)
    (hu : ∀ f, v.kind ≠ .ub f)
    (words : ∀ r, d = .inl r → r.site = .read → ∀ ac bs, v.kind = .rd ac bs →
      bs = [(b32 (if initial then 16777730 else 50529027)).toBytes[g % L.block / 32 - 4]?])
    (loads : ∀ r s, d = .inr ⟨.loader r, s⟩ →
      (s.site = .first ∨ s.site = .second ∨ ∃ u, s.site = .page u) →
      ∀ ac bs, v.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x)
    (count : ∀ r s, d = .inr ⟨.mma r, s⟩ → s.site = .ldNum →
      ∀ ac bs, v.kind = .rd ac bs → ∃ x, rebuild 3 bs = .ok x)
    (hn : (workerCode Q L g w x).next d v = none) : v.kind = .exit := by
  have hhi : iterCount Q L (g / L.block) < 2 ^ 31 := by
    exact Lib.blocksOf_lt hp hg
  rcases d with dsite | ⟨i, s⟩
  · exact Dispatch.live_site warp.1 warp.2 initial hu hc hf (words dsite rfl)
      (Option.map_eq_none_iff.mp hn)
  · cases i with
    | loader r =>
      exact absurd (Option.map_eq_none_iff.mp hn)
        (Loader.live_site hp hg rfl hhi inv.2.1 hat hc hf hu (loads r s rfl))
    | mma r =>
      exact absurd (Option.map_eq_none_iff.mp hn) (Mma.live_site hp hat hc hf hu (count r s rfl))

end PTX.Kernels.InklingRelDecode.Proof
