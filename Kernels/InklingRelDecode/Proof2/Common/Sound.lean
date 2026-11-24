-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Common.Roles
public import Kernels.InklingRelDecode.Proof2.Startup.Steps
public import Kernels.InklingRelDecode.Proof2.ProA.Steps
public import Kernels.InklingRelDecode.Proof2.Tail.Steps
public import Kernels.InklingRelDecode.Proof2.Worker.Machine
public import Kernels.InklingRelDecode.Proof.Thread.SmEntry

@[expose] public section

/-! # The thread machine is sound

`thread_sound`: for every launched thread, the glued machine of `Common/Roles.lean` obeys its step
obligations from the thread's first state. Its parts are the ABI prefix to the first event (`start`,
the flat common start's run of pc 0 to 10), the startup's steps, the roles' steps (`frag_steps`: the
default partition is the prologue glued to the softmax–epilogue fragment through the gate
`TailGate`, `tail_handoff`; every stub stops at its first event) and the hand-offs (`handoff`: the
startup's facts at pc 27 are the prologue's first facts for the recorded base word, and the gate's
warp index puts the thread in warps 0 to 3, which the prologue's invariant needs). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The ABI prefix reaches the first event with the startup's first facts. -/
theorem start (hp : Pre Q L m) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} t ∧
      (Startup.code Q L g).AtD (Startup.code Q L g).init t ∧
      (Startup.code Q L g).inv (Startup.code Q L g).init := by
  have hblk := hp.block
  have hn : L.ntid = ⟨L.block, 1, 1⟩ := by rw [hp.ntid, hblk]
  obtain ⟨t, hr, ht⟩ := Startup.start0 Q L g hn (by rw [hblk]; decide) (by rw [hblk]; decide)
  have hps : explicitParams L (Startup.startParams Q) = L := by
    apply explicitParams_eq
    intro p v hm
    simp only [Startup.startParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp.paramStrideBt
    · exact hp.paramPageRows
    · exact hp.paramHeadRows
    · exact hp.paramHeadCols
    · exact hp.paramSplits
    · exact hp.paramBt
  rw [hps] at hr
  have hk : ∀ r ∈ Flow.live 11, r ∈ [3, 462, 528, 529, 530, 531, 532, 534, 1949, 2020] := by
    decide
  have hF : ∀ d : Startup.D, d.w = b32 0 → ∀ R, Holds R (Startup.preFactsAt L g Q (b32 0) 11) →
      Holds R (Startup.F Q L g 11 d) := by
    intro d hd R h
    apply holds_of_pointwise
    intro r hr
    have hv : Startup.valueOf Q L g d r = Startup.preValueOf L g Q (b32 0) r := by
      have := hk r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Startup.valueOf, Startup.values, Startup.preValueOf, Startup.table,
          PTX.Flow.lookupLit, hd]
    rw [hv]
    exact holds_mem h (Flow.mem_factsFrom hr)
  by_cases hl : g % L.block < 32
  · refine ⟨t, run_rtg hr, ?_, fun _ => hl⟩
    simp only [Startup.code, Startup.init, hl, ↓reduceIte]
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, hF _ rfl _ ht.2.2.2.2⟩
  · have hp3 : (3, Value.pred false) ∈ Startup.preFactsAt L g Q (b32 0) 11 :=
      Startup.tbl_mem (by decide) (by simp [Startup.preValueOf, Startup.table, hl])
    obtain ⟨t', hr', ht'⟩ := Seg.guardSkip (K := kernel) (A := Assumptions.all) (L := L) (g := g)
      Flow.code_11 hp3 (by simp) t ht
    refine ⟨t', (run_rtg hr).trans (run_rtg hr'), ?_, ?_⟩
    · simp only [Startup.code, Startup.init, hl, ↓reduceIte]
      refine ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ?_⟩
      exact holds_factsFrom_mono (hF ⟨.bar0, 0, 0, b32 0⟩ rfl _ ht'.2.2.2.2) (by decide)
    · simp [Startup.init, hl, Startup.Inv]

/-- The startup's steps at every state that is not an exit. -/
theorem startup_steps (hp : Pre Q L m) (d : Startup.D) (hx : Startup.enterOf d = none) :
    (Startup.code Q L g).StepAt d := by
  have hb : g % L.block < 256 := hp.block ▸ Nat.mod_lt g (by rw [hp.block]; decide)
  cases hs : d.site with
  | alloc => exact Startup.stepAt_alloc d hs
  | allocWr => exact Startup.stepAt_allocWr d hs
  | bar0 => exact Startup.stepAt_bar0 d hs
  | ld0 => exact Startup.stepAt_ld0 d hs
  | bar1 => exact Startup.stepAt_bar1 hb d hs
  | relinq => exact Startup.stepAt_relinq hb d hs
  | shfl => exact Startup.stepAt_shfl hp d hs
  | enter r => simp [Startup.enterOf, hs] at hx

/-- **The hand-off from the prologue to the softmax region**: a concrete state of the prologue's
exit whose gate holds is one of the softmax region's first state (`SmEntry.entry`). -/
theorem tail_handoff (hp : Pre Q L m) (hg : g < L.threads) (tm : Nat) (w : Value) (d : ProA.D)
    (dt : Proof.ProA.Dat) (t : TState) (hx : ProA.exitOf d = some ())
    (hs : ProA.selTail Q L g () d = some dt)
    (hat : (ProA.code L g (Startup.inh L g Q tm) w).AtD d t)
    (hi : (ProA.code L g (Startup.inh L g Q tm) w).inv d) :
    (Tail.code L g (tailInit Q L g dt)).AtD (Tail.code L g (tailInit Q L g dt)).init t ∧
      (Tail.code L g (tailInit Q L g dt)).inv (Tail.code L g (tailInit Q L g dt)).init := by
  obtain ⟨site, dt0⟩ := d
  cases site <;> simp [ProA.exitOf] at hx
  simp only [ProA.selTail] at hs
  split at hs
  · rename_i hG
    simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨hpro, hm, hw⟩ := hG
    have hspl := hp.splitsRange
    have h := Proof.SmEntry.entry (P := Q) (dt := dt0) hp hg hi.args
      (by rw [hpro]; exact Nat.mod_eq_of_lt (by omega)) hm
      (by rw [hpro]; rfl) (by rw [hpro]; show 0 + 512 ≤ 2 ^ 16; decide)
      (by rw [hw, hpro]; rfl) hp.nTokPos
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
    exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩, h.2⟩
  · cases hs

theorem stub574 : StubSite kernel 574 = true := by decide +kernel

/-- The default partition: the prologue, then the softmax–epilogue fragment (or the stub where the
gate fails). -/
theorem dp_steps (hp : Pre Q L m) (hg : g < L.threads) (tm : Nat) (w : Value)
    (d : (dpCode Q L g tm w).D) : (dpCode Q L g tm w).StepAt d :=
  Code.glue_steps (fun d hx => by
      have h := ProA.stepAt (L := L) (g := g) (Startup.inh L g Q tm) d (by
        intro h; simp [Code.gatedExit, ProA.exitOf, h] at hx)
      exact ⟨h.site, h.step⟩)
    (fun j d => match j with
      | .inl _ => Tail.stepAt hp _ d
      | .inr _ => Code.stop_steps stub574 d)
    (Code.handoff_gated
      (fun d r hx _ => by
        obtain ⟨site, dt⟩ := d
        cases site <;> simp [ProA.exitOf] at hx
        exact ⟨rfl, rfl, rfl⟩)
      (fun d r i t hx hs hat hi => tail_handoff hp hg tm w d i t hx hs hat hi)) d

theorem frag_steps (hp : Pre Q L m) (hg : g < L.threads) (i : Role) (d : (frag Q L g i).D) :
    (frag Q L g i).StepAt d := by
  cases i with
  | dp tm w => exact dp_steps hp hg tm w d
  | worker w =>
    have h := Proof.WComp.stepAt (g := g) hp d
    exact ⟨h.site, h.step⟩

/-- An exit state of the startup sits at its entry's first pc. -/
theorem stub_at (d : Startup.D) (r : Startup.Entry) (h : Startup.enterOf d = some r) :
    (Startup.code Q L g).pc d = r.pc ∧ (Startup.code Q L g).sub d = 0 ∧
      (Startup.code Q L g).acc d = [] := by
  obtain ⟨site, tm, x, bw⟩ := d
  cases site <;> simp [Startup.enterOf] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- `shl.b32 %r5, %r71, 7` on the 32-bit `num_splits` word. -/
theorem shl7 (s : Nat) :
    Arith32.shl (BitVec.ofNat 64 (s % 2 ^ 32)) 7 = BitVec.ofNat 64 (s * 128 % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp [Arith32.shl, Arith32.i32, Arith32.r32, truncBits, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- **The hand-off to the workers**: a concrete state of the startup's exit to the workers whose
gate holds is one of the worker fragment's first state, the dispatch loop's head with
`workerPro`: the startup's registers at pc 2337 are the first tree's worker registers there. -/
theorem worker_handoff (tm : Nat) (x : BitVec 64) (bw : Value) (t : TState)
    (hw : x = BitVec.ofNat 64 (g % L.block / 32))
    (hF : Holds t.regs (Startup.facts Q L g ⟨.enter .worker, tm, x, bw⟩)) :
    Holds t.regs (Proof.Worker.facts L g ⟨.loop, Worker.workerPro Q L g bw⟩) := by
  apply holds_of_pointwise
  intro r hr
  have hr' : r ∈ Flow.live (Startup.Site.enter .worker).pc := hr
  have h := holds_mem hF (Flow.mem_factsFrom hr')
  have hk : ∀ r ∈ Flow.live 2337,
      r ∈ [3, 462, 463, 464, 465, 466, 528, 529, 530, 531, 532, 534, 1949, 2020] := by decide
  have hv : Proof.Worker.valueOf L g ⟨.loop, Worker.workerPro Q L g bw⟩ r =
      Startup.valueOf Q L g ⟨.enter .worker, tm, x, bw⟩ r := by
    have := hk r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
      simp [Proof.Worker.valueOf, Proof.Worker.own, Proof.Loader.Pro.val,
        Proof.Loader.Pro.table, Worker.workerPro, Startup.valueOf, Startup.values,
        Startup.table, Proof.Worker.warpOf, Proof.Loader.baseW, Startup.baseW, hw, b32,
        List.lookup, Startup.warpOf]
    all_goals exact (shl7 Q.splits).symm
  rw [hv]
  exact h

/-- **The hand-off to the default partition**: a concrete state of the startup's exit whose gate
holds is one of the prologue's first state: the startup's facts at pc 27 are the prologue's first
facts for the recorded base word, and the gate puts the thread in warps 0 to 3, which the
prologue's invariant needs. -/
theorem handoff (hp : Pre Q L m) (hg : g < L.threads) (d : Startup.D) (r : Startup.Entry)
    (i : Role) (t : TState) (hr : Startup.enterOf d = some r) (hs : sel L g r d = some i)
    (hat : (Startup.code Q L g).AtD d t) :
    (frag Q L g i).AtD (frag Q L g i).init t ∧ (frag Q L g i).inv (frag Q L g i).init := by
  obtain ⟨hpc, hsb, ha, hf, hF⟩ := hat
  obtain ⟨site, tm, x, bw⟩ := d
  cases site with
  | enter r' => ?_
  | _ => simp [Startup.enterOf] at hr
  obtain rfl : r' = r := by simpa [Startup.enterOf] using hr
  cases r' with
  | worker =>
    simp only [sel] at hs
    split at hs
    · rename_i hgate
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [WGate, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgate
      have hb := hp.block
      refine ⟨⟨hpc, hsb, ha, hf, worker_handoff tm x bw t hgate.1 hF⟩,
        ⟨hgate.2, by rw [hb]; exact Nat.mod_lt _ (by decide), hp.btAlign, rfl, ?_⟩⟩
      show Q.headCols % 2 ^ 32 % 8 = 0
      have := hp.headColsAlign
      omega
    · cases hs
  | dp =>
    simp only [sel] at hs
    split at hs
    · rename_i hgate
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [Gate, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgate
      refine ⟨⟨hpc, hsb, ha, hf, ?_⟩, Proof.ProA.inv_start
        (Startup.argsOk_inh hp hg hgate.2 tm), rfl⟩
      apply holds_of_pointwise
      intro r hr
      have h := holds_mem hF (Flow.mem_factsFrom hr)
      rw [Startup.bridge27 (Q := Q) (L := L) (g := g) ⟨.enter .dp, tm, x, bw⟩ r hr] at h
      exact h
    · cases hs

/-- **The thread machine of every launched thread is sound.** -/
theorem thread_sound (hp : Pre Q L m) (hg : g < L.threads) : (thread Q L g).Sound :=
  Code.roleThread_sound cls (start hp) (startup_steps hp) (frag_steps hp hg)
    (fun r => by cases r <;> decide +kernel) (fun d r h _ => stub_at d r h)
    (fun d r i t hr hs hat _ => handoff hp hg d r i t hr hs hat)

end
end PTX.Kernels.InklingRelDecode.Proof2
