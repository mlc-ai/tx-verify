-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.MmaWholePrefix
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma Prologue

noncomputable section

private def preservesColumn (op : Op) : Bool :=
  !(mmaWrites op).contains 1179 &&
    match op with
    | .bra dest _ => decide (1912 ≤ dest)
    | .brx .. => false
    | _ => true

set_option maxRecDepth 100000 in
private theorem preservesColumnAt {pc : Nat} {i : Instr} (hLo : 1912 ≤ pc) (hHi : pc < 2768)
    (hCode : kernel.code[pc]? = some i) : preservesColumn i.op = true := by
  let code := (kernel.code.drop 1912).take (2768 - 1912)
  have hAll : code.all (fun i => preservesColumn i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll
  apply List.mem_of_getElem? (i := pc - 1912)
  dsimp only [code]
  rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]

private theorem allocationFloor {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1912 ≤ s.pc) (hHi : s.pc < 2768) (hStep : WStep kernel Assumptions.all l g s e u) :
    1912 ≤ u.pc := by
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, hEvent⟩
  · have hTau' : Tau kernel [] l g s u := by
      unfold Tau at hTau ⊢
      rwa [← out_eq_core (by omega) hHi]
    obtain ⟨i, hc⟩ := tau_core_has_code hTau'
    rcases tau_core_frame hc hTau' with rfl | hFrame
    · change 1912 ≤ s.pc + 1
      omega
    · have hBranch := (Bool.and_eq_true_iff.mp (preservesColumnAt hLo hHi hc)).2
      have hPc := hFrame.pc
      cases hOp : i.op <;> simp only [hOp, nextPc, BrxTarget, or_false] at hPc
      case bra dest uni =>
        rw [hPc]
        exact of_decide_eq_true (by simpa only [hOp] using hBranch)
      case brx => simp [hOp] at hBranch
      all_goals omega
  · have he : EStep kernel [] l g s e (some u) := by
      obtain ⟨tmpl, hOut, hf⟩ := hEvent
      exact ⟨tmpl, by rwa [← out_eq_core (by omega) hHi], hf⟩
    rcases (estep_return_pc he (fun _ _ _ h => execLocal_frame h)).2 with h | h <;> omega

private theorem allocationFrameStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 1912 ≤ s.pc) (hHi : s.pc < 2768) (hShape : RoleShape s)
    (hRole : s.regs 1062 = some (b32 12)) (hValue : s.regs 1179 = some (b32 0))
    (hStep : WStep kernel Assumptions.all l g s e u) :
    RoleShape u ∧ u.regs 1062 = some (b32 12) ∧ u.regs 1179 = some (b32 0) ∧
      (1912 ≤ u.pc ∧ u.pc < 2768 ∨ u.pc = 3099 ∧ u.fault = none) := by
  obtain ⟨hDomain, hShape', hRole'⟩ := mmaCutStep (by omega) hHi hStep ⟨hShape, hRole⟩
  have hValue' : u.regs 1179 = s.regs 1179 := by
    apply mmaStepReg (by omega) hHi _ hStep
    intro i hCode
    have hStable := (Bool.and_eq_true_iff.mp (preservesColumnAt hLo hHi hCode)).1
    simpa using hStable
  refine ⟨hShape', hRole', hValue'.trans hValue, ?_⟩
  exact hDomain.imp (fun h => ⟨allocationFloor hLo hHi hStep, h.2⟩)
    (fun h => ⟨List.mem_singleton.mp h.1, h.2⟩)

/-- The allocator's column stays live on a returning prefix within the MMA body. -/
theorem mmaAllocationRegistersOfPrefix {l : Launch} {g : Nat} {t u : TState}
    {es : List Event} (hReach : TraceReach kernel Assumptions.all l g t es u)
    (hLo : 1912 ≤ t.pc) (hHi : u.pc < 2767) (hShape : RoleShape t)
    (hRole : t.regs 1062 = some (b32 12)) (hValue : t.regs 1179 = some (b32 0)) :
    u.regs 1062 = some (b32 12) ∧ u.regs 1179 = some (b32 0) := by
  have step {s v : TState} {e : Option Event} {es : List Event}
      (hStep : WStep kernel Assumptions.all l g s e v)
      (hTail : TraceReach kernel Assumptions.all l g v es u)
      (hLo : 1912 ≤ s.pc) (hShape : RoleShape s) (hRole : s.regs 1062 = some (b32 12))
      (hValue : s.regs 1179 = some (b32 0)) :
      1912 ≤ v.pc ∧ RoleShape v ∧ v.regs 1062 = some (b32 12) ∧
        v.regs 1179 = some (b32 0) := by
    have hV : v.pc < 2767 := by
      by_contra! h
      exact (Nat.not_le_of_lt hHi) (resourceSuffixFloor .release hTail h)
    have hS : s.pc < 2767 := by
      by_contra! h
      have hReach : ∃ events, TraceReach kernel Assumptions.all l g s events v := by
        rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, he⟩
        · exact ⟨[], .tau hTau (.refl _)⟩
        · exact ⟨[e], .event he (.refl _)⟩
      exact (Nat.not_le_of_lt hV) (resourceSuffixFloor .release hReach.choose_spec h)
    obtain ⟨hShape', hRole', hValue', hPc⟩ :=
      allocationFrameStep hLo (by omega) hShape hRole hValue hStep
    exact ⟨hPc.elim And.left (fun h => by omega), hShape', hRole', hValue'⟩
  induction hReach with
  | refl => exact ⟨hRole,hValue⟩
  | tau hTau hTail ih =>
    obtain ⟨hl, hs, hr, hv⟩ := step (.inl ⟨rfl,hTau⟩) hTail hLo hShape hRole hValue
    exact ih hl hHi hs hr hv step
  | event he hTail ih =>
    obtain ⟨hl, hs, hr, hv⟩ := step (.inr ⟨_,rfl,he⟩) hTail hLo hShape hRole hValue
    exact ih hl hHi hs hr hv step

private theorem allocationFrameInWalk {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hWalk : Walk kernel Assumptions.all l g s es vs)
    (hLo : 1912 ≤ s.pc) (hHi : s.pc < 2768) (hShape : RoleShape s)
    (hRole : s.regs 1062 = some (b32 12)) (hValue : s.regs 1179 = some (b32 0))
    {e : Event} (hMember : e ∈ es) (hEnd : e.pc < 2768) :
    ∃ t o, t.regs 1179 = some (b32 0) ∧ EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases hMember
  | last he =>
    obtain rfl := List.mem_singleton.mp hMember
    exact ⟨_, _, hValue, he⟩
  | @tau s u es vs ht hw ih =>
    obtain ⟨hShape', hRole', hValue', hDomain | hExit⟩ :=
      allocationFrameStep hLo hHi hShape hRole hValue (.inl ⟨rfl, ht⟩)
    · exact ih hDomain.1 hDomain.2 hShape' hRole' hValue' hMember
    · have hPc := mmaEpilogueExitEvents hExit.1 hExit.2 (.inl rfl) hRole' hw e hMember
      omega
  | @ev s u ev es vs he hw ih =>
    rcases List.mem_cons.mp hMember with rfl | hMem
    · exact ⟨_, _, hValue, he⟩
    · obtain ⟨hShape', hRole', hValue', hDomain | hExit⟩ :=
        allocationFrameStep hLo hHi hShape hRole hValue (.inr ⟨_, rfl, he⟩)
      · exact ih hDomain.1 hDomain.2 hShape' hRole' hValue' hMem
      · have hPc := mmaEpilogueExitEvents hExit.1 hExit.2 (.inl rfl) hRole' hw e hMem
        omega

/-- Any later MMA-role event retains the actual startup cursor after reading column zero. -/
theorem mmaStartAfterAllocation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hWarp : warpIndex l g = 12) (hLo : 1911 < e.pc) :
    allocationBarrierPos l g + 2 ≤ index ∧ ∃ u o,
      At u 1912 [(1179, b32 0), (1062, b32 12)] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (allocationBarrierPos l g + 2)) o := by
  obtain ⟨t, bytes, o, ht, _, heRead, hIndex, _, hRun⟩ :=
    allocationReadBeforeEvent hp hX he hWarp hLo
  have hBytes := mmaAllocationReadZero hp hX heRead
  subst bytes
  let u := afterLoad t [1179] ((b32 0).toBytes.map some)
  have hu : At u 1912 [(1179, b32 0), (1062, b32 12)] := by
    unfold u
    rw [afterLoad_ok ht.2.1 ht.2.2.1 (PTX.Proof.rebuild_scalar (v := b32 0) (by decide) rfl)]
    refine ⟨by simp [ht.1], rfl, rfl, ht.2.2.2.1, ?_⟩
    simp [setReg, ht.2.2.2.2.1]
  exact ⟨hIndex, u, o, hu, hRun⟩

/-- The allocation base stays in the MMA lane's register from the actual read through its use. -/
theorem mmaAllocationRegisterBeforeEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hWarp : warpIndex l g = 12) (hLo : 1911 < e.pc) (hHi : e.pc < 2768) :
    ∃ t o, t.regs 1179 = some (b32 0) ∧ EStep kernel Assumptions.all l g t e o := by
  obtain ⟨hIndex, u, _, hu, hRun⟩ := mmaStartAfterAllocation hp hX he hWarp hLo
  obtain ⟨_, hWalk⟩ := walkFromRun hRun
  have hMem : e ∈ (X.tr g).drop (allocationBarrierPos l g + 2) := by
    apply List.mem_of_getElem? (i := index - (allocationBarrierPos l g + 2))
    rwa [List.getElem?_drop, Nat.add_sub_of_le hIndex]
  exact allocationFrameInWalk hWalk (by rw [hu.1]) (by rw [hu.1]; decide)
    ⟨hu.2.1.symm ▸ Nat.zero_le _, hu.2.2.1, fun _ => hu.2.1⟩
    hu.2.2.2.2.2.1 hu.2.2.2.2.1 hMem hHi

/-- An actual deallocation returns the full column-zero allocation. -/
theorem mmaDeallocReturnsZero {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index base : Nat} {group : CtaGroup} {dst : Option Loc}
    (he : X.get (g, index) = some ⟨2766, .tc (.resource group dst (.dealloc base 512))⟩) :
    base = 0 := by
  have hRole := roleBodyPcOfEvent hp hX he
    (show 173 < 2766 by decide) (show 2766 ∉ registerHintSites by decide)
  have hWarp : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) 2766 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨t, o, hValue, hEvent⟩ :=
    mmaAllocationRegisterBeforeEvent hp hX he hWarp (show 1911 < 2766 by decide)
      (show 2766 < 2768 by decide)
  have hPc : t.pc = 2766 := (estep_source_pc hEvent).symm
  obtain ⟨tmpl, hOut, hFire⟩ := hEvent
  rcases out_ev hOut with ⟨fault, rfl⟩ | ⟨ins, hc, rfl⟩
  · exact (Kind.noConfusion (congrArg Event.kind hFire.1) : False).elim
  rw [hPc, Flow.code_2766] at hc
  obtain rfl := Option.some.inj hc
  have hBits : readBits l g t 32 (.reg 1179) = .ok 0 := readBits_b32 hValue (by decide)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  cases hn : readBits l g t 32 (.reg 2682) with
  | error fault =>
    simp [eventTmpl, tcTmpl, hBlock, hBits, hn, bind, Except.bind, ofExec, Fires] at hFire
  | ok n =>
    by_cases hv : Tmem.validColumns n.toNat = true
    · simp [eventTmpl, tcTmpl, hBlock, hBits, hn, hv, bind, Except.bind, pure, Except.pure,
        ofExec, Fires, hPc] at hFire
      omega
    · simp [eventTmpl, tcTmpl, hBlock, hBits, hn, hv, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, ofExec, Fires] at hFire

end
end PTX.Kernels.TmlFa4Fwd.Thread
