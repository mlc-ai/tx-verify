-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPacketFlow
public import Kernels.TmlFa4Fwd.Proof.MmaLinearEvents
public import Lemmas.Flow.TensorIssue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private def loaderMem (a : MemAccess) : Bool :=
  (a.kind == .load && !a.nc && a.regs.length ≤ 2 &&
    (a.ext == .same || a.space == some .local)) ||
  (a.kind == .store && a.space == some .local &&
    a.rule == some .threadAccess && a.srcs.length == 1)

private def loaderEventSupported : Op → Bool
  | .mem a => loaderMem a
  | .warp w => Mma.linearWarpOp w
  | .cpTensor _ _ _ _ _ _ _ _ none _ _ => true
  | .cpAsync .. | .cpAsyncCommit | .cpAsyncArrive .. | .mbarArrive ..
  | .mbarWait .. | .setMaxReg .. => true
  | op => op.isLocal

def loaderVector : Op → Bool
  | .mem a => a.kind == .load && a.regs.length == 2
  | _ => false

def loaderSubShape (s : TState) : Prop :=
  s.sub ≤ 1 ∧ (s.sub = 1 → ∃ op, kernel.code[s.pc]? = some ⟨none, op⟩ ∧
    loaderVector op = true ∧ op.isLocal = false)

private theorem loaderEventCode :
    ((kernel.code.drop 174).take (1906 - 174)).all
      (fun i => loaderEventSupported i.op &&
        (!loaderVector i.op || (i.guard.isNone && !i.op.isLocal))) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem localMemTemplate {l : Launch} {g : Nat} {s : TState} {a : MemAccess}
    (hSpace : a.space = some .local) (hRule : a.rule = some .threadAccess) :
    memTmpl Assumptions.all l g s a = accessTmpl Assumptions.all l g s a := by
  have hDirect : a.locSpace? = none := by simp [MemAccess.locSpace?, hSpace]
  simp [memTmpl, hDirect, hRule]

private def EventProgress (vector : Bool) (s u : TState) : Prop :=
  u.sub ≤ 1 ∧
    (u.pc = s.pc + 1 ∧ u.sub ≤ s.sub ∧ (vector = true → u.sub = 0) ∨
      u.pc = s.pc ∧ ((s.sub < u.sub ∧ vector = true) ∨ u.fault.isSome ∧ u.sub = s.sub))

private theorem fromAfterLoad {s : TState} {ext : MemExt} {w : Nat} {ds : List Nat}
    {bs : List (Option Byte)} (hSub : s.sub ≤ 1) (hlen : ds.length ≤ 2) :
    EventProgress (ds.length == 2) s (afterAccessLoad s ext w ds bs) := by
  unfold afterAccessLoad
  split
  · exact ⟨hSub, .inr ⟨rfl, .inr ⟨rfl, rfl⟩⟩⟩
  · split
    · exact ⟨by dsimp; omega, .inr ⟨rfl,
        .inl ⟨Nat.lt_succ_self _, beq_iff_eq.mpr (by omega)⟩⟩⟩
    · exact ⟨Nat.zero_le _, .inl ⟨rfl, Nat.zero_le _, fun _ => rfl⟩⟩

private theorem loaderMemProgress {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {a : MemAccess} (hSub : s.sub ≤ 1) (hOp : loaderMem a = true)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.mem a)) e (some u)) :
    EventProgress (loaderVector (.mem a)) s u := by
  have h : (a.kind = .load ∧ a.nc = false ∧ a.regs.length ≤ 2 ∧
      (a.ext = .same ∨ a.space = some .local)) ∨
      (a.kind = .store ∧ a.space = some .local ∧ a.rule = some .threadAccess ∧
      a.srcs.length = 1) := by
    simpa [loaderMem, and_assoc] using hOp
  rcases h with ⟨hk, hn, hLen, he | hSpace⟩ | ⟨hk, hSpace, hr, hLen⟩
  · obtain ⟨_, bs, _, rfl⟩ := fires_load hk hn hf he
    rw [← afterAccessLoad_same (w := 0)]
    simpa only [loaderVector, hk, beq_self_eq_true, Bool.true_and] using
      (fromAfterLoad (bs := bs) (ext := .same) (w := 0) hSub hLen)
  · have hRule : a.rule = some .threadAccess := by
      change Fires s.pc (memTmpl Assumptions.all l g s a) e (some u) at hf
      have hnAtom : a.rule ≠ some .threadAtomic := by
        rw [MemAccess.rule, hk]
        repeat' split
        all_goals simp_all
      by_contra hBad
      simp [memTmpl, show a.locSpace? = none by simp [MemAccess.locSpace?, hSpace],
        hBad] at hf
      cases hf.2
    simp only [eventTmpl, localMemTemplate hSpace hRule] at hf
    rcases accessTmpl_load (A := Assumptions.all) (L := l) (g := g) (t := s) hk with
      ⟨f, ht⟩ | ⟨acc, _, _, ht⟩ | ⟨_, _, hnc, _⟩
    · rw [ht] at hf
      cases hf.2
    · rw [ht] at hf
      obtain ⟨bs, _, _, hu⟩ := hf
      obtain rfl := Option.some.inj hu
      simpa only [loaderVector, hk, beq_self_eq_true, Bool.true_and] using
        (fromAfterLoad (bs := bs) (ext := a.ext) (w := a.elem.width) hSub hLen)
    · cases hn.symm.trans hnc
  · simp only [eventTmpl, localMemTemplate hSpace hr] at hf
    rcases accessTmpl_store (A := Assumptions.all) (L := l) (g := g) (t := s) hk with
      ⟨f, ht⟩ | ⟨acc, bs, _, ht⟩
    · rw [ht] at hf
      cases hf.2
    · rw [ht] at hf
      obtain rfl := Option.some.inj hf.2
      have hStep : ¬ s.sub + 1 < a.srcs.length := by rw [hLen]; omega
      exact ⟨by simp [afterStore, hStep], .inl ⟨by simp [afterStore, hStep],
        by simp [afterStore, hStep], fun _ => by simp [afterStore, hStep]⟩⟩

private theorem eventProgress {l : Launch} {g : Nat} {s u : TState}
    {e : Event} {op : Op} (hSub : s.sub ≤ 1)
    (hOp : loaderEventSupported op = true) (hLocal : op.isLocal = false)
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s op) e (some u)) :
    EventProgress (loaderVector op) s u := by
  cases op <;> simp only [loaderEventSupported, hLocal, Bool.false_eq_true] at hOp
  case mem a => exact loaderMemProgress hSub hOp hf
  case warp w =>
    obtain ⟨hp, hs⟩ := Mma.linearWarpAdvances hOp hf
    exact ⟨by omega, .inl ⟨hp, hs.le, by simp [loaderVector]⟩⟩
  case mbarWait =>
    obtain ⟨_, _, _, _, _, rfl⟩ := fires_wait hf
    exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
  case setMaxReg inc n =>
    obtain rfl := fires_next (op := .setMaxReg inc n) trivial hf
    exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
  case cpTensor ca grp dst off map cs mb moff mask mode policy =>
    cases mask
    · obtain ⟨_, _, _, rfl, _⟩ := fires_cpTensor_issue hf
      exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
    · cases hOp
  case mbarArrive =>
    obtain ⟨rfl, _⟩ := fires_arrive_state hf
    unfold mbarStateDest
    split <;> exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
  case cpAsyncCommit =>
    obtain rfl : u = next s := Option.some.inj hf.2
    exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
  case cpAsync db doff sb soff size src policy =>
    have h : CallbackFrame (· = next s)
        (eventTmpl Assumptions.all l g s (.cpAsync db doff sb soff size src policy)) := by
      simp only [eventTmpl, cpAsyncTmpl]
      apply ofExec_frame
      repeat' first | rfl | (apply allOk_bind; intro v) | split
    obtain rfl := callbackFrame_fires h hf
    exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩
  case cpAsyncArrive noinc base off generic =>
    have h : CallbackFrame (· = next s)
        (eventTmpl Assumptions.all l g s (.cpAsyncArrive noinc base off generic)) := by
      simp only [eventTmpl, cpAsyncTmpl]
      apply ofExec_frame
      repeat' first | rfl | (apply allOk_bind; intro v) | split
    obtain rfl := callbackFrame_fires h hf
    exact ⟨hSub, .inl ⟨rfl, le_rfl, by simp [loaderVector]⟩⟩

/-- Each returning event advances the loader by a PC, advances a two-element load by
one sub-step, or records a pending fault. This holds for partial executions. -/
theorem loaderEventProgressWithSubstep {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hSub : loaderSubShape s)
    (h : EStep kernel Assumptions.all l g s e (some u)) :
    loaderSubShape u ∧
      ((u.pc = s.pc + 1 ∧ u.sub = 0) ∨ u.pc = s.pc ∧ (s.sub < u.sub ∨ u.fault.isSome)) := by
  obtain ⟨ins, hc, hLoc, hf⟩ := estep_event_source h
  have hGet : ((kernel.code.drop 174).take (1906 - 174))[s.pc - 174]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
    exact hc
  have ha := List.all_eq_true.mp loaderEventCode ins (List.mem_of_getElem? hGet)
  simp only [Bool.and_eq_true] at ha
  obtain ⟨hBound, hNext | ⟨hPc, hGrow | hFault⟩⟩ := eventProgress hSub.1 ha.1 hLoc hf
  · have huZero : u.sub = 0 := by
      by_contra hNZ
      obtain ⟨op, hIns, hV, _⟩ := hSub.2 (by have := hNext.2.1; have := hSub.1; omega)
      have ht : ins = ⟨none, op⟩ := Option.some.inj (hc.symm.trans hIns)
      exact hNZ (hNext.2.2 (by rw [ht]; exact hV))
    exact ⟨⟨hBound, by omega⟩, .inl ⟨hNext.1, huZero⟩⟩
  · have hNone : ins.guard = none := by
      simpa [hGrow.2, hLoc] using ha.2
    refine ⟨⟨hBound, fun _ => ⟨ins.op, ?_, hGrow.2, hLoc⟩⟩, .inr ⟨hPc, .inl hGrow.1⟩⟩
    rw [hPc, hc]
    cases ins
    simp_all
  · exact ⟨⟨hBound, fun hOne => by simpa [hPc] using hSub.2 (hFault.2.symm.trans hOne)⟩,
      .inr ⟨hPc, .inr hFault.1⟩⟩

/-- The same progress statement for callers interested only in the program counter. -/
theorem loaderEventProgress {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1906) (hSub : loaderSubShape s)
    (h : EStep kernel Assumptions.all l g s e (some u)) :
    loaderSubShape u ∧
      (u.pc = s.pc + 1 ∨ u.pc = s.pc ∧ (s.sub < u.sub ∨ u.fault.isSome)) := by
  obtain ⟨hShape, hStep⟩ := loaderEventProgressWithSubstep hLo hHi hSub h
  exact ⟨hShape, hStep.imp_left And.left⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
