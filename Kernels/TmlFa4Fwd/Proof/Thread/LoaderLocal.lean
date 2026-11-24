-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
public import Kernels.TmlFa4Fwd.Proof.LoaderPointerStore
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringScratchWords
public import Lemmas.Flow.LocalLoadSpace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- Every byte of this local-memory operand is in the owner's allocated loader stack. -/
def StackAccess (l : Launch) (m : Mem0) (g : Nat) (a : Acc) : Prop :=
  a.loc.space = .local ∧ a.loc.cta = g ∧
    ∀ byte < a.size, l.localBase ≤ (a.loc.at byte).addr ∧
      (a.loc.at byte).addr < l.localBase + 128 ∧ m (a.loc.at byte) ≠ none

private def localLoadOp : Op → Bool
  | .mem ma => ma.space == some .local && ma.kind == .load &&
      match ma.addr.base with
      | .reg .. => true
      | _ => false
  | _ => false

private theorem localLoadShape {op : Op} (h : localLoadOp op = true) :
    ∃ ma base width, op = .mem ma ∧ ma.space = some .local ∧ ma.kind = .load ∧
      ma.addr.base = .reg base width := by
  cases op <;> simp only [localLoadOp, Bool.false_eq_true] at h
  rename_i ma
  cases hb : ma.addr.base <;> simp [hb] at h
  exact ⟨_, _, _, rfl, h.1, h.2, hb⟩

private theorem onlyDynamicLocalLoads :
    kernel.code.all (fun i => !readOp i.op || !dynamicAccess i.op || localLoadOp i.op) =
      true := by
  decide +kernel

private theorem noDirectLocalLoads :
    kernel.code.all (fun i => loadSpace i.op != some .local) = true := by
  decide +kernel

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
include hX

private theorem localLoadFires {i : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get i = some ⟨pc, .rd a bs⟩) (hLocal : a.loc.space = .local) :
    ∃ (s : TState) (ma : MemAccess) (base width : Nat),
      ma.space = some .local ∧
      ma.kind = .load ∧ ma.addr.base = .reg base width ∧ accessAcc l i.1 s ma = .ok a := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨s, ins, _, _, hc, hf⟩
  · cases hf
  have hm := List.mem_of_getElem? hc
  rcases fires_read_loc hf rfl with ⟨hs, _⟩ | hd
  · have hChecked := List.all_eq_true.mp noDirectLocalLoads ins hm
    simp [hs, hLocal] at hChecked
  · have hChecked := List.all_eq_true.mp onlyDynamicLocalLoads ins hm
    have hop : localLoadOp ins.op = true := by
      simpa only [fires_read_op hf rfl, hd, Bool.not_true, Bool.false_or] using hChecked
    obtain ⟨ma, base, width, hMa, hSp, hKind, hBase⟩ := localLoadShape hop
    rw [hMa] at hf
    exact ⟨s, ma, base, width, hSp, hKind, hBase,
      fires_localLoadAccess hSp hKind hBase hf⟩

/-- A nonlocal read identifies its decoded instruction and owns the issuing CTA if shared. -/
theorem nonlocalReadInstruction {i : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.Reads i a bs)
    (hOutside : a.loc.space ≠ .local) :
    ∃ pc ins, X.get i = some ⟨pc, .rd a bs⟩ ∧ kernel.code[pc]? = some ins ∧
      loadSpace ins.op = some a.loc.space ∧
      (a.loc.space = .shared → a.loc.cta = i.1 / l.block) := by
  obtain ⟨pc, he⟩ := he
  rcases get_source hX he with ⟨_, hf⟩ | ⟨s, ins, _, _, hc, hf⟩
  · cases hf
  rcases fires_read_loc hf rfl with ⟨hDecoded, hOwner⟩ | hd
  · exact ⟨pc, ins, he, hc, hDecoded, hOwner⟩
  · have hChecked := List.all_eq_true.mp onlyDynamicLocalLoads ins (List.mem_of_getElem? hc)
    have hop : localLoadOp ins.op = true := by
      simpa only [fires_read_op hf rfl, hd, Bool.not_true, Bool.false_or] using hChecked
    obtain ⟨ma, base, width, hMa, hSpace, hKind, hBase⟩ := localLoadShape hop
    rw [hMa] at hf
    have ha := fires_localLoadAccess hSpace hKind hBase hf
    exact (hOutside (accessAcc_explicitLocal hSpace hBase ha).1).elim

/-- A shared read identifies its decoded instruction and its issuing CTA. -/
theorem sharedReadInstruction {i : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.Reads i a bs)
    (hShared : a.loc.space = .shared) :
    ∃ pc ins, X.get i = some ⟨pc, .rd a bs⟩ ∧ kernel.code[pc]? = some ins ∧
      loadSpace ins.op = some .shared ∧ a.loc.cta = i.1 / l.block := by
  obtain ⟨pc, ins, hGet, hCode, hLoad, hOwner⟩ :=
    nonlocalReadInstruction hX he (by rw [hShared]; decide)
  exact ⟨pc, ins, hGet, hCode, hLoad.trans (congrArg some hShared), hOwner hShared⟩

/-- Ordinary shared loads address the issuing CTA. The only dynamic loads are local. -/
theorem sharedReadOwned {i : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.Reads i a bs)
    (hShared : a.loc.space = .shared) :
    a.loc.cta = i.1 / l.block := by
  obtain ⟨_, _, _, _, _, hOwned⟩ := sharedReadInstruction hX he hShared
  exact hOwned

/-- All dynamic loads address the loader stack, and no static load addresses constant memory. -/
theorem noConstantRead {i : EvId} {a : Acc} {bytes : List (Option Byte)} (hRead : X.Reads i a bytes)
    : a.loc.space ≠ .const := by
  intro hConst
  obtain ⟨_, he⟩ := hRead
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hf
  rcases fires_read_loc hf rfl with ⟨hSpace, _⟩ | hDynamic
  · have hClosed : kernel.code.all (fun j => loadSpace j.op != some .const) = true := by
      decide +kernel
    have hNo := List.all_eq_true.mp hClosed ins (List.mem_of_getElem? hc)
    simp [hSpace, hConst] at hNo
  · have hChecked := List.all_eq_true.mp onlyDynamicLocalLoads ins (List.mem_of_getElem? hc)
    obtain ⟨ma, base, width, hOp, hs, hk, hb⟩ := localLoadShape (by
      simpa only [fires_read_op hf rfl, hDynamic, Bool.not_true, Bool.false_or] using hChecked)
    rw [hOp] at hf
    rw [(accessAcc_explicitLocal hs hb (fires_localLoadAccess hs hk hb hf)).1] at hConst
    cases hConst

/-- Every actual normal local read is owned by its issuing thread. -/
theorem localReadOwned {i : EvId} {a : Acc} {bs : List (Option Byte)} (he : X.Reads i a bs)
    (hLocal : a.loc.space = .local) :
    a.loc.cta = i.1 := by
  obtain ⟨pc, he⟩ := he
  obtain ⟨_, _, _, _, hs, _, hb, ha⟩ := localLoadFires hX he hLocal
  exact (accessAcc_explicitLocal hs hb ha).2

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
