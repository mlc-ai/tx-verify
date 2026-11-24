-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocationTrace
public import Lemmas.Tmem.PairProtocol
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.OpPcsFast
import Lemmas.Flow.Resource

public section

/-! # The allocator events of the sparse-decode thread machine -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents

open PTX PTX.Proof PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {g : Nat}

private def locations : List Nat := [Flow.tmemAlloc_0, Flow.tmemRelinquish_0, Flow.tmemDealloc_0]

set_option maxRecDepth 100000 in
private theorem locations_cover : OpPcsFast kernel.code tmemOp locations = true := by
  decide +kernel

private def ResourceSite : Machine.ThreadD → Prop
  | .prologue s => s = .alloc ∨ s = .allocStore ∨ s = .relinquish
  | .wg0 d => d.site = .exit
  | _ => False

local macro "exclude_resource " h:ident : tactic => `(tactic| (
  exfalso
  revert $h
  first
  | decide
  | rename_i a; revert a; decide
  | rename_i a b; revert a b; decide
  | rename_i a b c; revert a b c; decide
  ))

private theorem site_of_pc {d : Machine.ThreadD} (h : (Machine.code P L g).pc d ∈ locations) :
    ResourceSite d := by
  cases d
  case prologue s =>
    change s.pc ∈ locations at h
    change s = .alloc ∨ s = .allocStore ∨ s = .relinquish
    cases s <;> first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl) |
      exclude_resource h
  case wg0 d =>
    change d.site.pc ∈ locations at h
    change d.site = .exit
    generalize d.site = s at h ⊢
    clear d
    cases s <;> first | rfl | exclude_resource h
  case mma d =>
    change d.site.pc ∈ locations at h
    change False
    generalize d.site = s at h
    clear d
    cases s <;> exclude_resource h
  case tma d =>
    change d.site.pc ∈ locations at h
    change False
    generalize d.site = s at h
    clear d
    cases s <;> exclude_resource h
  case index d =>
    change d.site.pc ∈ locations at h
    change False
    generalize d.site = s at h
    clear d
    cases s <;> exclude_resource h
  case wg2 d =>
    change d.site.pc ∈ locations at h
    change False
    generalize d.site = s at h
    clear d
    cases s <;> exclude_resource h
  case idle s =>
    change s.pc ∈ locations at h
    change False
    cases s <;> exclude_resource h
  case head =>
    change 1843 ∈ locations at h
    exclude_resource h
  case done =>
    change 3611 ∈ locations at h
    exclude_resource h

/-- Actual allocator events of the thread machine, with the precise one-CTA operands. -/
inductive Emits (L : Launch) (g : Nat) (group : CtaGroup) (dst : Option Loc)
    (req : Tmem.Request) : Machine.ThreadD → Prop
  | alloc : group = .one → dst = some (PrologueAllocation.allocAddress L g) →
      req = .alloc 512 → Emits L g group dst req (.prologue .alloc)
  | relinquish : group = .one → dst = none → req = .relinquish →
      Emits L g group dst req (.prologue .relinquish)
  | dealloc (d : Wg0.D) : d.site = .exit → warpOf L g = 0 → group = .one → dst = none →
      req = .dealloc 0 512 → Emits L g group dst req (.wg0 d)

/-- Classify a resource event from its actual firing and the typed state at that event. -/
theorem emits {mem0 : Mem0} {d : Machine.ThreadD} {e : Event} {o : Option TState}
    {grp : CtaGroup} {dst : Option Loc} {req : Tmem.Request} (hpre : Pre P L mem0)
    (hFire : (Machine.machine P L g).Fired (some d) e o)
    (hk : e.kind = .tc (.resource grp dst req)) :
    Emits L g grp dst req d := by
  obtain ⟨t, ⟨hAt, hInv⟩, hf⟩ := hFire
  change Fires t.pc (match kernel.code[(Machine.code P L g).pc d]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  cases hc : kernel.code[(Machine.code P L g).pc d]? with
  | none =>
    rw [hc] at hf
    have hv := congrArg Event.kind hf.1
    rw [hk] at hv
    cases hv
  | some ins =>
    rw [hc] at hf
    have hSite := site_of_pc (OpPcsFast.mem locations_cover hc (fires_resource_op hf hk))
    cases d
    case prologue s =>
      change s = .alloc ∨ s = .allocStore ∨ s = .relinquish at hSite
      rcases hSite with rfl | rfl | rfl
      · change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        change Fires t.pc (eventTmpl Assumptions.all L g t (.tcAlloc .one 554 0 (.reg 555)))
          e o at hf
        have hb : L.block % 32 = 0 := by rw [hpre.block]
        have ha : t.regs 554 = some (b32 (PrologueAllocation.allocAddress L g).addr) :=
          holds_mem hAt.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
        have hn : t.regs 555 = some (b32 512) :=
          holds_mem hAt.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
        have hbase := hpre.sharedAlignment
        rw [← hpre.sharedBase] at hbase
        have hfit := sharedBase_lt hpre
        have haddr : (PrologueAllocation.allocAddress L g).addr < 2 ^ 32 := by
          change L.sharedBase + 222752 < 2 ^ 32
          omega
        have halign : (PrologueAllocation.allocAddress L g).addr % 4 = 0 := by
          change (L.sharedBase + 222752) % 4 = 0
          omega
        rw [tcAlloc_tmpl0 hb ha haddr halign hn hAt.2.1] at hf
        have he := congrArg Event.kind hf.1
        obtain ⟨hg, hd, hn⟩ := TcKind.resource.inj (Kind.tc.inj (hk.symm.trans he))
        exact .alloc hg hd hn
      · change kernel.code[Flow.tmemAlloc_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
        have hsub := (fires_tcAlloc_resource hf hk).1
        have hone : t.sub = 1 := hAt.2.1
        omega
      · change kernel.code[Flow.tmemRelinquish_0]? = some ins at hc
        obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
        have hb : L.block % 32 = 0 := by rw [hpre.block]
        simp only [eventTmpl, tcTmpl, hb, ↓reduceIte, pure, Except.pure, ofExec]
          at hf
        have he := congrArg Event.kind hf.1
        obtain ⟨hg, hd, hn⟩ := TcKind.resource.inj (Kind.tc.inj (hk.symm.trans he))
        exact .relinquish hg hd hn
    case wg0 d =>
      change d.site = .exit at hSite
      change kernel.code[d.site.pc]? = some ins at hc
      rw [hSite] at hc
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
      change Fires t.pc (eventTmpl Assumptions.all L g t (.tcDealloc .one (.reg 2427) (.reg 2428)))
        e o at hf
      rw [Wg0.event_exit hpre hAt hSite] at hf
      have he := congrArg Event.kind hf.1
      obtain ⟨hg, hd, hn⟩ := TcKind.resource.inj (Kind.tc.inj (hk.symm.trans he))
      have hWarp : warpOf L g = 0 := (show Wg0.Inv P L g d from hInv).exitWarp hSite
      exact .dealloc d hSite hWarp hg hd hn
    all_goals exact (show False from hSite).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ResourceEvents
