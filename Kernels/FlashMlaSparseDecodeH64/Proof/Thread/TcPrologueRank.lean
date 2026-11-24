-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingGateEvents

@[expose] public section

/-! # Tensor Memory collective ranks in the launch prologue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcPrologueRank

open PTX PTX.Flow

/-- Warp zero runs the two allocator collectives and all other warps join at the gate. -/
def setup (L : Launch) (g : Nat) : Nat := if warpOf L g = 0 then 2 else 0

/-- The number of Tensor Memory collectives preceding a prologue site. -/
def rank (L : Launch) (g : Nat) : Proof.Site → Nat
  | .allocStore | .allocRead | .relinquish => 1
  | .barrier | .handoff _ => setup L g
  | _ => 0

/-- The initialization and allocator paths are confined to warp zero. -/
def InScope (L : Launch) (g : Nat) : Proof.Site → Prop
  | .elect0 | .elect1 | .init _ | .fence | .alloc | .allocStore | .allocRead | .relinquish =>
    warpOf L g = 0
  | _ => True

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

private theorem relinquish_kind {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue .relinquish)) e o) :
    e.kind = .tc (.resource .one none .relinquish) := by
  obtain ⟨_, _, he⟩ := RingGateEvents.fired_at_code hf Flow.code_tmemRelinquish_0
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  simp only [eventTmpl, tcTmpl, hb, ↓reduceIte, pure, Except.pure, ofExec] at he
  exact congrArg Event.kind he.1

private theorem no_collective {s : Proof.Site} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o)
    (ha : s ≠ .alloc) (hr : s ≠ .relinquish) : isTcColl e = false := by
  cases hk : isTcColl e with
  | false => rfl
  | true =>
    rcases TcCollectiveSites.of_fired hpre hf hk with ⟨_, h, _⟩ | ⟨_, _, _, _, hs⟩
    · cases h
    · cases hs
      · exact (ha rfl).elim
      · exact (hr rfl).elim

private theorem resource_collective {e : Event} {grp : CtaGroup} {dst : Option Loc}
    {req : Tmem.Request} (he : e.kind = .tc (.resource grp dst req)) : isTcColl e = true := by
  cases e
  simp_all [isTcColl]

/-- Each live prologue step increments the ordinal at exactly the two resource requests. -/
theorem step {s s' : Proof.Site} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some (.prologue s)) e o)
    (hi : InScope L g s) (hn : Proof.next L g s e = some (some s')) :
    InScope L g s' ∧ rank L g s' = rank L g s + (isTcColl e).toNat := by
  cases s
  case alloc =>
    simp only [Proof.next] at hn
    split at hn
    · rename_i grp dst n he
      have hw : warpOf L g = 0 := hi
      split_ifs at hn <;> cases hn <;> simp [InScope, rank, hw, resource_collective he]
    · cases hn
  case relinquish =>
    change some (some Proof.Site.barrier) = some (some s') at hn
    cases hn
    simp [rank, setup, InScope, show warpOf L g = 0 from hi,
      resource_collective (relinquish_kind hpre hf)]
  all_goals have he := no_collective hpre hf (by simp) (by simp)
  all_goals simp only [Proof.next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [InScope, rank, setup]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TcPrologueRank
