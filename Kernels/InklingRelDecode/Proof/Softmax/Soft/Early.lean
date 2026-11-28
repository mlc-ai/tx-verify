-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.Step

@[expose] public section

/-! # The states before the softmax

The startup's and the prologue's states of the value thread: they only follow their own and
their pcs are not those of the score poll and of the shuffle of the maxima. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat}

/-- The states before the softmax: the startup and the prologue. -/
public def Early (s : (threadD Q L g).D) : Prop :=
  (∃ b, s.1 = .inl b) ∨ ∃ (w : Value) (d : Prologue.Data.D), s.1 = .inr ⟨.inl (.prologue w), .inl d⟩

public theorem early_pred {s s' : (threadD Q L g).D} {e : Event}
    (h : (threadD Q L g).next s e = some (some s')) (hs' : Early s') : Early s := by
  obtain ⟨a, b⟩ := Code.counted_next_some h
  obtain ⟨s0, cnt⟩ := s
  rcases s0 with start | ⟨r, old⟩
  · exact .inl ⟨_, rfl⟩
  change ((Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e).map _ = _ at a
  rcases hn : (Code.withStubs (fragD Q L g) Startup.Entry.pc r).next old e with _ | _ | t <;>
    rw [hn] at a <;> try solve | cases a
  simp only [Option.map_some, Option.some.injEq] at a
  obtain ⟨x, n'⟩ := s'
  cases a
  rcases hs' with ⟨b, hb⟩ | ⟨w, d, hd⟩
  · cases hb
  · cases hd
    rcases old with old | ⟨ent, old⟩
    · exact .inr ⟨w, old, rfl⟩
    · change ((softDCode ent L g).next old e).map _ = _ at hn
      rcases hv : (softDCode ent L g).next old e with _ | _ | dn <;> rw [hv] at hn <;> cases hn

private theorem startup_far (st : Startup.Site) : st.pc ≠ 1257 ∧ st.pc ≠ 1838 := by
  cases st <;> first | decide | (rename_i r; cases r <;> decide)

public theorem early_pc {s : (threadD Q L g).D} (h : Early s) :
    (threadD Q L g).pc s ≠ 1257 ∧ (threadD Q L g).pc s ≠ 1838 := by
  obtain ⟨s0, cnt⟩ := s
  rcases h with ⟨b, hb⟩ | ⟨w, d, hd⟩
  · change s0 = _ at hb
    subst hb
    exact startup_far _
  · change s0 = _ at hd
    subst hd
    have := d.c.site.pc_range
    change d.c.site.pc ≠ 1257 ∧ d.c.site.pc ≠ 1838
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
