-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Lemmas.Register.RegisterFrame

public section

/-! # The kernel assumptions preserve the instruction's local frame -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Proof PTX.Flow Assumptions

private theorem frame_set {op : Op} {t : TState} {d : Nat} {v : Value}
    (hpc : nextPc op t.pc = t.pc + 1) (hd : d ∈ writesRegs op) :
    LocalFrame op t (PTX.next (setReg t d v)) := by
  refine ⟨.inl hpc.symm, rfl, rfl, rfl, ?_⟩
  intro r hr
  exact Function.update_of_ne (by intro h; subst h; exact hr hd) _ _

private theorem frame_next {op : Op} {t : TState}
    (hpc : nextPc op t.pc = t.pc + 1) : LocalFrame op t (PTX.next t) :=
  ⟨.inl hpc.symm, rfl, rfl, rfl, fun _ _ => rfl⟩

private def peerDst : PeerPack → Nat
  | .extend d _ | .upper d _ | .merge d _ _ _ => d

private theorem peer_run {t u : TState} {p : PeerPack} (h : p.run t = some u) :
    ∃ v, u = PTX.next (setReg t (peerDst p) v) := by
  cases p
  case extend d s =>
    simp only [PeerPack.run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    split_ifs at h
    exact ⟨_, (Option.some.inj h).symm⟩
  case upper d s =>
    simp only [PeerPack.run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    cases v <;> try contradiction
    case pair w z =>
      change (if z = peerPackZero ∧ scoreHalf w then _ else none) = _ at h
      split_ifs at h
      exact ⟨_, (Option.some.inj h).symm⟩
  case merge d lo hi order =>
    simp only [PeerPack.run, bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, -, h⟩ := h
    cases v <;> try contradiction
    case pair vl zl =>
      obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
      cases v <;> try contradiction
      case pair zh vh =>
        change (if zl = peerPackZero ∧ zh = peerPackZero ∧ scoreHalf vl ∧ scoreHalf vh then
          _ else none) = _ at h
        split_ifs at h
        exact ⟨_, (Option.some.inj h).symm⟩

private theorem peer_frame {t u : TState} {op : Op}
    (h : peerPackRule t op = some (.ok u)) : LocalFrame op t u := by
  unfold peerPackRule at h
  repeat' split at h
  all_goals try contradiction
  all_goals simp only [Option.map_eq_some_iff, Except.ok.injEq] at h
  all_goals obtain ⟨out, hout, rfl⟩ := h
  all_goals obtain ⟨v, rfl⟩ := peer_run hout
  all_goals apply frame_set rfl
  all_goals simp_all [writesRegs, peerDst]

private theorem dead_pack_frame {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : deadPackRule L g t op = some (.ok u)) : LocalFrame op t u := by
  unfold deadPackRule at h
  split at h
  · split_ifs at h
    simp only [Option.some.injEq, bind, Except.bind] at h
    repeat' split at h
    all_goals cases h
    all_goals apply frame_set rfl
    all_goals simp [writesRegs]
  · cases h

private theorem int_src_frame {t u : TState} {i : IntInstr} {src : List Opnd}
    (h : LocalFrame (.int { i with srcs := src }) t u) : LocalFrame (.int i) t u :=
  ⟨h.pc, h.sub, h.acc, h.fault, h.regs⟩

private theorem swizzle_frame {t u : TState} {i : IntInstr}
    (h : LocalFrame (.int i) t u) : LocalFrame (.int i) t (keepSwizzleTag t i u) := by
  unfold keepSwizzleTag
  split
  · rename_i _ _ _ _ dst _ _ _ _ hdst _
    split
    · refine ⟨h.pc, h.sub, h.acc, h.fault, ?_⟩
      intro r hr
      have hn : r ≠ dst := by intro he; subst r; apply hr; simp [writesRegs, hdst]
      exact (Function.update_of_ne hn _ _).trans (h.regs r hr)
    · exact h
  · exact h

private theorem shared_bits_frame {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : sharedBits.localRule L g t op = some (.ok u)) : LocalFrame op t u := by
  simp only [sharedBits] at h
  split at h
  · split at h
    · next i =>
      split at h
      · injection h with hu
        cases hr : execInt L g t { i with srcs := i.srcs.map (sharedPtrBits t) } with
        | error f => rw [hr] at hu; cases hu
        | ok w =>
          rw [hr] at hu
          have hs : keepSwizzleTag t i w = u := Except.ok.inj hu
          rw [← hs]
          exact swizzle_frame (int_src_frame (execInt_frame hr))
      · exact int_src_frame (execInt_frame (Option.some.inj h))
    · cases h
  · cases hd : deadPackRule L g t op with
    | none => exact peer_frame (by simpa only [hd, Option.orElse_none] using h)
    | some out =>
      rw [hd, Option.orElse_some] at h
      exact dead_pack_frame (hd.trans h)

private theorem numeric_set_frame {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : mulBf16x2.localRule L g t op = some (.ok u) ∨
      cvtBf16x2.localRule L g t op = some (.ok u) ∨
      cvtUe8m0.localRule L g t op = some (.ok u) ∨ lg2Exact.localRule L g t op = some (.ok u)) :
    LocalFrame op t u := by
  rcases h with h | h | h | h
  all_goals simp only [mulBf16x2, cvtBf16x2, cvtUe8m0, lg2Exact] at h
  all_goals repeat' split at h
  all_goals cases h
  all_goals apply frame_set rfl
  all_goals simp_all [writesRegs]

private theorem parameter_frame {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : paramPointers.localRule L g t op = some (.ok u)) : LocalFrame op t u := by
  simp only [paramPointers] at h
  repeat' split at h
  all_goals cases h
  all_goals first | exact frame_next rfl | (apply frame_set rfl; simp [writesRegs])

/-- Every local rule used by the frozen code advances as its instruction and preserves its frame. -/
theorem flashmla_rules_frame : RulesFrame Assumptions.all := by
  intro a ha L g t op u h
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idealReal_frame h
  · exact approxExact_frame h
  · exact numeric_set_frame (.inl h)
  · exact numeric_set_frame (.inr (.inl h))
  · exact numeric_set_frame (.inr (.inr (.inl h)))
  · exact numeric_set_frame (.inr (.inr (.inr h)))
  · cases h
  · exact parameter_frame h
  · cases h
  · exact shared_bits_frame h
  · cases h

/-- The kernel's local execution uses the register and control frame of the instruction. -/
theorem local_frame {L : Launch} {g : Nat} {t u : TState} {op : Op}
    (h : execLocalA Assumptions.all L g t op = .ok u) : LocalFrame op t u :=
  execLocalA_frame flashmla_rules_frame h (fun a ha _ _ s _ => asms_segment_free s a ha)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
