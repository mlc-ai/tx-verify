-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame

noncomputable section

private def afterLseCode (lo : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op || match i.op with | .ret => true | _ => false) &&
    !(Softmax.scoreEventWrites i.op).contains 0 &&
    match i.op with
    | .bra dst _ => lo ≤ dst
    | .brx .. => false
    | _ => true

private theorem afterLseDecoded {lo pc : Nat} {i : Instr}
    (hCut : lo = 9074 ∨ lo = 9083 ∨ lo = 9201) (hLo : lo ≤ pc)
    (hc : kernel.code[pc]? = some i) : afterLseCode lo i = true := by
  have hLen : pc < 9206 := by
    have h := (List.getElem?_eq_some_iff.mp hc).1
    rwa [Decoded.code_length] at h
  have hAll : ((kernel.code.drop lo).take (9206 - lo)).all (afterLseCode lo) = true := by
    rcases hCut with rfl | rfl | rfl
    all_goals set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - lo)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]

/-- The request drain and terminal suffix cannot return to earlier correction events. -/
theorem noEarlierCorrectionAfterStage {l : Launch} {g lo : Nat} {s : TState} {target : Event}
    {es : List Event} {visits : List Visit} (hCut : lo = 9074 ∨ lo = 9083 ∨ lo = 9201)
    (hp : target.pc < lo) (hs : lo ≤ s.pc)
    (hSub : s.sub ≤ 3) (hw : Walk kernel Assumptions.all l g s es visits) :
    target ∉ es := by
  induction hw with
  | stop => simp
  | @tau s u es vs ht hW ih =>
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hT⟩ := correctionTauFrame hOff ht
    have hCode := afterLseDecoded hCut hs hc
    simp only [afterLseCode, Bool.and_eq_true] at hCode
    rcases hT with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact ih (by change lo ≤ s.pc + 1; omega) (Nat.zero_le _)
    · apply ih _ (hF.sub ▸ hSub)
      have hPc := hF.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst aligned => rw [hPc]; simpa [ho] using hCode.2
      case brx => simp [ho] at hCode
      all_goals omega
  | @ev s u e es vs he hW ih =>
    intro he'
    rcases List.mem_cons.mp he' with he' | he'
    · have h := estep_source_pc he
      rw [← he'] at h
      change target.pc = s.pc at h
      omega
    · obtain ⟨i, hc, hl, hf⟩ := estep_event_source he
      have hCode := afterLseDecoded hCut hs hc
      simp only [afterLseCode, Bool.and_eq_true, Bool.or_eq_true, hl,
        Bool.false_eq_true, false_or] at hCode
      rcases hCode.1.1 with h | h
      · have hKeep : 0 ∉ Softmax.scoreEventWrites i.op := by simpa using hCode.1.2
        obtain ⟨hP, _⟩ := correctionEventProgress (r := 0) hc h hSub hKeep he
        have h' : lo ≤ u.pc := hP.pc.elim (fun h => by omega) (fun h => by omega)
        exact ih h' hP.sub he'
      · have hRet : i.op = .ret := by cases ho : i.op <;> simp_all
        rw [hRet] at hf
        cases hf.2
  | @last s e he =>
    intro h
    have h' := estep_source_pc he
    rw [(List.mem_singleton.mp h).symm] at h'
    change target.pc = s.pc at h'
    omega

/-- The request drain and terminal suffix cannot return to an LSE store site. -/
theorem noEarlierLseAfterStage {l : Launch} {g lo pc : Nat} {s : TState} {a : Acc} {bs : List Byte}
    {es : List Event} {visits : List Visit} (hCut : lo = 9074 ∨ lo = 9083)
    (hp : pc < lo) (hs : lo ≤ s.pc)
    (hSub : s.sub ≤ 3) (hw : Walk kernel Assumptions.all l g s es visits) :
    ⟨pc, .wr a bs⟩ ∉ es :=
  noEarlierCorrectionAfterStage (hCut.imp_right Or.inl) hp hs hSub hw

/-- The request drain and terminal suffix cannot return to an LSE store site. -/
theorem noLseAfterTile {l : Launch} {g pc : Nat} {s : TState} {a : Acc} {bs : List Byte}
    {es : List Event} {visits : List Visit} (hp : pc < 9083) (hs : 9083 ≤ s.pc)
    (hSub : s.sub ≤ 3) (hw : Walk kernel Assumptions.all l g s es visits) :
    ⟨pc, .wr a bs⟩ ∉ es :=
  noEarlierLseAfterStage (.inr rfl) hp hs hSub hw

end
end PTX.Kernels.TmlFa4Fwd.Correction
