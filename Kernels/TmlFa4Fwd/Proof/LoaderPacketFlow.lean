-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCopyCommit
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Lemmas.Flow.TauFrame
public import Lemmas.Execution.EventFrameSource
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.WarpUniform

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue

noncomputable section

/-- The start of the straight-line copy instructions preceding each loader commit. -/
def copyPacketFirst : Fin 6 → Nat
  | 0 => 550
  | 1 => 810
  | 2 => 1012
  | 3 => 1247
  | 4 => 1477
  | 5 => 1640

def packetCopyOp (op : Op) : Bool :=
  match op with
  | .cpAsync .. => true
  | _ => false

def packetCopyAt (pc : Nat) : Bool :=
  (kernel.code[pc]?).any (fun ins => packetCopyOp ins.op)

def packetCapacity (pc stop : Nat) : Nat :=
  (List.range' pc (stop - pc)).countP packetCopyAt

theorem loaderPacketBounds (site : Fin 6) :
    174 ≤ copyPacketFirst site ∧ copyPacketFirst site < copyCommitPc site ∧
      copyCommitPc site < 1906 := by
  fin_cases site <;> decide

theorem loaderPacketCapacity (site : Fin 6) :
    packetCapacity (copyPacketFirst site) (copyCommitPc site) = 32 := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem packetStraight (site : Fin 6) :
    ((kernel.code.drop (copyPacketFirst site)).take
      (copyCommitPc site - copyPacketFirst site)).all
        (fun ins => schedulerFallsThrough ins.op) = true := by
  fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem packetInstruction {site : Fin 6} {pc : Nat} {ins : Instr}
    (hLo : copyPacketFirst site ≤ pc) (hHi : pc < copyCommitPc site)
    (hc : kernel.code[pc]? = some ins) : schedulerFallsThrough ins.op = true := by
  apply List.all_eq_true.mp (packetStraight site) ins
  apply List.mem_of_getElem? (i := pc - copyPacketFirst site)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
  exact hc

/-- Every backward direct branch in the loader dispatch and its role body. -/
def loaderBackEdges : List (Nat × Nat) :=
  [(287, 234), (401, 398), (514, 488), (519, 517), (537, 522), (681, 679),
   (706, 704), (732, 730), (758, 756), (784, 782), (802, 787), (956, 921),
   (962, 960), (980, 965), (1148, 1146), (1177, 1175), (1208, 1206), (1226, 1211),
   (1352, 917), (1363, 1361), (1426, 1401), (1432, 1430), (1450, 1435),
   (1613, 1611), (1631, 1616), (1743, 1396), (1847, 1794), (1868, 1866),
   (1879, 1877), (1890, 1888), (1895, 1893)]

private def loaderBackEdge (entry : Instr × Nat) : Option (Nat × Nat) :=
  match entry.1.op with
  | .bra pc _ => if pc ≤ entry.2 then some (entry.2, pc) else none
  | _ => none

private theorem loaderBackEdgeCode :
    (((kernel.code.drop 174).take (1906 - 174)).zipIdx 174).filterMap loaderBackEdge =
      loaderBackEdges := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderHasNoIndexedBranch :
    ((kernel.code.drop 174).take (1906 - 174)).all
      (fun ins => match ins.op with | .brx .. => false | _ => true) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderInstruction {pc : Nat} {ins : Instr}
    (hLo : 174 ≤ pc) (hHi : pc < 1906) (hc : kernel.code[pc]? = some ins) :
    ((kernel.code.drop 174).take (1906 - 174))[pc - 174]? = some ins := by
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
  exact hc

private theorem loaderCopyCoverageCode :
    (((kernel.code.drop 174).take (1906 - 174)).zipIdx 174).all
      (fun (ins, pc) => !packetCopyOp ins.op || (List.finRange 6).any (fun site =>
        copyPacketFirst site ≤ pc && pc < copyCommitPc site)) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- Every ordinary copy in the loader role belongs to one of the six commit intervals. -/
theorem loaderCopyPcInPacket {pc : Nat} (hLo : 174 ≤ pc) (hHi : pc < 1906)
    (hc : packetCopyAt pc = true) :
    ∃ site : Fin 6, copyPacketFirst site ≤ pc ∧ pc < copyCommitPc site := by
  cases hi : kernel.code[pc]? with
  | none => simp [packetCopyAt, hi] at hc
  | some ins =>
    have hm : (ins, pc) ∈ ((kernel.code.drop 174).take (1906 - 174)).zipIdx 174 := by
      apply List.mem_of_getElem? (i := pc - 174)
      rw [List.getElem?_zipIdx, loaderInstruction hLo hHi hi]
      simp [Nat.add_sub_of_le hLo]
    simp only [packetCopyAt, hi, Option.any_some] at hc
    have h := List.all_eq_true.mp loaderCopyCoverageCode _ hm
    simp only [hc, Bool.not_true, Bool.false_or] at h
    obtain ⟨site, _, hs⟩ := List.any_eq_true.mp h
    exact ⟨site, by simpa using hs⟩

private theorem loaderOnlyOrdinaryCopyCode :
    ((kernel.code.drop 174).take (1906 - 174)).all
      (fun ins => !bulkOp ins.op || packetCopyOp ins.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderTauCore {l : Launch} {g : Nat} {t u : TState}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906)
    (h : Tau kernel Assumptions.all l g t u) : Tau kernel [] l g t u := by
  unfold Tau at *
  rwa [loaderOutCore hLo hHi] at h

private theorem loaderEventCore {l : Launch} {g : Nat} {t : TState} {e : Event}
    {u : Option TState} (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906)
    (h : EStep kernel Assumptions.all l g t e u) : EStep kernel [] l g t e u := by
  obtain ⟨tmpl, ht, hf⟩ := h
  exact ⟨tmpl, by rwa [← loaderOutCore hLo hHi], hf⟩

/-- Every actual local backward transition in the loader follows one of the decoded edges. -/
theorem loaderTauBackEdge {l : Launch} {g : Nat} {t u : TState}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906) (hBack : u.pc ≤ t.pc)
    (h : Tau kernel Assumptions.all l g t u) : (t.pc, u.pc) ∈ loaderBackEdges := by
  have ht := loaderTauCore hLo hHi h
  obtain ⟨ins, hc⟩ := tau_core_has_code ht
  have hGet := loaderInstruction hLo hHi hc
  have hm := List.mem_of_getElem? hGet
  have hNo := List.all_eq_true.mp loaderHasNoIndexedBranch ins hm
  rcases tau_core_frame hc ht with rfl | hFrame
  · change t.pc + 1 ≤ t.pc at hBack
    omega
  · have hBra : ∃ b, ins.op = .bra u.pc b := by
      rcases hFrame.pc with he | he
      · cases hi : ins.op <;> simp_all [nextPc]
      · cases hi : ins.op <;> simp_all [BrxTarget]
    obtain ⟨b, hb⟩ := hBra
    rw [← loaderBackEdgeCode]
    apply List.mem_filterMap.mpr
    refine ⟨(ins, t.pc), ?_, by simp [loaderBackEdge, hb, hBack]⟩
    apply List.mem_of_getElem? (i := t.pc - 174)
    rw [List.getElem?_zipIdx, hGet]
    simp [Nat.add_sub_of_le hLo]

/-- Silent instructions in a copy packet fall through to the next instruction. -/
theorem packetTauNext {l : Launch} {g : Nat} {t u : TState} {site : Fin 6}
    (hLo : copyPacketFirst site ≤ t.pc) (hHi : t.pc < copyCommitPc site)
    (h : Tau kernel Assumptions.all l g t u) : u.pc = t.pc + 1 := by
  have bounds := loaderPacketBounds site
  have ht := loaderTauCore (by omega) (by omega) h
  obtain ⟨ins, hc⟩ := tau_core_has_code ht
  have hf := packetInstruction hLo hHi hc
  rcases tau_core_frame hc ht with rfl | hf'
  · rfl
  · have he := hf'.pc
    cases heq : ins.op <;> simp_all [schedulerFallsThrough, nextPc, BrxTarget]

private theorem packetCopyAdvances {l : Launch} {g : Nat} {t u : TState} {e : Event} {op : Op}
    (hCopy : packetCopyOp op = true)
    (hf : Fires t.pc (eventTmpl [] l g t op) e (some u)) : u = next t := by
  have hTmpl : CallbackFrame (· = next t) (eventTmpl [] l g t op) := by
    cases op <;> simp only [packetCopyOp, Bool.false_eq_true] at hCopy
    case cpAsync =>
      simp only [eventTmpl, cpAsyncTmpl]
      apply ofExec_frame
      repeat' first
        | exact rfl
        | apply allOk_bind; intro v
        | split
  exact callbackFrame_fires (P := (· = next t)) hTmpl hf

/-- A returning loader event advances, or stays at a site that is not an ordinary copy. -/
theorem packetEventNext {l : Launch} {g : Nat} {t u : TState} {e : Event}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906)
    (h : EStep kernel Assumptions.all l g t e (some u)) :
    u.pc = t.pc + 1 ∨ (u.pc = t.pc ∧ packetCopyAt t.pc = false) := by
  have hCore := loaderEventCore hLo hHi h
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source hCore
  cases hCopy : packetCopyOp ins.op
  · rcases (estep_return_pc hCore (fun _ _ _ hstep => execLocal_frame hstep)).2 with he | he
    · exact .inr ⟨he, by simp [packetCopyAt, hc, hCopy]⟩
    · exact .inl he
  · exact .inl (by rw [packetCopyAdvances hCopy hf]; rfl)

private theorem packetCapacityStep {pc stop : Nat} (h : pc < stop) :
    packetCapacity pc stop =
      (if packetCopyAt pc then 1 else 0) + packetCapacity (pc + 1) stop := by
  have hn : stop - pc = stop - (pc + 1) + 1 := by omega
  unfold packetCapacity
  conv_lhs => rw [hn, List.range'_succ]
  simp only [List.countP_cons]
  cases packetCopyAt pc <;> simp; omega

variable {l : Launch} {g : Nat} {t : TState}

/-- All linear copy events in the loader role originate at decoded ordinary-copy sites.
Tensor-map loads use tensor issue events. -/
theorem loaderCopyEventSite {e : Event} {u : Option TState} {s : AsyncCopy.Spec} (hLo : 174 ≤ t.pc)
    (hHi : t.pc < 1906) (h : EStep kernel Assumptions.all l g t e u) (he : e.kind = .copy s) :
    packetCopyAt t.pc = true := by
  obtain ⟨m, hm, hf⟩ := loaderEventCore hLo hHi h
  rcases out_ev hm with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · rw [hf.1] at he
    cases he
  · have hb := fires_bulk_op hf he
    have hmem := List.mem_of_getElem? (loaderInstruction hLo hHi hc)
    have hq := List.all_eq_true.mp loaderOnlyOrdinaryCopyCode ins hmem
    simpa [packetCopyAt, hc, hb] using hq

/-- A linear-copy event in the loader role is an ordinary `cp.async` issue. -/
def loaderCopyEvent (e : Event) : Bool :=
  match e.kind with | .copy _ => true | _ => false

private theorem loaderUnguardedCopies :
    ((kernel.code.drop 174).take (1906 - 174)).all
      (fun ins => !packetCopyOp ins.op || ins.guard.isNone) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem loaderCopyCode {pc : Nat} (hLo : 174 ≤ pc) (hHi : pc < 1906)
    (hc : packetCopyAt pc = true) :
    ∃ ins, kernel.code[pc]? = some ins ∧ ins.guard = none ∧ packetCopyOp ins.op = true := by
  cases hi : kernel.code[pc]? with
  | none => simp [packetCopyAt, hi] at hc
  | some ins =>
    simp only [packetCopyAt, hi, Option.any_some] at hc
    have hMem := List.mem_of_getElem? (loaderInstruction hLo hHi hi)
    have hg := List.all_eq_true.mp loaderUnguardedCopies ins hMem
    simp only [hc, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] at hg
    exact ⟨ins, rfl, hg, hc⟩

private theorem loaderTauNoCopy {l : Launch} {g : Nat} {t u : TState}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906) (ht : Tau kernel Assumptions.all l g t u) :
    packetCopyAt t.pc = false := by
  cases hc : packetCopyAt t.pc
  · rfl
  obtain ⟨ins, hCode, hGuard, hCopy⟩ := loaderCopyCode hLo hHi hc
  have hOp : ins.op.isLocal = false := by
    cases hi : ins.op <;> simp_all [packetCopyOp, Op.isLocal]
  have hInst : ins = ⟨none, ins.op⟩ := by
    cases ins
    simp_all
  rw [hInst] at hCode
  exact (tau_core_not_event hCode hOp (loaderTauCore hLo hHi ht)).elim

private theorem returningCopyOfExec {pc : Nat} {r : Exec Tmpl}
    (h : AllOk (fun t => ∀ e u, Fires pc t e (some u) → loaderCopyEvent e = true) r)
    {e : Event} {u : TState} (hf : Fires pc (ofExec r) e (some u)) :
    loaderCopyEvent e = true := by
  cases r with
  | error f => exact (Option.some_ne_none _ hf.2).elim
  | ok t => exact h e u hf

/-- At a loader copy site, the returning event is the decoded ordinary-copy issue. -/
theorem loaderReturningCopyKind {l : Launch} {g : Nat} {t u : TState} {e : Event}
    (hLo : 174 ≤ t.pc) (hHi : t.pc < 1906) (he : EStep kernel Assumptions.all l g t e (some u)) :
    loaderCopyEvent e = packetCopyAt t.pc := by
  cases hc : packetCopyAt t.pc
  · cases hk : e.kind <;> simp [loaderCopyEvent, hk]
    case copy =>
      have h := loaderCopyEventSite hLo hHi he hk
      rw [hc] at h
      cases h
  obtain ⟨ins, hCode, _, hCopy⟩ := loaderCopyCode hLo hHi hc
  obtain ⟨j, hj, _, hFires⟩ := estep_event_source (loaderEventCore hLo hHi he)
  rw [hCode] at hj
  obtain rfl := Option.some.inj hj
  cases hi : ins.op <;> simp only [hi, packetCopyOp, Bool.false_eq_true] at hCopy
  rw [hi] at hFires
  simp only [eventTmpl, cpAsyncTmpl] at hFires
  apply returningCopyOfExec _ hFires
  repeat' first
    | apply allOk_bind; intro _
    | apply allOk_ite
    | (intro f v hf; rw [hf.1]; rfl)

private theorem packetCopyCountAtCommit {events : List Event} {visits : List Visit} {site : Fin 6}
    (hw : Walk kernel Assumptions.all l g t events visits) (hLo : copyPacketFirst site ≤ t.pc)
    (hReach : ∃ v ∈ visits, v.pc = copyCommitPc site) :
    (((visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev).countP
      loaderCopyEvent) = packetCapacity t.pc (copyCommitPc site) := by
  have bounds := loaderPacketBounds site
  have past {s : TState} {tail : List Visit} (ev : Option Event)
      (hp : ¬ s.pc < copyCommitPc site) :
      (((visit kernel l g s ev :: tail).takeWhile (fun v => v.pc < copyCommitPc site)).filterMap
        Visit.ev).countP loaderCopyEvent = packetCapacity s.pc (copyCommitPc site) := by
    simp [packetCapacity, visit, hp, show copyCommitPc site - s.pc = 0 by omega]
  have later {s : TState} {tail : List Visit} (ev : Option Event)
      (hp : s.pc < copyCommitPc site)
      (h : ∃ v ∈ visit kernel l g s ev :: tail, v.pc = copyCommitPc site) :
      ∃ v ∈ tail, v.pc = copyCommitPc site := by
    obtain ⟨v, hv, hc⟩ := h
    rcases List.mem_cons.mp hv with rfl | hm
    · exact (hp.ne ((visit_pc _ _ _ _ _).symm.trans hc)).elim
    · exact ⟨v, hm, hc⟩
  induction hw with
  | stop => simp at hReach
  | @last s e _ =>
    by_cases hHi : s.pc < copyCommitPc site
    · simpa using later (some e) hHi hReach
    · exact past (some e) hHi
  | @tau s u es vs ht hw ih =>
    by_cases hHi : s.pc < copyCommitPc site
    · have hn := packetTauNext hLo hHi ht
      have hCopy := loaderTauNoCopy (by omega) (by omega) ht
      have hTail := ih (by omega) (later none hHi hReach)
      rw [hn] at hTail
      simpa [visit, hHi, packetCapacityStep hHi, hCopy] using hTail
    · exact past none hHi
  | @ev s u e es vs he hw ih =>
    by_cases hHi : s.pc < copyCommitPc site
    · have hKind := loaderReturningCopyKind (by omega) (by omega) he
      have hContinue := later (some e) hHi hReach
      rcases packetEventNext (by omega) (by omega) he with hn | ⟨hn, hCopy⟩
      · have hTail := ih (by omega) hContinue
        rw [hn] at hTail
        simp [visit, hHi, List.countP_cons, hKind, hTail, packetCapacityStep hHi, Nat.add_comm]
      · have hTail := ih (by omega) hContinue
        rw [hn] at hTail
        simpa [visit, hHi, hKind, hCopy] using hTail
    · exact past (some e) hHi

/-- A finite walk reaching any of the six commit PCs from its packet entry issued all
32 ordinary copies. This counts events rather than visits to the copy instructions. -/
theorem loaderPacketCopiesAtCommit {events : List Event} {visits : List Visit} {site : Fin 6}
    (hw : Walk kernel Assumptions.all l g t events visits) (hStart : t.pc = copyPacketFirst site)
    (hReach : ∃ v ∈ visits, v.pc = copyCommitPc site) :
    (((visits.takeWhile (fun v => v.pc < copyCommitPc site)).filterMap Visit.ev).countP
      loaderCopyEvent) = 32 := by
  have h := packetCopyCountAtCommit hw hStart.ge hReach
  rwa [hStart, loaderPacketCapacity] at h

end
end PTX.Kernels.TmlFa4Fwd.Loader
