-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalIndex
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader (RingShape)

noncomputable section

/-- Each indexed stack site scales its loop entry and adds one immutable array root. -/
structure ScalarSite where
  loop : TwoEntryLoop
  scalePc : Nat
  offsetReg : Nat
  addPc : Nat
  addressReg : Nat
  accessPc : Nat
  array : Fin 4

def ScalarSite.word (s : ScalarSite) : Nat :=
  if s.array.val < 2 then 8 else 4

def ScalarSite.shift (s : ScalarSite) : Nat :=
  if s.array.val < 2 then 3 else 2

def storeWords (b : TwoEntryLoop) (start off page row rowAccess : Nat) : List ScalarSite :=
  [⟨b, start, off, start + 1, page, start + 2, 3⟩,
   ⟨b, start, off, start + 3, row, rowAccess, 2⟩]

def loadWordsSavePointer (b : TwoEntryLoop) (start off page row offPtr ptr : Nat)
    (array : Fin 4) : List ScalarSite :=
  [⟨b, start, off, start + 1, page, start + 2, 3⟩,
   ⟨b, start, off, start + 3, row, start + 4, 2⟩,
   ⟨b, start + 9, offPtr, start + 10, ptr, start + 11, array⟩]

def scalarSites : List ScalarSite :=
  storeWords ⟨486, 512, 514, 7172, false⟩ 504 7532 7533 7534 511 ++
  storeWords ⟨919, 954, 956, 7175, false⟩ 947 7651 7652 7653 953 ++
  storeWords ⟨1399, 1424, 1426, 7182, false⟩ 1417 7766 7767 7768 1423 ++
  loadWordsSavePointer ⟨520, 535, 537, 9535, true⟩ 523 7535 7536 7538 7544 7545 0 ++
  loadWordsSavePointer ⟨785, 800, 802, 9536, true⟩ 788 7599 7600 7602 7608 7609 0 ++
  loadWordsSavePointer ⟨963, 978, 980, 9537, true⟩ 966 7654 7655 7657 7663 7664 1 ++
  loadWordsSavePointer ⟨1209, 1224, 1226, 9538, true⟩ 1212 7708 7709 7711 7717 7718 0 ++
  loadWordsSavePointer ⟨1433, 1448, 1450, 9539, true⟩ 1436 7769 7770 7772 7778 7779 1 ++
  loadWordsSavePointer ⟨1614, 1629, 1631, 9540, true⟩ 1617 7813 7814 7816 7822 7823 0

/-- The two operands in the stack address calculation: scaled entry, then rooted address. -/
inductive AddressStage
  | offset
  | address

def ScalarSite.birth (s : ScalarSite) : AddressStage → Nat
  | .offset => s.scalePc
  | .address => s.addPc

def ScalarSite.last (s : ScalarSite) : AddressStage → Nat
  | .offset => s.addPc
  | .address => s.accessPc

def ScalarSite.dest (s : ScalarSite) : AddressStage → Nat
  | .offset => s.offsetReg
  | .address => s.addressReg

def ScalarSite.value (l : Launch) (s : ScalarSite) (entry : Fin 2) : AddressStage → Value
  | .offset => b64 (s.word * entry.val)
  | .address => b64 (l.localBase + kvLocalOffset s.array entry)

def ScalarSite.active (s : ScalarSite) (phase : AddressStage) (pc : Nat) : Prop :=
  s.birth phase < pc ∧ pc ≤ s.last phase

instance (s : ScalarSite) (phase : AddressStage) (pc : Nat) :
    Decidable (s.active phase pc) :=
  inferInstanceAs (Decidable (s.birth phase < pc ∧ pc ≤ s.last phase))

def ScalarSite.calculation (s : ScalarSite) : AddressStage → IntInstr
  | .offset =>
    if s.loop.wide then
      ⟨.shl, .int .b 64, false, [some s.offsetReg], [.reg s.loop.reg, .imm s.shift]⟩
    else
      ⟨.mul .wide, .int .u 32, false, [some s.offsetReg], [.reg s.loop.reg, .imm 4]⟩
  | .address =>
    ⟨.add, .int .s 64, false, [some s.addressReg], [.reg (7292 + s.array.val), .reg s.offsetReg]⟩

private def checkSite (pc : Nat) (i : Instr) (s : ScalarSite) (phase : AddressStage) : Bool :=
  (if pc == s.birth phase then i.guard.isNone &&
      (match i.op with | .int math => decide (math = s.calculation phase) | _ => false)
   else !decide (s.active phase pc) || !(Loader.loaderRingWrites i.op).contains (s.dest phase)) &&
  (!decide (pc = s.birth phase ∨ s.active phase pc) ||
    !(Loader.loaderRingWrites i.op).contains s.loop.reg) &&
  (match i.op with
  | .bra target _ => !decide (s.active phase target) || decide (s.active phase pc)
  | .brx .. => false
  | _ => true)

private theorem siteCheckAt {pc : Nat} {i : Instr} (hLo : 174 ≤ pc) (hHi : pc < 1901)
    (hc : kernel.code[pc]? = some i) {s : ScalarSite} (hs : s ∈ scalarSites)
    (phase : AddressStage) : checkSite pc i s phase = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAudit : code.all (fun (ins, pos) =>
      scalarSites.all (fun site =>
        checkSite pos ins site .offset && checkSite pos ins site .address)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : (i, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - 174)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  have h := List.all_eq_true.mp (List.all_eq_true.mp hAudit (i, pc) hm) s hs
  cases phase
  · exact (Bool.and_eq_true_iff.mp h).1
  · exact (Bool.and_eq_true_iff.mp h).2

private theorem invariantSite {s : ScalarSite} (hs : s ∈ scalarSites) :
    s.loop ∈ scratchLoops ∧ s.loop.active s.scalePc ∧ s.active .offset s.addPc ∧
      (!s.loop.wide → s.word = 4) ∧ 174 ≤ s.scalePc ∧ 174 ≤ s.addPc ∧
      s.active .address s.accessPc := by
  let valid := fun q : ScalarSite => decide (q.loop ∈ scratchLoops ∧
    q.loop.active q.scalePc ∧ q.active .offset q.addPc ∧ (!q.loop.wide → q.word = 4) ∧
    174 ≤ q.scalePc ∧ 174 ≤ q.addPc ∧ q.active .address q.accessPc)
  have checked : scalarSites.all valid = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp checked s hs)

def addressInvariant (l : Launch) (t : TState) : Prop :=
  ∀ s ∈ scalarSites, ∀ phase, s.active phase t.pc →
    ∃ entry, t.regs s.loop.reg = some (s.loop.value entry) ∧
      t.regs (s.dest phase) = some (s.value l entry phase)

theorem addressInitial {l : Launch} {t : TState} (ht : t.pc = 174) :
    addressInvariant l t := by
  intro s hs phase hp
  obtain ⟨_, _, _, _, hScale, hAdd, _⟩ := invariantSite hs
  cases phase <;> simp [ScalarSite.active, ScalarSite.birth, ht, not_lt_of_ge hScale,
    not_lt_of_ge hAdd] at hp

private theorem checkedCalculation {s : ScalarSite} {phase : AddressStage} {i : Instr}
    (hc : checkSite (s.birth phase) i s phase = true) :
    i = ⟨none, .int (s.calculation phase)⟩ := by
  obtain ⟨guard, op⟩ := i
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1
  simp only [beq_self_eq_true, ↓reduceIte] at h
  obtain ⟨hg, ho⟩ := Bool.and_eq_true_iff.mp h
  have hNone : guard = none := Option.isNone_iff_eq_none.mp hg
  subst guard
  cases op <;> simp_all

private theorem calculationLocal (s : ScalarSite) (phase : AddressStage) :
    (Op.int (s.calculation phase)).isLocal = true := by
  cases phase
  · cases h : s.loop.wide <;> simp only [ScalarSite.calculation, h, Bool.false_eq_true, ↓reduceIte]
    all_goals rfl
  · rfl

private theorem calculateStackReg {l : Launch} {g : Nat} {t : TState} {s : ScalarSite}
    {warp : Fin 2} (hRoots : Holds t.regs (roots l warp))
    {phase : AddressStage} {entry : Fin 2}
    (hStack : l.localBase + 128 ≤ 2 ^ 32)
    (hSize : !s.loop.wide → s.word = 4)
    (hIndex : phase = .offset → t.regs s.loop.reg = some (s.loop.value entry))
    (hOffset : phase = .address → t.regs s.offsetReg = some (s.value l entry .offset)) :
    execLocalA [] l g t (.int (s.calculation phase)) =
      .ok (next (setReg t (s.dest phase) (s.value l entry phase))) := by
  have hRule : (s.calculation phase).rule = some .threadInt := by
    cases phase
    · cases h : s.loop.wide <;>
        simp only [ScalarSite.calculation, h, Bool.false_eq_true, ↓reduceIte]
      all_goals rfl
    · rfl
  rw [execLocalA_nil, execLocal_int hRule]
  cases phase with
  | offset =>
    have hi := hIndex rfl
    cases hw : s.loop.wide
    · have hW := hSize (by simp [hw])
      fin_cases entry <;> simp [ScalarSite.calculation, ScalarSite.dest, ScalarSite.value,
        TwoEntryLoop.value, hW, hw, execInt, hi, DType.width, readBits, readReg,
        b32, b64, bind, Except.bind, pure, Except.pure]
      all_goals rfl
    · by_cases ha : s.array.val < 2 <;>
        fin_cases entry <;> simp [ScalarSite.calculation, ScalarSite.dest, ScalarSite.value,
          ScalarSite.shift, ScalarSite.word, TwoEntryLoop.value, hw, ha, execInt, hi,
          DType.width, readBits, readReg, b64, bind, Except.bind, pure, Except.pure]
      all_goals rfl
  | address =>
    have hReg : t.regs (7292 + s.array.val) = some (b64 (l.localBase + 32 * s.array.val)) := by
      apply holds_mem hRoots
      obtain ⟨_, _, _, _, _, _, array⟩ := s
      fin_cases array <;> simp [roots]
    have hb := hOffset rfl
    have hA := s.array.isLt
    have he := entry.isLt
    have hWord : s.word ≤ 8 := by simp only [ScalarSite.word]; split <;> decide
    have hBase : l.localBase + 32 * s.array.val < 2 ^ 64 := by omega
    have hOff : s.word * entry.val < 2 ^ 64 := by
      interval_cases entry.val
      · simp
      · simpa only [Nat.mul_one] using (show s.word < 2 ^ 64 by omega)
    have hSum : l.localBase + 32 * s.array.val + s.word * entry.val < 2 ^ 64 := by
      interval_cases entry.val <;> simp only [Nat.mul_zero, Nat.mul_one] <;> omega
    simp only [ScalarSite.dest, ScalarSite.calculation, execInt, DType.width, readValue, readBits,
      readReg, hReg, ScalarSite.value, b64, bind, Except.bind, pure, Except.pure]
    have hOffReg : t.regs s.offsetReg =
        some (Value.bits 64 (BitVec.ofNat 64 (s.word * entry.val))) := hb
    rw [hOffReg]
    simp only [truncBits_ofNat hBase (by decide), truncBits_ofNat hOff (by decide)]
    change (Except.ok (next (setReg t s.addressReg (.bits 64 (truncBits 64
      (BitVec.ofNat 64 (l.localBase + 32 * s.array.val) +
        BitVec.ofNat 64 (s.word * entry.val)))))) =
        Except.ok (next (setReg t s.addressReg (.bits 64
          (BitVec.ofNat 64 (l.localBase + kvLocalOffset s.array entry))))))
    rw [← BitVec.ofNat_add, truncBits_ofNat hSum (by decide)]
    simp only [kvLocalOffset, ScalarSite.word, Nat.add_assoc]

/-- The actual loader can enter a live address interval only through its checked definition. -/
theorem addressStep {l : Launch} {g : Nat} {warp : Fin 2} {t u : TState}
    {ev : Option Event} (hLo : 174 ≤ t.pc) (hHi : t.pc < 1901)
    (hStack : l.localBase + 128 ≤ 2 ^ 32) (hRoots : Holds t.regs (roots l warp))
    (hIndex : indexInvariant t) (hInv : addressInvariant l t)
    (hStep : WStep kernel Assumptions.all l g t ev u) : addressInvariant l u := by
  intro site hs stage hActive
  have hFall (h : u.pc = t.pc + 1) : t.pc = site.birth stage ∨ site.active stage t.pc := by
    unfold ScalarSite.active at hActive ⊢
    omega
  have hKeepsIndex (hLive : t.pc = site.birth stage ∨ site.active stage t.pc) :
      u.regs site.loop.reg = t.regs site.loop.reg := by
    apply Loader.loaderPipelineStepRegs hLo hHi _ hStep
    intro ins hc
    have h := (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (siteCheckAt hLo hHi hc hs stage)).1).2
    simpa [checkSite, hLive] using h
  have hPreserve (hDef : t.pc ≠ site.birth stage) (hLive : site.active stage t.pc) :
      ∃ entry, u.regs site.loop.reg = some (site.loop.value entry) ∧
        u.regs (site.dest stage) = some (site.value l entry stage) := by
    obtain ⟨entry, hIdx, hEntry⟩ := hInv site hs stage hLive
    refine ⟨entry, (hKeepsIndex (.inr hLive)).trans hIdx,
      (Loader.loaderPipelineStepRegs hLo hHi ?_ hStep).trans hEntry⟩
    intro i hc
    have h := (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (siteCheckAt hLo hHi hc hs stage)).1).1
    simpa [checkSite, hDef, hLive] using h
  rcases hStep with ⟨rfl, ht⟩ | ⟨event, rfl, he⟩
  · have ht' : Tau kernel [] l g t u := by
      unfold Tau at ht ⊢
      rwa [← Loader.loaderOutCore hLo (by omega)]
    obtain ⟨ins, hc, hf, _⟩ := Softmax.tauScoreSource ht
    have hCert := siteCheckAt hLo hHi hc hs stage
    by_cases hDef : t.pc = site.birth stage
    · have hk := hKeepsIndex (.inl hDef)
      have hi : ins = ⟨none, .int (site.calculation stage)⟩ :=
        checkedCalculation (hDef ▸ hCert)
      rw [hi] at hc
      obtain ⟨hLoop, hScale, hAdd, hWord, _, _, _⟩ := invariantSite hs
      have computed (entry : Fin 2)
          (hEntry : stage = .offset → t.regs site.loop.reg = some (site.loop.value entry))
          (hOffset : stage = .address →
            t.regs site.offsetReg = some (site.value l entry .offset)) :
          u.regs (site.dest stage) = some (site.value l entry stage) := by
        have hExec := calculateStackReg (g := g) hRoots hStack hWord hEntry hOffset
        have hLocal := calculationLocal site stage
        simp only [Tau, out, hf, hc, guardHolds, pure, Except.pure, hLocal, ↓reduceIte,
          hExec] at ht'
        obtain rfl := Out.tau.inj ht'.symm
        exact Function.update_self _ _ _
      cases stage with
      | offset =>
        obtain ⟨entry, hEntry⟩ := hIndex site.loop hLoop (hDef.symm ▸ hScale)
        exact ⟨entry, hk.trans hEntry, computed entry (fun _ => hEntry) (fun h => by cases h)⟩
      | address =>
        obtain ⟨entry, hIdx, hEntry⟩ := hInv site hs .offset (hDef.symm ▸ hAdd)
        exact ⟨entry, hk.trans hIdx, computed entry (fun h => by cases h) (fun _ => hEntry)⟩
    apply hPreserve hDef
    have hBranch := (Bool.and_eq_true_iff.mp hCert).2
    rcases tau_core_frame hc ht' with rfl | hFrame
    · exact (hFall rfl).resolve_left hDef
    · have hPc := hFrame.pc
      cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra target uni =>
        rw [hPc] at hActive
        simpa [ho, hActive] using hBranch
      case brx => simp [ho] at hBranch
      all_goals exact (hFall hPc).resolve_left hDef
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source he
    have hDef : t.pc ≠ site.birth stage := by
      intro hEq
      have hCert := siteCheckAt hLo hHi hc hs stage
      have hi : ins = ⟨none, .int (site.calculation stage)⟩ :=
        checkedCalculation (hEq ▸ hCert)
      rw [hi, show (Instr.mk none (.int (site.calculation stage))).op =
        .int (site.calculation stage) from rfl, calculationLocal] at hLocal
      cases hLocal
    apply hPreserve hDef
    have he' : EStep kernel [] l g t event (some u) := by
      obtain ⟨tmpl, ho, hf⟩ := he
      exact ⟨tmpl, by rwa [← Loader.loaderOutCore hLo (by omega)], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact (hFall h).resolve_left hDef

/-- The actual scalar scratch access carries one of the two aligned stack-cell addresses. -/
theorem eventScalarAddress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hLo : 506 ≤ e.pc) (hHi : e.pc < 1901)
    (site : ScalarSite) (hs : site ∈ scalarSites) (hPc : e.pc = site.accessPc) :
    ∃ (t : TState) (o : Option TState) (entry : Fin 2), t.pc = e.pc ∧
      RingShape t ∧
      t.regs site.addressReg = some (b64 (l.localBase + kvLocalOffset site.array entry)) ∧
      EStep kernel Assumptions.all l i.1 t e o := by
  obtain ⟨t, o, _, ht, hShape, _, ⟨_, hAddr⟩, hEv⟩ := eventFrame hp hX he hLo hHi
    (fun t => indexInvariant t ∧ addressInvariant l t)
    (fun _ hpc => ⟨indexInitial hpc, addressInitial hpc⟩)
    (by
      intro warp t u ev hL hH hRoots hInv hStep
      exact ⟨indexStep hL hH hInv.1 hStep,
        addressStep hL hH hp.localMemory.2.1 hRoots hInv.1 hInv.2 hStep⟩)
  have hLive : site.active .address t.pc := (ht.trans hPc).symm ▸ (invariantSite hs).2.2.2.2.2.2
  obtain ⟨entry, _, hEntry⟩ := hAddr site hs .address hLive
  exact ⟨t, o, entry, ht, hShape, hEntry, hEv⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
