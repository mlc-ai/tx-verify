-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Iface.BarRows.Base
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC
import Kernels.InklingRelDecode.Flow.Code.Part044
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotClc
import Lemmas.Flow.TmemOperands

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

/-- All whole-CTA synchronizations on the publication barrier. -/
def barOneSites : List Nat :=
  [573,575,2334,2335,2338,2346,2419,2424,2554,2557,2558,2846,2849]

private def sync (op : Op) (id : Nat) : Bool :=
  match op with
  | .barSync (.imm v) _ => v == (id : Int)
  | _ => false

private theorem sync_op {op id} (h : sync op id = true) :
    ∃ a, op = .barSync (.imm id) a := by
  unfold sync at h
  split at h <;> simp_all

private def halfSync : Op → Bool
  | .barSyncN (.imm 0) (.imm 128) _ => true
  | _ => false

private theorem half_op {op} (h : halfSync op = true) :
    ∃ a, op = .barSyncN (.imm 0) (.imm 128) a := by
  unfold halfSync at h
  split at h <;> simp_all

private def matchesSite (x : Instr × Nat) : Bool :=
  if x.2 ∈ barOneSites then x.1.guard.isNone && sync x.1.op 1
  else !barOp x.1.op || sync x.1.op 0 || halfSync x.1.op

private theorem checked : kernel.code.zipIdx.all matchesSite = true := by decide +kernel

private theorem sync_kind {A L g t pc e o id al} (hid : id < 16)
    (hf : Fires pc (eventTmpl A L g t (.barSync (.imm (id : Nat)) al)) e o) :
    e = ⟨pc, .bar id none .sync⟩ := by
  have himm : readBits L g t 32 (Opnd.imm (id : Int)) = .ok (BitVec.ofNat 64 id) := by
    simp only [readBits, truncBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
    omega
  simp only [eventTmpl, barTmpl, himm, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show id < 2 ^ 64 by omega), show ¬ 16 ≤ id by omega, ↓reduceIte] at hf
  exact hf.1

/-- At a firing instruction the barrier-1 prefix counter advances precisely at
the listed pcs. A half-CTA synchronization records count 128 on barrier 0. -/
theorem barOne_fires {A L g t pc e o ins} (hb : L.block = 256)
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o) :
    Execution.isBarId 1 e = decide (pc ∈ barOneSites) := by
  have h := List.all_eq_true.mp checked (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr hc)
  by_cases hpc : pc ∈ barOneSites
  · simp only [matchesSite,hpc,↓reduceIte,Bool.and_eq_true] at h
    obtain ⟨_,hop⟩ := sync_op h.2
    rw [hop] at hf
    rw [sync_kind (by decide) hf]
    simp [Execution.isBarId,hpc]
  · simp only [matchesSite,hpc,↓reduceIte,Bool.or_eq_true,Bool.not_eq_true'] at h
    simp only [hpc,decide_false]
    cases he : Execution.isBarId 1 e with
    | false => rfl
    | true =>
      obtain ⟨ep,k⟩ := e
      cases k <;> simp [Execution.isBarId] at he
      subst he
      have hbar := fires_bar_op hf rfl
      rcases h with (bad | whole) | half
      · simp [bad] at hbar
      · obtain ⟨_,hop⟩ := sync_op whole
        rw [hop] at hf
        cases sync_kind (by decide) hf
      · obtain ⟨_,hop⟩ := half_op half
        rw [hop] at hf
        cases fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide) (by decide)
          (by decide) (by omega) hf

/-- The publication barrier always synchronizes the full CTA and records no count. -/
theorem publication_kind {L m X i pc cnt mode} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block=256) (he : X.get i = some ⟨pc,.bar 1 cnt mode⟩) :
    cnt = none ∧ mode = .sync := by
  obtain ⟨_,bad⟩ | ⟨t,ins,o,_,code,fire⟩ := get_source hX he
  · cases bad
  have hit := barOne_fires hb code fire
  change true = decide (pc ∈ barOneSites) at hit
  have site := of_decide_eq_true hit.symm
  have check := List.all_eq_true.mp checked (ins,pc) (List.mem_zipIdx_iff_getElem?.mpr code)
  simp only [matchesSite,site,↓reduceIte,Bool.and_eq_true] at check
  obtain ⟨_,op⟩ := sync_op check.2
  rw [op] at fire
  cases sync_kind (by decide) fire
  exact ⟨rfl,rfl⟩

private def zeroCheck (x : Instr × Nat) : Bool :=
  (!sync x.1.op 0 || x.2 ∈ BarRow.fullZeroSites) &&
  (!halfSync x.1.op || x.2 ∈ BarRow.halfZeroSites)

private theorem zeroSites : kernel.code.zipIdx.all zeroCheck = true := by decide +kernel

/-- Classification of every recorded CTA-barrier event, including the two final
full-CTA rendezvous. The half-CTA instructions record a count of 128. -/
theorem recorded_bar {L m X i pc id cnt mode} (hX : Consistent L kernel Assumptions.all m X)
    (hb : L.block=256) (he : X.get i = some ⟨pc,.bar id cnt mode⟩) :
    mode=.sync ∧ ((id=1 ∧ cnt=none ∧ pc ∈ barOneSites) ∨
      (id=0 ∧ cnt=none ∧ pc ∈ BarRow.fullZeroSites) ∨
      (id=0 ∧ cnt=BarRow.recCnt L.block 128 ∧ pc ∈ BarRow.halfZeroSites)) := by
  obtain ⟨_,bad⟩ | ⟨_,ins,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have isBar := fires_bar_op fire rfl
  have atPC : (ins,pc) ∈ kernel.code.zipIdx := List.mem_zipIdx_iff_getElem?.mpr code
  have check := List.all_eq_true.mp checked (ins,pc) atPC
  have loc := List.all_eq_true.mp zeroSites (ins,pc) atPC
  simp only [zeroCheck,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
    decide_eq_true_eq] at loc
  by_cases one : pc ∈ barOneSites
  · simp only [matchesSite,one,↓reduceIte,Bool.and_eq_true] at check
    obtain ⟨_,op⟩ := sync_op check.2
    rw [op] at fire
    cases sync_kind (by decide) fire
    exact ⟨rfl,.inl ⟨rfl,rfl,one⟩⟩
  · simp only [matchesSite,one,↓reduceIte,isBar,Bool.not_true,Bool.false_or,
      Bool.or_eq_true] at check
    rcases check with full|half
    · have site := loc.1.resolve_left (by simp [full])
      obtain ⟨_,op⟩ := sync_op full
      rw [op] at fire
      cases sync_kind (by decide) fire
      exact ⟨rfl,.inr (.inl ⟨rfl,rfl,site⟩)⟩
    · have site := loc.2.resolve_left (by simp [half])
      obtain ⟨_,op⟩ := half_op half
      rw [op] at fire
      cases fires_barSyncN_imm (id := 0) (n := 128) (by decide) (by decide) (by decide)
        (by decide) (by omega) fire
      exact ⟨rfl,.inr (.inr ⟨rfl,by rw [hb]; decide,site⟩)⟩

theorem final_kind {L m X i e} (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get i=some e) (site : finalSync e.pc=true) (hu : ∀ f, e.kind≠.ub f) :
    e.kind=.bar 0 none .sync := by
  have fetch : kernel.code[e.pc]? = some ⟨none,.barSync (.imm 0) true⟩ := by
    simp only [finalSync,Bool.or_eq_true,beq_iff_eq] at site
    rcases site with eq|eq <;> rw [eq]
    · exact Flow.code_2850
    · exact Flow.code_2853
  obtain ⟨f,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
  · exact (hu f bad).elim
  cases Option.some.inj (code.symm.trans fetch)
  exact congrArg Event.kind (sync_kind (id := 0) (by decide) fire)

end PTX.Kernels.InklingRelDecode.Proof.Lib
