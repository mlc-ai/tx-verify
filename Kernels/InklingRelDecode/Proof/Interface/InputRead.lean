-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SxGRead
public import Kernels.InklingRelDecode.Proof.Interface.PrefixTrack
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Step.WfInOrder
public import Lemmas.Snoc.PlainAsyncExtend

@[expose] public section

/-!
# The read-only input assumption: the launch bytes, the steps

`Assumptions.inputReadOnly` constrains the plain reads at the 203 global loads of the program
(`Assumptions.inputReadSites`). Here is what the proof takes from it.

* The sites are exactly the reads of the program outside shared memory, and each is a load of
  global memory (`kernel_nonShared_reads`, `kernel_sites_global`, `decide +kernel`): a read event
  is at a site exactly when it reads global memory (`read_site_global`).
* So every read of an input byte returns the launch byte (`launchRead_of_wf`), at every event of
  every consistent execution, with no premise about the order of the execution.
* `inputReadOnly_wf_ext`, `inputReadOnly_wf_read`: the assumption's constraint holds of an
  extension that adds no read, and of the append of a read whose bytes have sources
  (`NewRead`) when no write of the execution covers the bytes a read at a site reads.
* `ReadFresh`, `readFresh_of`: the next read of a followed thread at a site reads input bytes, and
  no write of the execution covers them (the progress layer's per-step fact).
* `out_pinned`: two parameter sets of one launch (`Pre`) have the same output arrays; with it
  `Safety.no_inputReadOnly_ub` shows the assumption's `ub` never holds.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The sites -/

/-- Instructions that may read global memory: a load that names global memory or no space. -/
def nonSharedReadOp (op : Op) : Bool :=
  match op with
  | .mem ma => readOp op && (ma.space == some .global || ma.space == none)
  | _ => false

/-- **The reads of the program that may read global memory are at the sites.** -/
theorem kernel_nonShared_reads :
    OpPcsFast kernel.code nonSharedReadOp Assumptions.inputReadSites = true := by
  decide +kernel

/-- **Each site is a load of global memory.** -/
theorem kernel_sites_global : Assumptions.inputReadSites.all (fun pc =>
    (kernel.code[pc]?).any fun ins => loadSpace ins.op == some .global) = true := by
  decide +kernel

theorem inputReadOnly_mem : Assumptions.inputReadOnly ∈ asms := by
  simp [asms, Assumptions.all]

/-- A read fired at a site reads global memory. -/
theorem fired_site_global {A : List Assumption} {g : Nat} {t : TState} {pc : Nat} {ins : Instr}
    {e : Event} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .rd a bs) (hs : Assumptions.inputReadSites.contains pc = true) :
    a.loc.space = .global := by
  have h := List.all_eq_true.mp kernel_sites_global pc (by simpa using hs)
  rw [hc] at h
  simp only [Option.any_some, beq_iff_eq] at h
  exact fires_read_space hf hk h

/-- A read of global memory is fired at a site. -/
theorem fired_global_site {A : List Assumption} {g : Nat} {t : TState} {pc : Nat} {ins : Instr}
    {e : Event} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl A L g t ins.op) e o)
    (hk : e.kind = .rd a bs) (hsp : a.loc.space = .global) :
    Assumptions.inputReadSites.contains pc = true := by
  have hr := fires_read_op hf hk
  obtain ⟨ma, hma, hns⟩ := fires_read_global hf hk hsp
  have hm := OpPcsFast.mem kernel_nonShared_reads hc (by
    rw [hma] at hr ⊢
    rcases hns with h | h <;> simp [nonSharedReadOp, hr, h])
  simpa using hm

/-- **A read event is at a site exactly when it reads global memory.** -/
theorem read_site_global (hX : Consistent L kernel asms mem0 X) {e : EvId} {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get e = some ⟨pc, .rd a bs⟩) :
    Assumptions.inputReadSites.contains pc = true ↔ a.loc.space = .global := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hfi⟩
  · cases hf
  · exact ⟨fired_site_global hc hfi rfl, fired_global_site hc hfi rfl⟩

/-! ### The launch bytes -/

/-- **Every read of an input byte returns the launch byte**, by `Assumptions.inputReadOnly`. -/
theorem launchRead_of_wf (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    ∀ e, LaunchRead Q mem0 X e := by
  intro e pc a bs he hsp hcta k hk hrd
  have hs := (read_site_global hX he).mpr hsp
  have heq : a.loc.at k = ⟨.global, 0, (a.loc.at k).addr⟩ := by
    simp only [Loc.at, hsp, hcta]
  obtain ⟨c, hc⟩ := reads_mem0 hpre hrd
  rw [← heq] at hc
  exact ⟨c, hc, hX.asm _ inputReadOnly_mem e pc a bs he hs k hk c hc⟩

/-- **The output arrays are fixed by the launch**: two parameter sets of one launch have the same
output bases and sizes (`param_10`, `param_11`, `param_24`, `param_25`). -/
theorem out_pinned {P P' : Params} (h : Pre P L mem0) (h' : Pre P' L mem0) :
    P'.oBase = P.oBase ∧ P'.lseBase = P.lseBase ∧ oBytes P' = oBytes P ∧
      lseBytes P' = lseBytes P := by
  have key : ∀ {x y : Nat}, x < 2 ^ 64 → y < 2 ^ 64 →
      (some (BitVec.ofNat 64 x) : Option (BitVec 64)) = some (BitVec.ofNat 64 y) → x = y := by
    intro x y hx hy he
    have := congrArg BitVec.toNat (Option.some.inj he)
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hs : P'.splits = P.splits := key (by have := h'.splitsRange; omega)
    (by have := h.splitsRange; omega) (h'.paramSplits.symm.trans h.paramSplits)
  have hn : P'.nTok = P.nTok := key (by have := h'.nTokRange; omega)
    (by have := h.nTokRange; omega) (h'.paramNTok.symm.trans h.paramNTok)
  have hob : oBytes P' = oBytes P := by simp only [oBytes, hs, hn]
  have hlb : lseBytes P' = lseBytes P := by simp only [lseBytes, hs, hn]
  have hpo : ∀ {R : Params}, Pre R L mem0 → 0 < oBytes R ∧ 0 < lseBytes R := by
    intro R hR
    have := hR.splitsPos
    have := hR.nTokPos
    unfold oBytes lseBytes heads headDim
    constructor <;> positivity
  have hoB : ∀ {R : Params}, Pre R L mem0 → R.oBase < 2 ^ 64 := fun hR => by
    have := hR.oRange; have := (hpo hR).1; omega
  have hlB : ∀ {R : Params}, Pre R L mem0 → R.lseBase < 2 ^ 64 := fun hR => by
    have := hR.lseRange; have := (hpo hR).2; omega
  exact ⟨key (hoB h') (hoB h) (h'.paramO.symm.trans h.paramO),
    key (hlB h') (hlB h) (h'.paramLse.symm.trans h.paramLse), hob, hlb⟩

/-! ### The assumption's constraint on the extensions of the progress layer -/

/-- **An extension that adds no read keeps the constraint.** -/
theorem inputReadOnly_wf_ext {Y : Execution}
    (hwf : Assumptions.inputReadOnly.wf L mem0 X) (hr : X.NoNewRead Y) :
    Assumptions.inputReadOnly.wf L mem0 Y :=
  fun e pc a bs he hs => hwf e pc a bs (hr e _ he rfl) hs

/-- **A read whose bytes have sources keeps the constraint**, when at a site no write of the
execution covers a byte it reads: each byte then has no write source, so it is the launch byte. -/
theorem inputReadOnly_wf_read {g pc : Nat} {e : Event} {r : Nat → Option AsyncCopy.Ref}
    {a : Acc} {bs : List (Option Byte)}
    (hwf : Assumptions.inputReadOnly.wf L mem0 X) (hread : NewRead L mem0 X g e r a bs)
    (hfresh : Assumptions.inputReadSites.contains pc = true →
      ∀ k < a.size, ∀ w a' bs', X.MemWrites w a' bs' → ¬ a'.Covers (a.loc.at k)) :
    Assumptions.inputReadOnly.wf L mem0 (X.snoc g ⟨pc, .rd a bs⟩ r) := by
  intro v pc' a' bs' hv hs
  rw [snoc_get] at hv
  split_ifs at hv
  · simp only [Option.some.injEq, Event.mk.injEq, Kind.rd.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    intro k hk c hc
    have hsrc := hread.src k hk
    cases hrk : r k with
    | none =>
      rw [hrk] at hsrc
      simpa [Execution.initialByte] using hsrc _ hc
    | some w =>
      rw [hrk] at hsrc
      obtain ⟨a'', bs'', hw, hcov, -⟩ := hsrc
      exact absurd hcov (hfresh hs k hk w a'' bs'' hw)
  · exact hwf v pc' a' bs' hv hs

/-- **The next read of a followed thread at a site reads bytes no write of the execution
covers.** -/
def ReadFresh (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g pc : Nat} {s : TSt} {u : TState} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    St Q L X g (X.tr g).length = some (some s) →
    (threadCode L g Q).toMachine.Fired (some s) ⟨pc, .rd a bs⟩ (some u) →
    Assumptions.inputReadSites.contains pc = true →
    ∀ k < a.size, ∀ w a' bs', X.MemWrites w a' bs' → ¬ a'.Covers (a.loc.at k)

/-- A write of global memory covers no input byte: it is an output store of a followed thread. -/
theorem write_not_input (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {w : AsyncCopy.Ref} {a' : Acc} {bs' : List Byte}
    (hw : X.MemWrites w a' bs') {l : Loc} (hl : l.space = .global) (hrd : Q.reads l.addr)
    (hcov : a'.Covers l) : False := by
  have hsp' : a'.loc.space = .global := hcov.1.symm.trans hl
  have hap := hpre.outputsApart _ hrd
  have htr : ∀ g n, w = .thread (g, n) → ∃ s, St Q L X g n = some (some s) := by
    intro g n hwn
    subst hwn
    rcases hw with ⟨pc', hh⟩ | ⟨old, pc', hh⟩
    · exact Frame.event_state hf.sound hX hf.tracked hh (by intro pc f h; cases h)
    · exact absurd hh (no_rmw hX)
  rcases write_in_arrays_at hpre hX hf.sound hw hsp' hcov htr with h | h
  · exact hap.1 h
  · exact hap.2 h

/-- **`ReadFresh`** from the thread facts: the read is a global load (`fired_site_global`) of
input bytes (`fired_read_input`), and no write covers an input byte (`write_not_input`). -/
theorem readFresh_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) : ReadFresh Q L X := by
  intro g pc s u a bs hg hσ hF hs k hk w a' bs' hw hcov
  obtain ⟨t, ins, -, -, hc, hfi⟩ := Frame.fired_site_of hf.sound hg hF
  have hpc : pc = (code L Q g).pc s := EventFrame.fires_source_pc hfi
  rw [← hpc] at hc hfi
  have hsp := fired_site_global hc hfi rfl hs
  obtain ⟨-, hcta, hrd⟩ := fired_read_input hpre hX hf hn hg hσ hF (by rw [hsp]; decide)
  exact write_not_input hpre hX hf hw (l := a.loc.at k) (by simp [Loc.at, hsp])
    (by simpa [Loc.at] using hrd k hk) hcov

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
