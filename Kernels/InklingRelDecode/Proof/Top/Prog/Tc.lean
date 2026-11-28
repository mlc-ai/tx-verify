-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Lemmas.Quiet.Progress.Async
public import Lemmas.Quiet.Step.CpDrainVisible
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Top.Prog.TcKv
import Kernels.InklingRelDecode.Proof.Protocol.Values.QueryTile
import Kernels.InklingRelDecode.Proof.Protocol.Shared.KvCopyForm
import Kernels.InklingRelDecode.Proof.Top.Safe.NoAssumptionUb
import Kernels.InklingRelDecode.Proof.Top.Result.Frame
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.Shared.QueryOrder
import Kernels.InklingRelDecode.Proof.Protocol.Shared.BaseZero
import Kernels.InklingRelDecode.Proof.Top.Safe.NoTmemSource
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Mma.Export.Operands
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.MmaCells
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.AssumptionStep
import Lemmas.Tcgen05.TcMmaSingleLayout

/-! # Progress class: the MMA completions, static operand facts

An open MMA obligation steps (`Sched.mma_stepsQ`) when the shared operand bytes of the issued MMAs
have visible writes (`OperandVisible`), the A cells in Tensor Memory are apart from the writers of
the same accumulator (`TcMma.ATmemApart`), the layouts are injective, and the kernel has no
`tcgen05.cp` or `tcgen05.shift`. This file proves every premise but the visible writes. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every MMA layout is injective**: the issues are one-CTA (`qkDesc`, `pvDesc`). -/
public theorem Prog.layoutInjective (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) : TcMma.LayoutInjective X := by
  intro i d s acc mask ⟨pc, he⟩ row col row' col' cell h h'
  obtain ⟨g, k⟩ := i
  obtain ⟨-, -, -, _, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, -, -, -, desc⟩ := qk
    exact TcMma.writeCell_one_injective (by rw [desc]; rfl) h h'
  · obtain ⟨j, -, -, -, desc⟩ := pv
    exact TcMma.writeCell_one_injective (by rw [desc]; rfl) h h'

/-- **The A cells of a PV MMA are apart from the cells of its accumulator's writers**: the A
cells are below column 144, the accumulator's columns start at 256. -/
theorem Prog.aApart (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) : TcMma.ATmemApart X := by
  intro j d s acc mask hi index cell pos ha w d' s' acc' mask' row col hw same hwc
  have mc : X.MmaCell w cell := ⟨d', s', acc', mask', row, col, hw, hwc⟩
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, k⟩ := j
  obtain ⟨-, -, -, b, qk | pv⟩ := Mma.Export.columns hp hX hf base he
  · obtain ⟨j, -, -, none, -⟩ := qk
    simp [TcMma.aCell, none] at ha
  · obtain ⟨j, -, hd, hat, -⟩ := pv
    have range := Tmem.mma_a_range hp hX hf base he hat ⟨d, s, acc, mask, index, pos, ⟨pc, he⟩, ha⟩
    obtain ⟨pc', d'', s'', acc'', mask'', get, -, hlo, -, -, -, -⟩ :=
      Tmem.mma_write_cell hp hX hf base mc
    obtain ⟨_, ev⟩ := hw
    rw [get] at ev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at ev
    obtain ⟨-, rfl, -, -, -⟩ := ev
    have := Fin.isLt j
    have h256 : d'' = 256 := same.1.trans hd
    omega

/-- **One lane of a warp issues its MMAs.** -/
theorem Prog.issuerUnique (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) : TcMma.WarpIssuerUnique L X := by
  intro i j ⟨d, s, acc, mask, pc, hi⟩ ⟨d', s', acc', mask', pc', hj⟩ ⟨⟨hg, hg', cta⟩, warp⟩
  obtain ⟨g, k⟩ := i
  obtain ⟨g', k'⟩ := j
  obtain ⟨w, el, -⟩ := Mma.Export.read_slot hp hX hf words hi
  obtain ⟨w', el', -⟩ := Mma.Export.read_slot hp hX hf words hj
  obtain ⟨e, h, r⟩ := el
  obtain ⟨e', h', r'⟩ := el'
  have e1 := Protocol.KV.leader_eq hX (Frame.lt_of_get hX hi) ⟨e, List.mem_of_mem_take h, r⟩
  have e2 := Protocol.KV.leader_eq hX (Frame.lt_of_get hX hj) ⟨e', List.mem_of_mem_take h', r'⟩
  simp only at cta warp
  rw [← e1, ← e2, cta, warp]

/-- **The shared operand bytes of the issued MMAs have visible writes**: what is left to prove
for the MMA class. A write of each byte is causally before the operand read, and every such write
has a defined byte. The K and V bytes are the copies' and the query bytes the prologue's stores. -/
def Prog.Visible (L : Launch) (X : Execution) : Prop :=
  ∀ i d sp acc mask, X.MmaIssue i d sp acc mask → X.async.mmaOperands i = none →
    ∀ isB k loc, X.MmaFootprint i isB k loc →
      (∃ w a bs, X.MemWrites w a bs ∧ a.Covers loc ∧
        ByteCausality L X loc w (.async i (.mmaRead isB k))) ∧
      ∀ w a bs, X.MemWrites w a bs → a.Covers loc →
        ByteCausality L X loc w (.async i (.mmaRead isB k)) → ∃ v, wbyte a bs loc = some v

/-- **The operand bytes have visible writes** given the query tile's stores: a K or V byte has the
copy of its use before the read (`Prog.kvVisible`), a query byte its covering store
(`QueryTile.covered`, ordered by `query_write_read`). -/
theorem Prog.visible (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) (T : Iface.QueryTile L X) : Prog.Visible L X := by
  intro i d sp acc mask hi _ isB k loc hfoot
  refine ⟨?_, fun w a bs hw hc _ => Prog.wbyte_of_write hX hw hc⟩
  obtain ⟨pc, he⟩ := hi
  obtain ⟨g, j⟩ := i
  rcases hfoot with ⟨d', s', acc', mask', ⟨pc', he'⟩, byte⟩ | ⟨c, _, _, cp, _⟩
  swap
  · exact (Lib.no_cp hX _ c cp).elim
  rw [he] at he'
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he'
  cases isB
  · obtain ⟨-, -, tile⟩ := Mma.Export.operands_all hp hX hf he
    obtain ⟨space, cta, lo, hi⟩ := tile .a k loc byte
    obtain ⟨gs, ks, a, bs, i', get, cov⟩ := T.covered he ⟨space, lo, hi⟩ cta
    have memw : X.MemWrites (.thread (gs, ks)) a bs := Or.inl ⟨_, get⟩
    have rintent : X.Intent (.async (g, j) (.mmaRead false k)) { loc := loc, size := 1 } false :=
      ⟨rfl, rfl, .inl ⟨d, sp, acc, mask, ⟨pc, he⟩, byte⟩⟩
    have cov' : ({ loc := loc, size := 1 } : Acc).Covers loc := by simp [Acc.Covers, Loc.InRange]
    exact ⟨_, a, bs, memw, cov, Protocol.Shared.query_write_read hp hX hf memw.intent rintent cov
      cov' ⟨space, lo, hi⟩⟩
  · exact Prog.kvVisible hp hX hf rows init words hu nub form he byte

/-- **An open MMA obligation steps** when the operand bytes' writes are visible. -/
theorem Prog.mma_of_visible (hp : Pre Q L m) (hm : Maximal L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (vis : Prog.Visible L X)
    (ho : Descent.Obl L X .mma) : Sched.Steps (schedule Q L) m X .mma := by
  have hX := hm.1
  have hos : OperandVisible L X := by
    refine ⟨Prog.issuerUnique hp hX hf words, fun i d sp acc mask hi hn =>
      ⟨?_, vis i d sp acc mask hi hn⟩⟩
    obtain ⟨pc, he⟩ := hi
    obtain ⟨g, k⟩ := i
    obtain ⟨desc, -⟩ := Mma.Export.operands hp hX hf he
    rcases desc with h | h <;> rw [h]
    exacts [Lib.qkDesc_valid, Lib.pvDesc_valid]
  have base : Iface.BaseRead L X := Protocol.Shared.base_read hp hX hf
  have rows := mbarRows_of hp hX hf
  have init := initRows_of hp hX hf
  refine (ho fun i hi => ?_).elim
  rcases hi with ⟨_, _, _, _, hmm⟩ | ⟨c, hc⟩ | ⟨s, hs⟩
  · exact Maximal.mma_all_done_visibleQ Lib.assumptions_step.wfQuiet hm
      (Safe.guarded hp hX hf rows init) hos (Prog.aApart hp hX hf base)
      (Prog.layoutInjective hp hX hf base) hmm
  · exact (Lib.no_cp hX i c hc).elim
  · exact (Tmem.no_shift hX i s hs).elim

/-- **A pending MMA obligation steps.** -/
public theorem Prog.mma {Q L m} (hp : Pre Q L m) : Prog.Async Q L m [.mma] := by
  intro hs X hm hf o mem ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  subst o
  have hX := hm.1
  have nub : ¬ Assumptions.inputReadOnly.ub L m X := fun h =>
    Safe.noAssumptionUb hp hX (Result.output_placed hp hX hf) ⟨_, by simp [Assumptions.all], h⟩
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  exact Prog.mma_of_visible hp hm hf words (Prog.visible hp hX hf (mbarRows_of hp hX hf)
    (initRows_of hp hX hf) words (.of_noUb (Sched.safe_noUb (hs.2 X hX))) nub
    (Protocol.Shared.kv_copy_form hp hX hf) (Protocol.Values.query_tile hp hX hf words)) ho

end PTX.Kernels.InklingRelDecode.Proof.Top
