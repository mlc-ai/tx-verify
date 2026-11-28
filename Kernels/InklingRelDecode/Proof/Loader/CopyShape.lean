-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Shape
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.TensorLoadFacts

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

theorem copy_instr (p : Fin 4) (half : Bool) :
    let pc := (Site.copy p half).pc
    ∃ guard dst coords, kernel.code[pc]? = some ⟨guard,
      .cpTensor false false dst 0 (.reg 1949) coords 580 0 none .tile⟩ := by
  fin_cases p <;> cases half
  · exact ⟨_, _, _, Flow.code_2389⟩
  · exact ⟨_, _, _, Flow.code_2391⟩
  · exact ⟨_, _, _, Flow.code_2394⟩
  · exact ⟨_, _, _, Flow.code_2396⟩
  · exact ⟨_, _, _, Flow.code_2404⟩
  · exact ⟨_, _, _, Flow.code_2406⟩
  · exact ⟨_, _, _, Flow.code_2410⟩
  · exact ⟨_, _, _, Flow.code_2412⟩

theorem copy_site (s : Site) :
    s.pc ∈ [2389, 2391, 2394, 2396, 2404, 2406, 2410, 2412] → ∃ p half, s=.copy p half := by
  cases s <;> first | exact fun _ => ⟨_,_,rfl⟩ |
    (repeat' first | decide +kernel | (rename_i j; revert j))

private theorem packet_live (p : Fin 4) (half : Bool) :
    1949 ∈ Flow.live (Site.copy p half).pc ∧ 580 ∈ Flow.live (Site.copy p half).pc := by
  fin_cases p <;> cases half <;> decide

/-- All eight issue sites debit the same ready slot by the descriptor's full byte count. -/
theorem copy_slot {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {w : Value}
    {regs : Nat → Value} {i n a b : Value} {p : Fin 4} {half : Bool} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {addr : Nat} {sp : TensorCopy.Spec}
    (hp : Pre Q L mem0) (hi : (bits i).toNat < 2 ^ 31)
    (hr : regs 1949 = .ptr 64 true (.param (param "1")) 0)
    (ht : (code L g w regs).AtD ⟨.copy p half,i,n,a,b⟩ t)
    (hc : kernel.code[(Site.copy p half).pc]? = some ins)
    (hf : Fires (Site.copy p half).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : e.kind = .tensorIssue addr sp) :
    addr = Q.kvMap ∧ sp.mbar = Iface.kvReadyLoc L (g / L.block) ⟨(bits i).toNat % 3, by omega⟩ ∧
      TensorTransfer.bytes sp.descriptor = 8192 := by
  obtain ⟨guard, dst, coords, hop⟩ := copy_instr p half
  obtain rfl := Option.some.inj (hc.symm.trans hop)
  obtain ⟨_, _, _, _, hregs⟩ := ht
  let val := valueOf L g w regs ⟨.copy p half,i,n,a,b⟩
  have hreg (r : Nat) (hm : r ∈ Flow.live (Site.copy p half).pc) : t.regs r = some (val r) :=
    holds_mem hregs (mem_factsFrom hm)
  have hptr : t.regs 1949 = some (.ptr 64 true (.param (param "1")) 0) :=
    (hreg 1949 (packet_live p half).1).trans (congrArg some hr)
  have hbar := ready_location (g := g) hp hi (hreg 580 (packet_live p half).2)
  obtain ⟨hm, hb, desc, hd, _, hs, _⟩ := tensorLoadCopy_ok (fires_cpTensor_copy hf he)
  obtain ⟨decl, hobj⟩ := tensorMapAddress_param hptr hm
  obtain ⟨_, ha⟩ := Prod.mk.inj (Option.some.inj (hobj.symm.trans hp.paramKv))
  refine ⟨ha, (Except.ok.inj ((show mbarLoc L g t 580 0 = .ok sp.mbar from hb).symm.trans hbar)),
    ?_⟩
  rw [ha] at hd
  have hmaps := Option.some.inj (hd.symm.trans hp.mapKvBind)
  rw [hs]
  exact (congrArg (fun m : (o : Nat) × TensorDescriptor.Descriptor o =>
    TensorTransfer.bytes m.2) hmaps).trans (by
    simp [TensorTransfer.bytes, mapKv, TensorTile.count, TensorTile.rows, TensorTile.rowsOf,
      TensorTile.step, TensorDescriptor.Format.bytes])

end PTX.Kernels.InklingRelDecode.Proof.Loader
