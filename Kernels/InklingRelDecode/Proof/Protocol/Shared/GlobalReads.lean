-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Occurs
public import Kernels.InklingRelDecode.Proof.Iface.GlobalReads
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TensorSource
import Kernels.InklingRelDecode.Proof.Lib.ReadKinds
import Kernels.InklingRelDecode.Proof.Protocol.Shared.OperandRead
import Kernels.InklingRelDecode.Proof.Prologue.Export.RequestAddress
import Kernels.InklingRelDecode.Proof.Prologue.Export.BlockAddress
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryReadAddress
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasAddress
import Kernels.InklingRelDecode.Proof.Loader.Export.PageAddress
import Kernels.InklingRelDecode.Proof.Common.Export.LoaderWarp
import Kernels.InklingRelDecode.Proof.Common.Export.PairAddress
import Kernels.InklingRelDecode.Proof.Dispatch.Export.RoleAddress
import Kernels.InklingRelDecode.Proof.Startup.Export.AllocWrite
import Lemmas.Flow.NotBulk
import Lemmas.Flow.AccessLocal
import Lemmas.Flow.OpPcsFast

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow PTX.Proof

private def globalLoadOp (op : Op) : Bool := loadSpace op == some .global

private def dynamicRead (op : Op) : Bool := dynamicAccess op && readOp op

private theorem global_sites :
    OpPcsFast kernel.code globalLoadOp Assumptions.inputReadSites = true := by decide +kernel

private theorem dynamic_sites : OpPcsFast kernel.code dynamicRead [13,2340,2345,2423] = true := by
  decide +kernel

private def Site (p : Nat) : Bool :=
  p == 34 || p == 37 || p == 41 || p == 197 || p == 220 || p == 241 || p == 262 || p == 283 ||
    p == 304 || (388 ≤ p && p ≤ 514 && p % 2 == 0) || (680 ≤ p && p ≤ 806 && p % 2 == 0) ||
    (1124 ≤ p && p ≤ 1250 && p % 2 == 0) || p == 2382 || p == 2399

private theorem site_shape : Assumptions.inputReadSites.all Site = true := by decide +kernel

/-- **A read at one of the 203 sites reads input bytes**, whether it is in the trace or is the
read its lane is about to perform. -/
public theorem occurs_input {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : Occurs L X g k ⟨pc,.rd a bs⟩) (site : pc ∈ Assumptions.inputReadSites) :
    Iface.InputAcc Q a := by
  have shape := List.all_eq_true.mp site_shape pc site
  simp only [Site, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at shape
  have hu : ∀ f, (⟨pc,.rd a bs⟩ : Event).kind ≠ .ub f := fun _ => nofun
  rcases shape with ((((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|⟨⟨h1,h2⟩,h3⟩)|⟨⟨h1,h2⟩,h3⟩)|
    ⟨⟨h1,h2⟩,h3⟩)|h)|h
  · exact Prologue.Export.request_address hp hX hf he (by omega)
  · exact Prologue.Export.request_address hp hX hf he (by omega)
  · exact Prologue.Export.request_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.block_address hp hX hf he (by omega)
  · exact Prologue.Export.query_read_address hp hX hf he ⟨⟨(pc - 388) / 2, by omega⟩,
      by show pc = 388 + 2 * ((pc - 388) / 2); omega⟩
  · exact Softmax.Export.bias_address hp hX hf he (.inl ⟨⟨(pc - 680) / 2, by omega⟩,
    by show pc = 680 + 2 * ((pc - 680) / 2); omega⟩)
  · exact Softmax.Export.bias_address hp hX hf he (.inr ⟨⟨(pc - 1124) / 2, by omega⟩,
    by show pc = 1124 + 2 * ((pc - 1124) / 2); omega⟩)
  · exact Loader.Export.page_address hp hX hf
      (Export.loader_warp_occ hp hX hf he hu (by change 2344 < pc; omega)
        (by change pc < 2422; omega)) he (by omega)
  · exact Loader.Export.page_address hp hX hf
      (Export.loader_warp_occ hp hX hf he hu (by change 2344 < pc; omega)
        (by change pc < 2422; omega)) he (by omega)

private theorem thread_input {Q L m X g k pc a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.rd a bs⟩) (sp : a.loc.space = .global) : Iface.InputAcc Q a := by
  obtain ⟨_,bad⟩|⟨t,ins,u,_,code,fire⟩ := get_source hX he
  · cases bad
  have listed : pc ∈ Assumptions.inputReadSites ∨ pc ∈ [13,2340,2345,2423] := by
    rcases fires_read_loc fire rfl with ⟨eq,_⟩|dyn
    · exact .inl (OpPcsFast.mem global_sites code (by simp [globalLoadOp, eq, sp]))
    · exact .inr (OpPcsFast.mem dynamic_sites code
        (by simp [dynamicRead, dyn, fires_read_op fire rfl]))
  rcases listed with sites | dyn
  · exact occurs_input hp hX hf (.inl he) sites
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at dyn
    rcases dyn with rfl|rfl|rfl|rfl
    · obtain ⟨loc,_⟩ := Startup.Export.base_address hp hX he
      rw [loc] at sp; cases sp
    · obtain ⟨_,_,_,loc⟩ := Dispatch.Export.role_address hp hX he
      rw [loc] at sp; cases sp
    · obtain ⟨j,_,loc,_⟩ := Export.pair_address hp hX he (by simp)
      rw [loc] at sp; cases sp
    · obtain ⟨j,_,loc,_⟩ := Export.pair_address hp hX he (by simp)
      rw [loc] at sp; cases sp

private theorem covered_input {Q : Params} {a : Acc} {l : Loc} (inp : Iface.InputAcc Q a)
    (cover : a.Covers l) (sp : l.space = .global) : Iface.InInput Q l := by
  obtain ⟨_,cta0,rd⟩ := inp
  obtain ⟨space,cta,lo,hi⟩ := cover
  refine ⟨sp, by omega, ?_⟩
  have := rd (l.addr - a.loc.addr) (by omega)
  have e : a.loc.addr + (l.addr - a.loc.addr) = l.addr := by omega
  rwa [e] at this

/-- **Every global byte an access reads is an input byte.** The thread loads are the 203
sites; the tensor loads' sources are the rows `TensorInputBytes` owes; the MMA operand reads
are shared. -/
public theorem global_reads {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (inputs : TensorInputBytes Q X) : Iface.GlobalReads Q X := by
  intro ref a l intent cover sp
  have hsp : a.loc.space = .global := cover.1.symm.trans sp
  rcases Lib.read_intents hX intent with ⟨i,pc,bs,rfl,get⟩|⟨i,isB,j,rfl,foot⟩|
    ⟨i,x,y,z,addr,s,rfl,issue,loc,size⟩
  · obtain ⟨g,k⟩ := i
    exact covered_input (thread_input hp hX hf get hsp) cover sp
  · have := operand_byte hp hX hf foot
    rw [this.1] at hsp
    cases hsp
  · rw [TensorCopy.readLoc_source] at loc
    obtain ⟨slot,_,hs⟩ := Option.bind_eq_some_iff.mp loc
    revert hs
    cases hsrc : TensorCopy.source s slot with
    | fill => simp
    | global address =>
      intro hs
      have eq : a.loc = ⟨.global, 0, address⟩ := (Option.some.inj hs).symm
      have hit := inputs i addr s issue slot address hsrc
      exact covered_input ⟨by rw [eq], by rw [eq], fun j hj => by
        obtain rfl : j = 0 := by omega
        rw [eq]
        exact hit⟩ cover sp

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
