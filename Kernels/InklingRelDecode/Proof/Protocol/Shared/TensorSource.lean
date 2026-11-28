-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Shared.TileWriters
public import Lemmas.Quiet.Progress.Async
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Lemmas.Flow.NotObject
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotBulk
import Lemmas.Flow.TensorLoadFacts
import Lemmas.Kernel.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Flow

private def unicast : Op → Bool
  | .cpTensor false false _ _ _ _ _ _ none .tile _ => true
  | _ => false

private theorem routes : kernel.code.all (fun i => !tensorOp i.op || unicast i.op)=true := by
  decide +kernel

/-- The issue itself fixes both endpoints inside its issuer's CTA. Its launch
descriptor has 8192 bytes, including slots whose source is a fill. -/
theorem tensor_box {Q L m X g k pc addr s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.tensorIssue addr s⟩) :
    TensorCopy.RoutingOk L (g/L.block) s ∧ TensorDescriptor.Valid s.descriptor ∧
      TensorTransfer.bytes s.descriptor=8192 := by
  have desc := tensor_map hp hX he
  have valid := Lib.mapKv_valid hp.kvAlign hp.slotStridePos hp.slotStrideAlign hp.slotStrideRange
    hp.rowsPos hp.rowsRange
  have transfer (d : (n : Nat) × TensorDescriptor.Descriptor n) :
      d=⟨1,mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass⟩ →
      TensorDescriptor.Valid d.2 ∧ TensorTransfer.bytes d.2=8192 := by
    rintro rfl
    exact ⟨valid,by simp [TensorTransfer.bytes,mapKv,TensorTile.count,TensorTile.rows,
      TensorTile.rowsOf,TensorTile.step,TensorDescriptor.Format.bytes]⟩
  refine ⟨?_,transfer _ desc⟩
  obtain ⟨_,bad⟩|⟨t,ins,_,_,code,fire⟩ := get_source hX he
  · cases bad
  have top : tensorOp ins.op=true := by
    cases eq : tensorOp ins.op with
    | true => rfl
    | false => exact (fires_notTensor (eventTmpl_notTensor eq) fire addr s rfl).elim
  have localOp := List.all_eq_true.mp routes ins (List.mem_of_getElem? code)
  simp only [top,Bool.not_true,Bool.false_or] at localOp
  have shape : ∃ dst off map cs mb moff pol,
      ins.op=.cpTensor false false dst off map cs mb moff none .tile pol := by
    generalize ins.op=op at localOp ⊢
    cases op <;> try contradiction
    rename_i ca grp dst off map cs mb moff mask mode pol
    cases ca <;> cases grp <;> cases mask <;> cases mode <;> simp_all [unicast]
  obtain ⟨_,_,_,_,_,_,_,op⟩ := shape
  rw [op] at fire
  have load := fires_cpTensor_copy fire rfl
  obtain ⟨dest,ca,grp⟩ := tensorLoadCopy_box load
  obtain ⟨_,mb,_⟩ := tensorLoadCopy_ok load
  obtain ⟨sp,cta⟩ := sharedEffAddr_local dest
  obtain ⟨sp',cta'⟩ := mbarLoc_local mb
  have hg := Frame.lt_of_get hX he
  have cg : g/L.block<L.grid := Nat.div_lt_of_lt_mul (by
    simpa [Launch.threads,Nat.mul_comm] using hg)
  have member : CtaInCluster L (g/L.block) (g/L.block) := ⟨cg,cg,rfl⟩
  unfold TensorCopy.RoutingOk TensorRoute
  rw [ca,grp,cta,cta']
  exact ⟨hp.launchValid.1,sp,sp',member,member,fun _ => ⟨rfl,rfl⟩,
    (sameCtaGroup_iff ..).mpr ⟨member,rfl⟩⟩

theorem initialized {Q L m addr} (hp : Pre Q L m) (read : Q.reads addr) :
    ∃ b, m ⟨.global,0,addr⟩=some (some b) := by
  rcases read with ⟨r,hr,t,ht,h,hh,d,hd,b,hb,rfl⟩|⟨r,hr,t,ht,h,hh,c,hc,b,hb,rfl⟩|
    ⟨r,hr,s,hs,h,hh,i,hi,c,hc,b,hb,rfl⟩|⟨r,hr,b,hb,rfl⟩|⟨r,hr,b,hb,rfl⟩|⟨r,hr,s,hs,b,hb,rfl⟩
  · exact ⟨_,hp.qInput r hr t ht h hh d hd b hb⟩
  · exact ⟨_,hp.relInput r hr t ht h hh c hc b hb⟩
  · exact ⟨_,hp.kvInput r hr s hs h hh i hi c hc b hb⟩
  · exact ⟨_,hp.cuInput r hr b hb⟩
  · exact ⟨_,hp.seqInput r hr b hb⟩
  · exact ⟨_,hp.btInput r hr s hs b hb⟩

/-- The address row still owed by both copy issuers. Descriptor fill slots have
no source address. -/
def TensorInputBytes (Q : Params) (X : Execution) : Prop :=
  ∀ i addr s, X.TensorIssue i addr s → ∀ slot a, TensorCopy.source s slot=.global a → Q.reads a

theorem tensor_sources {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hs : ¬ Unsafe L kernel Assumptions.all m X) (inputs : TensorInputBytes Q X) :
    TensorSources L m X := by
  rintro ⟨g,k⟩ addr s issue
  obtain ⟨pc,get⟩ := id issue
  obtain ⟨route,valid,size⟩ := tensor_box hp hX get
  refine ⟨route,valid,by omega,?_⟩
  intro slot a source
  have hit := inputs _ _ _ issue _ _ source
  obtain ⟨v,byte⟩ := initialized hp hit
  refine ⟨v,byte,?_⟩
  intro ref dst bytes write cover
  apply hs
  have bad : Assumptions.inputReadOnly.ub L m X :=
    ⟨Q,ref,dst,_,hp,write.intent,cover,rfl,rfl,hit⟩
  have use : ∃ a ∈ Assumptions.all, a.ub L m X := ⟨_,by simp [Assumptions.all],bad⟩
  simp [Unsafe,use]

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
