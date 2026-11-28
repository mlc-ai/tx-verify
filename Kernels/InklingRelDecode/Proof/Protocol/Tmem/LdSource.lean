-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdCand
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Live
public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.Wrote
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdstBefore
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.DataStatic
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Tcgen05.TmemLatestSource

@[expose] public section

/-! # A load register has a source with a value

The load's candidate writer (`ld_s_cand`, `ld_o_cand`, `ld_e_cand`), the order of every writer with
the load (`ld_order`) and the liveness of the allocation (`source_live_ld`) give the latest write
before it as the read source (`TcMma.readSourceOfCandidate`); a done MMA or a store has a value. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.TcMma

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The register of a load has a read source with a value**, and an MMA source is done. -/
public theorem ld_source_done (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (hG : SyncGuarded L kernel X) (hws : WritesSafe L X) (ht : Tmem.One.Tmem1Facts L X 0)
    {e : EvId} {j : Nat} {cell : Cell}
    (hCV : ∀ i d s acc mask, X.MmaIssue i d s acc mask → X.MmaCell i cell →
      WriteBefore L X i e → CompletedValues L Assumptions.all X i) (hl : LoadCell L X e j cell) :
    ∃ source value, ReadSource L X .ld source e cell ∧
      Wrote L Assumptions.all X source cell value ∧
        (X.MmaCell source cell → X.async.mmaDone source = true) := by
  obtain ⟨a,vals,sh,hld,hj,hcell⟩ := hl
  obtain ⟨t,k0⟩ := e
  obtain ⟨pc,he⟩ := id hld
  obtain ⟨i,k,-,hpa,-⟩ := ld_static hp hX hf base he
  have hpc : pc = 1265 ∨ pc = 2260 ∨ pc = 2607 := by omega
  subst hcell
  obtain ⟨w,hw,hb⟩ : ∃ w, TmemWrite L X w (tcDataCell L t sh a j) ∧ WriteBefore L X w (t,k0) := by
    rcases hpc with rfl|rfl|rfl
    · obtain ⟨w, hw, hb, -⟩ := ld_s_cand hp hX hf hu safe base rows init he hj 0
      exact ⟨w, hw, hb⟩
    · exact ld_o_cand hp hX hf hu safe base rows init he hj
    · exact ld_e_cand hp hX hf hu base rows init he hj
  have hwd : ∀ {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
      {grp : CtaGroup} {dst : Option Loc} {da n : Nat},
      X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩ →
      d.1 / L.block = e.1 / L.block → X.TLd e a vals sh → WaitBefore L X .waitLd e d :=
    fun hd hc hl => (ldst_before_dealloc hp hX hf safe base hd hc).1 hl
  obtain ⟨src,hrs⟩ := readSourceOfCandidate hX hG hws
    (fun w' hw' => ld_order hp hX hf safe base rows init he hpc hj hw')
    (fun w' _ _ => source_live_ld hX ht hwd hld rfl) hw hb
  have hdone : X.MmaCell src (tcDataCell L t sh a j) → X.async.mmaDone src = true := fun hm => by
    obtain ⟨d0,s0,a0,m0,row,col,⟨pc0,h0⟩,-⟩ := hm
    rcases hrs.2.2.1 with (hdn | hpl) | ⟨⟨a',vals',sh',⟨pcs,hst⟩⟩,-⟩ |
        ⟨-,-,c,d,s,acc,mask,-,-,⟨pc',hy⟩,-⟩
    · exact hdn.done hX.tcCommit
    · obtain ⟨-,-,d,s,acc,mask,d',s',acc',mask',-,⟨pc',hy⟩,-⟩ := hpl
      cases get_tc_inj he hy
    · cases get_tc_inj h0 hst
    · cases get_tc_inj he hy
  obtain ⟨value,hv⟩ := wrote_of hX (fun d s acc mask hi hm => hCV _ d s acc mask hi hm hrs.2.2.1)
    hrs.2.1 hdone
  exact ⟨src,value,hrs,hv,hdone⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
