-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Iface.Objects
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Cluster.Unit
import Lemmas.Flow.TcTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

inductive CommitSite where | qk | empty | done | final

def CommitSite.site : CommitSite → Site
  | .qk => .qkCommit | .empty => .pvCommit1 | .done => .pvCommit2 | .final => .finCommit

def CommitSite.reg : CommitSite → Nat
  | .qk => 549 | .empty => 567 | .done => 568 | .final => 572

def CommitSite.offset (s : CommitSite) (i : Nat) : Nat :=
  match s with
  | .qk => Iface.sReady ⟨i % 2, by omega⟩
  | .empty => Iface.kvEmpty ⟨(i-1) % 3, by omega⟩
  | .done => Iface.oDone
  | .final => Iface.oFinal

def CommitSite.spec (s : CommitSite) (L : Launch) (g i : Nat) : TcCommit.Spec :=
  let c := g / L.block
  ⟨.one, ⟨.shared,c,L.sharedBase + s.offset i⟩, 1, c, 1⟩

private theorem commit_code (s : CommitSite) :
    ∃ guard, kernel.code[s.site.pc]? = some ⟨guard,.tcCommit .one s.reg 0 none⟩ := by
  cases s
  · exact ⟨_,Flow.code_2499⟩
  · exact ⟨_,Flow.code_2546⟩
  · exact ⟨_,Flow.code_2548⟩
  · exact ⟨_,Flow.code_2553⟩

theorem commit_shape {Q L g m i v regs w t ins e o} (hp : Pre Q L m) (hg : g < L.threads)
    (s : CommitSite) (hat : (code L g regs w).AtD ⟨s.site,i,v⟩ t)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    e.kind = .tc (.commit (s.spec L g i)) := by
  obtain ⟨guard,hins⟩ := commit_code s
  obtain rfl := Option.some.inj (hc.symm.trans hins)
  obtain ⟨_,_,_,_,hR⟩ := hat
  have hr : t.regs s.reg = some (b32 (L.sharedBase + s.offset i)) := by
    have hm : s.reg ∈ Flow.live s.site.pc := by cases s <;> decide
    have hval := holds_mem hR (mem_factsFrom (val := valueOf L regs w ⟨s.site,i,v⟩) hm)
    rw [hval]
    cases s <;> simp only [CommitSite.offset, Iface.sReady, Iface.kvEmpty, ← Nat.add_assoc] <;> rfl
  have hbase := hp.sharedRange
  have hal := hp.sharedAlignment
  have hoff : s.offset i < 213340 ∧ s.offset i % 8 = 0 := by
    cases s <;> simp [CommitSite.offset,Iface.sReady,Iface.kvEmpty,Iface.oDone,Iface.oFinal] <;>
      omega
  have hgrid : g / L.block < L.grid :=
    Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hn : g / L.block < L.nclusters := hp.nclusters ▸ hgrid
  have hplaces : ∀ k, (L.clusterPlaces k).shape = ⟨1,1,1⟩ := by
    intro k
    rw [hp.clusterPlaces, hp.clusterNctaid]
    rfl
  have ht := tc_commit (group := .one) hr (by unfold sharedBytes at hbase; omega)
    (by omega) hg (s := s.spec L g i) (by
      simp [TcCommit.resolve, CommitSite.spec, Launch.rankOfCta_unit hplaces hn,
        Launch.clusterOfCta_unit hplaces hn, Launch.clusterStart_unit hplaces,
        Launch.clusterSizeOf_unit hplaces, hp.launchValid.1, hgrid])
  change Fires s.site.pc (tcCommitTmpl L g t (.tcCommit .one s.reg 0 none)) e o at hf
  rw [ht] at hf
  exact congrArg Event.kind hf.1

end PTX.Kernels.InklingRelDecode.Proof.Mma
