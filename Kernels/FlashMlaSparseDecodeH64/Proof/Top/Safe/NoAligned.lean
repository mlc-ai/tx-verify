-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Aligned
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TcAligned
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.ReqOnce
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode

@[expose] public section

/-! # ERR-ALIGNED: aligned collectives are warp-uniform

The safety class of Core's `Unsafe` this file owns (`AlignedMismatch`), by class: the code has no
cluster barrier (`noClusterEvent`) and no warp matrix instruction (`noMatrixEvent`); the
`setmaxnreg` class holds because every thread makes one request, its first (`request_first`), at
its warpgroup's pc (`request_pc`), and an `exit` follows it (`request_exit`); the barrier class
is the barrier rows' and ordinals' (`bar_pc`, `bar_unexited`); the warp-collective `tcgen05`
class is `tc_uniform` and `tc_unexited` (`Common/Export/TcAligned.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Proof MbarRow

variable {P : Params} {L : Launch} {mem0 : Mem0}

private theorem req_kind {pc : Nat} {k : Kind} (h : SetMaxNReg.isRequest ⟨pc, k⟩ = true) :
    ∃ inc n inst, k = .setMaxReg inc n inst := by
  cases k <;> simp_all [SetMaxNReg.isRequest]

/-- The requests of the lanes of a warp are at one pc. -/
private theorem req_pc (hp : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {e f : EvId} {pe pf : Nat} {ke kf : Kind}
    (hw : SameWarp L e.1 f.1) (he : X.get e = some ⟨pe, ke⟩) (hf : X.get f = some ⟨pf, kf⟩)
    (hme : SetMaxNReg.isRequest ⟨pe, ke⟩ = true) (hmf : SetMaxNReg.isRequest ⟨pf, kf⟩ = true) :
    pe = pf := by
  obtain ⟨inc, n, inst, rfl⟩ := req_kind hme
  obtain ⟨inc', n', inst', rfl⟩ := req_kind hmf
  have h1 := request_pc hp hX hFw hnu he
  have h2 := request_pc hp hX hFw hnu hf
  have hwe := warp_of_sameWarp hp hw
  omega

/-- **ERR-ALIGNED**: aligned collectives are warp-uniform. -/
theorem Safe.noAligned (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, hc⟩
  cases c with
  | tc =>
    rcases hc with hc | hc
    · obtain ⟨e, f, k, pc, pc', ke, kf, hw, ⟨⟨ev, he1, hev⟩, hk⟩, ⟨⟨fv, hf1, hfv⟩, hk'⟩, he, hf,
        hne⟩ := (AlignedClass.divergent_tc_iff L).mp hc
      rw [he] at he1
      rw [hf] at hf1
      cases he1
      cases hf1
      obtain ⟨hpc, hst⟩ := tc_uniform hp hX hFw hnu hw he hf hev hfv hk hk'
      exact hne.elim (fun h => h hpc) (fun h => h (hst ke kf rfl rfl))
    · obtain ⟨e, f, k, hw, ⟨⟨ev, he, hev⟩, hk⟩, ⟨⟨pcx, hxe⟩, hle⟩⟩ :=
        (AlignedClass.exited_tc_iff L).mp hc
      exact tc_unexited hp hX hFw hnu hw he hev hk hxe hle
  | bar =>
    have hB := hIn.bar hp X hX hFw
    have hO := hIn.barOrd hp X hX hFw
    rcases hc with hc | hc
    · obtain ⟨g, h, i, j, id, id', cnt, cnt', md, md', pc, pc', hw, he, hf, hk, ha, hne⟩ :=
        (AlignedClass.divergent_bar_iff L).mp hc
      exact hne (bar_pc hp hB hO hw he hf rfl rfl hk ha)
    · obtain ⟨e, f, k, hs, ⟨ev, he, hm⟩, rfl, hx⟩ := (AlignedClass.exited_bar_iff L).mp hc
      exact bar_unexited hp hX hFw hB hO hs he hm hx
  | cluster =>
    have hno : ∀ e ev, X.get e = some ev → isCluster ev = false := by
      intro e ⟨pc, k⟩ he
      cases k <;> try rfl
      rename_i op
      exact (noClusterEvent hX he).elim
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · rw [AlignedClass.member, hno _ _ he] at hme; cases hme
    · have hme' : isCluster ev = true := hme
      rw [hno _ _ he] at hme'; cases hme'
  | matrix =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, -, he, -, hme, -⟩ | ⟨e, f, ev, -, he, hme, -⟩
    · rw [AlignedClass.member, noMatrixEvent hX he] at hme; cases hme
    · have hme' : isMatrix ev = true := hme
      rw [noMatrixEvent hX he] at hme'; cases hme'
  | setMaxReg =>
    rcases hc with ⟨e, f, pe, pf, ke, kf, hw, he, hf, hme, hmf, -, -, hne⟩ |
      ⟨e, f, ev, -, he, hme, -, ⟨pc, hx⟩, hle⟩
    · have h1 := req_pc hp hX hFw hnu hw he hf hme hmf
      exact hne.elim (fun h => h h1) (fun h => h rfl)
    · obtain ⟨pe, ke⟩ := ev
      obtain ⟨inc, n, inst, rfl⟩ := req_kind hme
      have h0 := request_first hp hX hFw hnu he
      have h1 := request_exit hp hX hFw hnu hx
      have h2 : ((X.tr f.1).take f.2).countP SetMaxNReg.isRequest ≤
          (X.tr f.1).countP SetMaxNReg.isRequest := (List.take_sublist _ _).countP_le
      have h4 : (X.tr f.1).countP SetMaxNReg.isRequest ≤
          ((X.tr e.1).take e.2).countP SetMaxNReg.isRequest := hle
      omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
