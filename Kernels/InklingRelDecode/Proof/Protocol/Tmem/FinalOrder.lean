-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Protocol.Bar.AlignedLanes
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ScratchRound
import Kernels.InklingRelDecode.Proof.Protocol.Shared.FinalWitness
public import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC

@[expose] public section

/-! # The final rendezvous of two data lanes of a CTA is one barrier-0 generation

The final `bar.sync 0` of a data lane is its first event at a final position. Two data lanes of a
CTA at the same barrier ordinal are at the same pc, so a lane cannot have a final rendezvous at a
smaller barrier-0 ordinal than another lane's: its event of that ordinal would be at the other's
final pc, a second final rendezvous. The two final rendezvous therefore have the same ordinal and
(`Shared.scratch_handoff`) every earlier event of one is before every later event of the other. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem lt_false (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy px py}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨px,.bar 0 none .sync⟩)
    (hy : X.get (y,iy) = some ⟨py,.bar 0 none .sync⟩) (fx : Lib.finalSync px = true)
    (fy : Lib.finalSync py = true)
    (lt : ((X.tr x).take ix).countP (Execution.isBarId 0) <
      ((X.tr y).take iy).countP (Execution.isBarId 0)) : False := by
  obtain ⟨j,ev,hj,hbj,hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 0)
    (show ((X.tr x).take ix).countP (Execution.isBarId 0) + 1 ≤ _ from lt)
  have hji : j < iy := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hji.le] at hcj
  have hget : X.get (y,j) = some ev := by
    change (X.tr y)[j]? = some ev
    rw [← List.getElem?_take_of_lt hji]
    exact hj
  obtain ⟨pcj,kj⟩ := ev
  obtain ⟨cnt,md,rfl⟩ : ∃ cnt mode, kj = .bar 0 cnt mode := by
    cases kj <;> simp [Execution.isBarId] at hbj
    rename_i id c md
    cases id <;> simp at hbj
    exact ⟨c,md,rfl⟩
  have isb : Execution.isBar ⟨px,.bar 0 none .sync⟩ = true := by simp [Execution.isBar]
  have isb' : Execution.isBar ⟨pcj,.bar 0 cnt md⟩ = true := by simp [Execution.isBar]
  have ordB := Protocol.Bar.zero_count_isBar hp hX hf safe cta lx ly hx hget hcj.symm
  have pcs := Protocol.Bar.data_bar_agree hp hX hf safe cta lx ly hx hget isb isb' ordB
  subst pcs
  have none := Export.final_first hp hX hy fy
  have mem : (⟨px,.bar 0 cnt md⟩ : Event) ∈ (X.tr y).take iy :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hji]; exact hget)
  exact List.countP_eq_zero.mp none _ mem fx

/-- **The final rendezvous of two data lanes of a CTA have the same barrier-0 ordinal.** -/
theorem final_ordinal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {x ix y iy px py}
    (cta : x / L.block = y / L.block) (lx : x % L.block < 128) (ly : y % L.block < 128)
    (hx : X.get (x,ix) = some ⟨px,.bar 0 none .sync⟩)
    (hy : X.get (y,iy) = some ⟨py,.bar 0 none .sync⟩) (fx : Lib.finalSync px = true)
    (fy : Lib.finalSync py = true) :
    ((X.tr x).take ix).countP (Execution.isBarId 0) =
      ((X.tr y).take iy).countP (Execution.isBarId 0) := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · exact lt_false hp hX hf safe cta lx ly hx hy fx fy lt
  · exact lt_false hp hX hf safe cta.symm ly lx hy hx fy fx gt

/-- **Every event of a data lane before its final rendezvous is before every event of another
data lane of the CTA after its final rendezvous.** -/
theorem before_final_after_final (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬ Race L X) {y h w u u' v pcu pch}
    (cta : h / L.block = y / L.block) (ly : y % L.block < 128) (lh : h % L.block < 128)
    (hy : X.get (y,u) = some ⟨pcu,.bar 0 none .sync⟩)
    (hh : X.get (h,u') = some ⟨pch,.bar 0 none .sync⟩) (fy : Lib.finalSync pcu = true)
    (fh : Lib.finalSync pch = true) (hw : w < u) (hv : u' < v) (pres : v < (X.tr h).length) :
    baseCausality L X (y,w) (h,v) :=
  Protocol.Shared.scratch_handoff hp hX hy hh cta.symm ly lh
    (final_ordinal hp hX hf safe cta.symm ly lh hy hh fy fh) hw hv pres

/-- **A lane of the CTA of a passed final rendezvous has a final rendezvous.** -/
theorem final_of_passed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h u' pch y} (hh : X.get (h,u') = some ⟨pch,.bar 0 none .sync⟩)
    (pass : u' + 1 < (X.tr h).length) (ord : 2 ≤ ((X.tr h).take u').countP (Execution.isBarId 0))
    (cta : y / L.block = h / L.block) :
    ∃ u p, X.get (y,u) = some ⟨p,.bar 0 none .sync⟩ ∧ Lib.finalSync p = true ∧
      2 ≤ ((X.tr y).take u).countP (Execution.isBarId 0) := by
  obtain ⟨⟨z,l⟩,eq,-,ev⟩ := Protocol.Shared.final_witness hp hX hh pass ord (h := y) cta
  change z = y at eq
  subst z
  rcases ev with ⟨pcx,ex⟩|⟨pcZ,mZ,hZ,hord⟩
  · obtain ⟨u,p,-,get,ord'⟩ := Export.exit_final_bar hp hX ex
    exact ⟨u,p,get,(Export.final_late hp hX get).mpr ord',ord'⟩
  · obtain ⟨md,_⟩ := Lib.recorded_bar hX hp.block hZ
    subst md
    exact ⟨l,pcZ,hZ,(Export.final_late hp hX hZ).mpr hord,hord⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
