-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmStartInPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The low-stage Bias column receives the sign bit of the stage trip difference. -/
def warmBiasResidualBit (p : Params) (batch tile : Nat) : Nat :=
  vPrimingResidual p batch tile / 2^31

theorem warmBiasResidualBit_le (p : Params) (batch tile : Nat) :
    warmBiasResidualBit p batch tile ≤ 1 := by
  have h := Nat.mod_lt
    (min ((p.kLength batch+127)/128)
      ((p.kLength batch-p.qLength batch+256*tile+128+127)/128) +
      2^32-Mma.trips p batch tile) (by decide : 0 < 2^32)
  change vPrimingResidual p batch tile < 2^32 at h
  unfold warmBiasResidualBit
  omega

private theorem warmResidualBitSetup {l : Launch} {g residue : Nat} (h : residue < 2^32) :
    Seg kernel [] l g 1 912 [(1089,b32 residue)] 913 [(1117,b32 (residue/2^31))] := by
  intro t ht
  seg_fp ht using
    (nf_simp [Nat.shiftRight_eq_div_pow]
     all_goals omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g/l.block < tilePrefix p p.batch*p.heads)
include hp hX hg hw hl writes hCTA

set_option maxRecDepth 10000 in
/-- A later warm event reaches the actual first loop entry with all launch Bias
coordinates and the low-stage residual bit. -/
theorem warmFirstWithBiasRoleOfEvent {e : Event} (he : X.get (warpLane l g src,j) = some e)
    (hLate : 917 ≤ e.pc) (hWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧ ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174,b32 0),(1117,b32 (warmBiasResidualBit p batch co.1))] ++
          warmStartFrame p l batch (co.2/6) trips (warpIndex l g) (thread % l.block) ++
          warmBiasRoots p batch co.1 co.2 ++
          [(123,.pred (decide (warpIndex l g ≠ 14)))]) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,hTwo,pos,hBefore,s,ending,hs,hr,hRank⟩ :=
    loaderWarmArmWithBiasRoleOfEventRanked hp hX hg hw hl writes hCTA he (by omega) hWarm hSafe
  let co := assignedCoordinates p batch (g/l.block)
  let thread := warpLane l g src
  let trips := Mma.trips p batch co.1
  let F := warmStartFrame p l batch (co.2/6) trips (warpIndex l g) (thread % l.block) ++
    warmBiasRoots p batch co.1 co.2 ++
    [(123,.pred (decide (warpIndex l g ≠ 14)))]
  let residue := vPrimingResidual p batch co.1
  have hResidue : residue < 2^32 := Nat.mod_lt _ (by decide)
  have hRoot : (1089,b32 residue) ∈ F := by simp [F,warmBiasRoots,residue]
  have hHeld : Holds s.regs F := hs.2.2.2.2.2
  obtain ⟨a,ha,haAt⟩ := (warmResidualBitSetup (l := l) (g := thread) hResidue).apply
    (hs.mono ⟨holds_mem hHeld hRoot,trivial⟩)
  obtain ⟨haCore,haFrame⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hs.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl ha
  let G := (1117,b32 (warmBiasResidualBit p batch co.1)) :: F
  have haG : At a 913 G := haAt.mono
    ⟨haAt.2.2.2.2.1,holdsSchedulerFrame hHeld haFrame (fun _ hm => List.mem_map_of_mem hm)⟩
  obtain ⟨b,hbStep,hbAt⟩ := warmCounterSeedCore (l := l) (g := thread) a (haG.mono trivial)
  obtain ⟨hbA,hbFrame⟩ := loaderLinear (regs := G.map Prod.fst)
    (by decide) (by decide) haG.1 (by set_option maxRecDepth 100000 in kernel_rfl) rfl hbStep
  have hbG : At b 914 ((7174,b32 0)::G) :=
    hbAt.mono ⟨hbAt.2.2.2.2.1,holdsSchedulerFrame haG.2.2.2.2 hbFrame
      (fun _ hm => List.mem_map_of_mem hm)⟩
  have hbRun := hr.after_local_nonempty (run_rtg (run_comp haCore hbA))
    (traceAfterObservedEvent he hBefore)
  have hAudit : ∀ branch, ((kernel.code.drop 914).take 3).all
      (fun ins => loaderPipelineCutOp 914 917 branch
        (((7174,b32 0)::G).map Prod.fst) ins.op) = true := by
    intro branch
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨c,passed,stop,_,hc,hcRun,hcRank,hcBefore⟩ :=
    prefixQuietCut (stop := 917) (by decide) hAudit
      (by set_option maxRecDepth 100000 in kernel_rfl) ⟨_,Flow.code_917,rfl⟩
      hbG hbRun he hBefore hLate hSafe
  exact ⟨batch,hb,hLo,hHi,hTwo,pos+passed.length,hcBefore,c,stop,
    hc,hcRun,hcRank.trans hRank⟩


set_option maxRecDepth 10000 in
/-- A later warm event reaches the actual first loop entry with all launch Bias
coordinates and the low-stage residual bit. -/
theorem warmFirstWithBiasOfEvent {e : Event} (he : X.get (warpLane l g src,j) = some e)
    (hLate : 917 ≤ e.pc) (hWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let co := assignedCoordinates p batch (g/l.block)
      let thread := warpLane l g src
      let trips := Mma.trips p batch co.1
      2 ≤ trips ∧ ∃ pos ≤ j, ∃ s ending,
        At s 917 ([(7174,b32 0),(1117,b32 (warmBiasResidualBit p batch co.1))] ++
          warmStartFrame p l batch (co.2/6) trips (warpIndex l g) (thread % l.block) ++
          warmBiasRoots p batch co.1 co.2) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 := by
  obtain ⟨batch,hb,hLo,hHi,hTwo,pos,hPos,s,ending,hs,hr,hRank⟩ :=
    warmFirstWithBiasRoleOfEvent hp hX hg hw hl writes hCTA he hLate hWarm hSafe
  refine ⟨batch,hb,hLo,hHi,hTwo,pos,hPos,s,ending,hs.mono ?_,hr,hRank⟩
  exact ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,((holds_append ..).mp hs.2.2.2.2.2.2).1⟩

end PTX.Kernels.TmlFa4Fwd.Loader
