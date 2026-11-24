-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Lemmas.Step.TmemPair
public import Lemmas.Tmem.PairProtocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Interface.Assumptions
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceTrace
import Lemmas.Kernel.ProgressDescent
import Lemmas.Protocol.NamedBarSources
import Lemmas.Step.SetMaxNReg
import Lemmas.Step.WarpLanes

public section

/-! # Recording the allocator's actual warp-wide request -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Step Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem member_thread {w : WarpRequest} {group : CtaGroup} (hv : w.Valid L X group)
    (lane l : Fin 32) :
    warpLane L (w.event L lane).1 l.val = (w.event L l).1 := by
  have hLt : w.warp * 32 + lane.val < L.block := by
    have := hv.2.1
    have := lane.isLt
    omega
  have hMod : (w.event L lane).1 % L.block = w.warp * 32 + lane.val := by
    change (w.cta * L.block + w.warp * 32 + lane.val) % L.block = _
    rw [Nat.add_assoc, Nat.add_comm (w.cta * L.block), Nat.mul_comm w.cta L.block,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLt]
  have hLane : PTX.laneOf L (w.event L lane).1 = lane.val := by
    rw [PTX.laneOf, hMod, Nat.mul_comm w.warp 32, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt lane.isLt]
  rw [warpLane, hLane]
  simp only [WarpRequest.event, Nat.add_sub_cancel]

private theorem covered_same_ordinal (hX : Consistent L kernel Assumptions.all mem0 X)
    {e f : EvId} {k : Nat} (hw : SameWarp L e.1 f.1) (hE : X.TcK e k)
    (hF : X.TcK f k) (hCovered : Covered L X e) : Covered L X f := by
  obtain ⟨ws, hDone, w, hMem, lane, hLane⟩ := hCovered
  obtain ⟨grp, hv⟩ := hDone.valid hX.tmemPair hMem
  obtain ⟨j, hJ⟩ := hv.2.2.2
  have hK := hJ lane
  rw [hLane] at hK
  have hEq : j = k := hK.2.symm.trans hE.2
  subst j
  let l : Fin 32 := ⟨PTX.laneOf L f.1, Nat.mod_lt _ (by decide)⟩
  have hThread := member_thread hv lane l
  rw [hLane, PTX.Step.warpLane_of_sameWarp hw] at hThread
  have hSame : (w.event L l).1 = f.1 := hThread.symm
  have hIndex : (w.event L l).2 = f.2 := by
    have hEvent := hJ l
    have hPair : w.event L l = (f.1, (w.event L l).2) := Prod.ext hSame rfl
    rw [hPair] at hEvent
    exact Execution.TcK.unique hEvent hF
  exact ⟨ws, hDone, w, hMem, l, Prod.ext hSame hIndex⟩

/-- A fully issued one-CTA warp request is covered in a maximal execution. -/
theorem resource_covered_of_issued {g tag n k : Nat} {dst : Option Loc}
    (hpre : Pre P L mem0) (hmax : Maximal L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hg : g < L.threads) (hWarp : warpOf L g = 0) (hN : n < 3)
    (hOps : ∀ h, SameWarp L g h →
      ∃ i, X.get (h, i) = some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩ ∧
        X.TcK (h, i) k ∧ opsAt X h i = n)
    (hKey : X.TcK (g, (X.tr g).length - 1) k) :
    Covered L X (g, (X.tr g).length - 1) := by
  let action := opAct 0 n
  let cta := g / L.block
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hZero : g % L.block / 32 = 0 := by
    simpa only [warpOf, tidOf_eq hpre, hpre.block] using hWarp
  have hLane (l : Fin 32) : warpThread L g l.val = warpLane L g l.val := by
    unfold warpThread warpLane
    rw [PTX.sub_laneOf]
  have hAt (l : Fin 32) : SameWarp L g (warpThread L g l.val) := by
    rw [hLane]
    exact (PTX.Step.sameWarp_lane hb hg l.isLt).1
  by_contra hMissing
  have ops (l : Fin 32) :
      X.get (warpThread L g l.val, (X.tr (warpThread L g l.val)).length - 1) =
        some ⟨tag, .tc (.resource .one dst action.request)⟩ ∧
      X.TcK (warpThread L g l.val, (X.tr (warpThread L g l.val)).length - 1) k ∧
      opsAt X (warpThread L g l.val) ((X.tr (warpThread L g l.val)).length - 1) = n ∧
      ¬ Covered L X (warpThread L g l.val, (X.tr (warpThread L g l.val)).length - 1) := by
    let h := warpThread L g l.val
    have hSame := hAt l
    obtain ⟨i, hi, hiK, hiN⟩ := hOps h hSame
    have hFree : ¬ Covered L X (h, i) := fun hc =>
      hMissing (covered_same_ordinal hmax.1 (PTX.sameWarp_symm hSame) hiK hKey hc)
    have hPos : i < (X.tr h).length := PTX.len_of_get hi
    have hIndex : i = (X.tr h).length - 1 := by
      by_contra hn
      have hLater : i + 1 < (X.tr h).length := by omega
      exact hFree (hmax.1.tmemPairBlocking.covered
        ⟨tag, .one, dst, _, hi, by
          cases (opAct 0 n).request <;> first | trivial | exact .inl rfl⟩ hLater)
    rw [← hIndex]
    exact ⟨hi, hiK, hiN, hFree⟩
  let r := ownerRecord L X g tag dst action
  have hReady : CompletionReady L X [r.own] := by
    intro w hm prev group hv hbefore i hi
    obtain rfl := List.mem_singleton.mp hm
    have hValid : r.own.Valid L X .one := by
      refine ⟨?_, ?_, fun l => (ops l).1, k, fun l => (ops l).2.1⟩
      · exact PTX.NamedBar.cta_lt hg
      · change (g % L.block / 32 + 1) * 32 ≤ L.block
        rw [hZero, hpre.block]
        decide
    obtain ⟨a, ha, hA⟩ := recorded_of_before hmax.1.tmemPair hmax.1.tmemPairBlocking
      hv hValid hbefore
    have he' := hv.2.2.1 0
    have hGroup := (ResourceEvents.ordinal hpre hmax.1
      (hs _ (Frame.lt_of_get hmax.1 he')).machine he'
      (Frame.event_state hs hmax.1 ht he' (by simp)).choose_spec).2.1
    have hGrpA : a.group = .one := by
      have haGet := ((hmax.1.tmemPair.1 _).1 a ha).2.2.2.2.1 0
      rw [hA, he'] at haGet
      exact (TcKind.resource.inj (Kind.tc.inj
        (congrArg Event.kind (Option.some.inj haGet)))).1.symm.trans hGroup
    exact ⟨[a.own], .inl ⟨prev.cta, a, ha, hGrpA, rfl⟩, a.own, by simp, hA ▸ hi⟩
  have hLeader : warpThread L g 0 = cta * L.block := by simp [warpThread, cta, hZero]
  obtain ⟨h0, _, hOrd0, hFree0⟩ := ops 0
  change X.get (warpThread L g 0, (X.tr (warpThread L g 0)).length - 1) = _ at h0
  change opsAt X (warpThread L g 0) ((X.tr (warpThread L g 0)).length - 1) = n at hOrd0
  change ¬ Covered L X (warpThread L g 0, (X.tr (warpThread L g 0)).length - 1) at hFree0
  rw [hLeader] at h0 hOrd0 hFree0
  have hRun := Safety.run_before_resource hpre hmax.1 hs ht hN hOrd0 h0 hFree0
    (r := r) rfl
  obtain ⟨Y, hY, hLe, _, hSize⟩ := warp_entry_counted hmax.1 hg hb
    (fun l => (ops l).1) ⟨k, fun l => (ops l).2.1⟩ (fun l => (ops l).2.2.2)
    hReady hRun (Interface.all_wf_effects hmax.1 le_recordEntry rfl rfl rfl)
  exact hmax.not_grows ⟨Y, hY, hLe, hSize⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
