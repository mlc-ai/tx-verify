-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions.WellFormed
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.PrologueTrace
public import Lemmas.Step.DrainInOrder
public import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Proof

private def startupPc (stage : Fin 3) : Nat := ![25, 34, 35] stage

private def startupValue (l : Launch) (g : Nat) (stage : Fin 3) : Value :=
  if stage.val = 0 then b32 l.sharedBase else b32 (warpIndex l g)

private def startupEvent (l : Launch) (g : Nat) (stage : Fin 3) : Event :=
  ⟨startupPc stage, .shfl .idx (startupValue l g stage) 0 31 (startupValue l g stage) true⟩

private theorem startupEvent_eq {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 3) {e : Event}
    (he : X.get (g, stage.val) = some e) : e = startupEvent l g stage := by
  fin_cases stage
  · exact firstSharedValue hp hX g hg he
  · exact secondWarpValue hp hX g hg he
  · exact thirdWarpValue hp hX g hg he

private theorem startupFires {l : Launch} {g dst : Nat} {stage : Fin 3} {t : TState}
    (hPc : t.pc = startupPc stage)
    (hOut : out kernel Assumptions.all l g t =
      .ev (broadcastTemplate t dst (startupValue l g stage))) (recv : Value) (ok : Bool) :
    EStep kernel Assumptions.all l g t
      ⟨startupPc stage, .shfl .idx (startupValue l g stage) 0 31 recv ok⟩
      (some (next (setReg t dst recv))) :=
  ⟨_, hOut, recv, ok, by rw [hPc], rfl⟩

private theorem startupTracesNext {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (stage : Fin 3) (hLen : (X.tr g).length = stage.val) :
    ∀ recv ok, ∃ t u o, Run kernel Assumptions.all l g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      EStep kernel Assumptions.all l g u
        ⟨startupPc stage, .shfl .idx (startupValue l g stage) 0 31 recv ok⟩ o := by
  intro recv ok
  obtain ⟨s, hStart, hAt⟩ := firstBroadcastWith (A := Assumptions.all) hp g
  have hStep₀ := startupFires (stage := 0) hAt.1 hStart.stop
  fin_cases stage
  · have hEmpty : X.tr g = [] := List.length_eq_zero_iff.mp hLen
    exact ⟨{}, s, _, hEmpty ▸ .nil _, hStart.steps, hStep₀ recv ok⟩
  · change (X.tr g).length = 1 at hLen
    have h₀ : 0 < (X.tr g).length := by omega
    have he : X.get (g, 0) = some (X.tr g)[0] := List.getElem?_eq_getElem h₀
    have hVal := startupEvent_eq hp hX hg 0 he
    have hTrace : X.tr g = [startupEvent l g 0] := by
      rw [← hVal]
      have hs := List.drop_eq_getElem_cons (i := 0) h₀
      have hd : (X.tr g).drop 1 = [] := List.drop_eq_nil_iff.mpr (by omega)
      simpa only [List.drop_zero, hd, Nat.zero_add] using hs
    let t := next (setReg s 2535 (b32 l.sharedBase))
    have hTpc : t.pc = 26 := by change s.pc + 1 = 26; rw [hAt.1]
    have hRun : Run kernel Assumptions.all l g {} (X.tr g) (some t) :=
      hTrace ▸ .step hStart.steps (hStep₀ _ true) (.nil _)
    obtain ⟨u, hLocal, hPc, hFault, hReg, _⟩ :=
      warpIndexLocalWith (A := Assumptions.all) hp g t hTpc hAt.2.2.2.1
    have hOut := startupOut (A := Assumptions.all) (.inl (by rw [hPc]; decide))
      (warpBroadcastOut (stage := 0) hp.block hPc hFault hReg)
    exact ⟨t, u, _, hRun, run_rtg hLocal, startupFires (stage := 1) hPc hOut recv ok⟩
  · change (X.tr g).length = 2 at hLen
    have h₀ : 0 < (X.tr g).length := by omega
    have h₁ : 1 < (X.tr g).length := by omega
    have he₀ : X.get (g, 0) = some (X.tr g)[0] := List.getElem?_eq_getElem h₀
    have he₁ : X.get (g, 1) = some (X.tr g)[1] := List.getElem?_eq_getElem h₁
    have hVal₀ := startupEvent_eq hp hX hg 0 he₀
    have hVal₁ := startupEvent_eq hp hX hg 1 he₁
    have hTrace : X.tr g = [startupEvent l g 0, startupEvent l g 1] := by
      have hDrop₀ := List.drop_eq_getElem_cons (i := 0) h₀
      have hDrop₁ := List.drop_eq_getElem_cons (i := 1) h₁
      have hNil : (X.tr g).drop 2 = [] := List.drop_eq_nil_iff.mpr (by omega)
      rw [show 1 + 1 = 2 by decide, hNil] at hDrop₁
      rw [List.drop_zero, show 0 + 1 = 1 by decide, hDrop₁, hVal₀, hVal₁] at hDrop₀
      exact hDrop₀
    let t := next (setReg s 2535 (b32 l.sharedBase))
    have hTpc : t.pc = 26 := by change s.pc + 1 = 26; rw [hAt.1]
    obtain ⟨u, hLocal, hPc, hFault, hReg, _⟩ :=
      warpIndexLocalWith (A := Assumptions.all) hp g t hTpc hAt.2.2.2.1
    have hOut₁ := startupOut (A := Assumptions.all) (.inl (by rw [hPc]; decide))
      (warpBroadcastOut (stage := 0) hp.block hPc hFault hReg)
    let v := next (setReg u 1673 (b32 (warpIndex l g)))
    have hVpc : v.pc = 35 := by change u.pc + 1 = 35; rw [hPc]
    have hStep₁ := startupFires (stage := 1) hPc hOut₁ (b32 (warpIndex l g)) true
    have hRun : Run kernel Assumptions.all l g {} (X.tr g) (some v) :=
      hTrace ▸ .step hStart.steps (hStep₀ _ true) (.step (run_rtg hLocal) hStep₁ (.nil _))
    have hOut₂ := startupOut (A := Assumptions.all) (.inl (by rw [hVpc]; decide))
      (warpBroadcastOut (stage := 1) hp.block hVpc hFault rfl)
    exact ⟨v, v, _, hRun, .refl, startupFires (stage := 2) hVpc hOut₂ recv ok⟩

private theorem startupShflK {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (stage : Fin 3) (hLen : stage.val < (X.tr g).length) :
    X.ShflK (g, stage.val) stage.val := by
  have he : X.get (g, stage.val) = some (X.tr g)[stage.val] := List.getElem?_eq_getElem hLen
  rw [startupEvent_eq hp hX hg stage he] at he
  refine ⟨⟨_, _, _, _, _, _, _, he⟩, ?_⟩
  change ((X.tr g).take stage.val).countP Execution.isShfl = stage.val
  calc
    _ = ((X.tr g).take stage.val).length := by
      apply List.countP_eq_length.mpr
      intro e hm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
      rw [List.getElem?_take] at hj
      split at hj
      · rename_i hj'
        rw [startupEvent_eq hp hX hg ⟨j, hj'.trans stage.isLt⟩ hj]
        rfl
      · cases hj
    _ = stage.val := by simp [Nat.min_eq_left hLen.le]

/-- A maximal execution performs all three initial broadcasts in every warp of the launch. -/
theorem startupBroadcastsProgress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Maximal l kernel Assumptions.all m X) :
    ∀ g < l.threads, 3 ≤ (X.tr g).length := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  suffices hAll : ∀ n ≤ 3, ∀ g < l.threads, n ≤ (X.tr g).length from hAll 3 le_rfl
  intro n hn
  induction n with
  | zero => intro g _; exact Nat.zero_le _
  | succ n ih =>
    intro g hg
    by_contra hnLen
    have hLen : (X.tr g).length = n := by
      have h := ih (by omega) g hg
      omega
    let stage : Fin 3 := ⟨n, by omega⟩
    have hWarp (h : Nat) (hs : SameWarp l g h) : (X.tr h).length = n := by
      have hh := hs.1.2.1
      have hlo := ih (by omega) h hh
      by_contra hn'
      have hlt : stage.val < (X.tr h).length := by dsimp [stage]; omega
      have hk := startupShflK hp hX.1 hh stage hlt
      obtain ⟨⟨pc, md, a, b, c, r, o, he⟩, _⟩ := id hk
      rcases Step.shfl_lane_of_ready hX.1 he hk (sameWarp_symm hs) with
        ⟨j, hj⟩ | ⟨j, pc, he, _⟩
      · have hi := Step.ShflK.lt_count hj
        have hb := List.countP_le_length (p := Execution.isShfl) (l := X.tr g)
        change n < (X.tr g).countP Execution.isShfl at hi
        omega
      · have hj : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
        have hj' : j < 3 := by omega
        have hEvent := startupEvent_eq hp hX.1 hg ⟨j, hj'⟩ he
        cases hEvent
    apply hX.not_grows
    apply Step.shfl_counted_extension hX.1 hBlock (fun h => startupValue l h stage)
      (fun _ => 0) (fun _ => 31) hg (pc := startupPc stage) (m := .idx)
    · intro h _
      exact .inr (fun ⟨_, _, _, hi⟩ => (noClcIssue hX.1 hi).elim)
    · intro h hs
      apply Step.Released.of_get
      intro ev he
      have hLast : (X.tr h).length - 1 < (X.tr h).length :=
        (List.getElem?_eq_some_iff.mp he).1
      have hn : (X.tr h).length - 1 < 3 := by have := hWarp h hs; omega
      rw [startupEvent_eq hp hX.1 hs.1.2.1 ⟨(X.tr h).length - 1, hn⟩ he]
      intro heq
      cases heq
    · intro h hs
      exact startupTracesNext hp hX.1 hs.1.2.1 stage (hWarp h hs)
    · intro ev h
      exact Assumptions.wfStep.quiet hX.1 le_appendLanes rfl (noNewRead_appendLanes h)

end PTX.Kernels.TmlFa4Fwd.Prologue
