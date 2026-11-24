-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputOps
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaCounts
public import Kernels.Fp16Gemm8192.Proof.Thread.RoleWarp

@[expose] public section

/-! # The input ring's copies and MMAs of a thread

A tensor issue of a followed thread is the loader's load at block `b`, part `j`: the copy of the
map's box into tile `j` of slot `b % 4` of the loader's CTA, with three of its issues there per
successful empty poll before it, less the loads of the batch still to issue
(`tensor_issue_fact`, the loader's `LoaderTasks.Counts` before the issue). An MMA of a followed
thread is the MMA thread's MMA at slot `s`, K step `j`, of its warp's operands, after one more
successful full poll of the slot than its commits there (`mma_issue_fact`, `Mma.Counts`). A
commit of the MMA thread to slot `s`'s empty barrier follows the slot's four MMAs, right before
it (`mma_batch_fact`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An event that the trace continues after is not undefined behaviour, so a trace's events
before a given event are not. -/
theorem run_noUb_take {K : Kernel} {A : List Assumption} {g : Nat} :
    ∀ {t : TState} {l : List Event} {o : Option TState}, Run K A L g t l o →
      ∀ k, k < l.length → LoaderTasks.NoUb (l.take k)
  | _, _, _, .nil _, k, hk => by simp at hk
  | _, _, _, .step (e := e) (rest := rest) _ hst hr, k, hk => by
    cases k with
    | zero => intro x hx; simp at hx
    | succ k =>
      intro x hx f hf
      rw [List.take_succ_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · obtain ⟨m, -, hfire⟩ := hst
        obtain ⟨pc, kd⟩ := x
        simp only at hf
        subst hf
        exact fires_some_not_ub hfire pc f rfl
      · exact run_noUb_take hr k (by simp at hk; omega) x hx f hf
  | _, _, _, .last _ _, k, hk => by
    have : k = 0 := by simp at hk; omega
    subst this
    intro x hx
    simp at hx

/-- **The loader's copies.** A tensor issue of a followed thread is the loader's load at block
`b`, part `j`: the copy of the A or B map's box into tile `j` of slot `b % 4` of the loader's
CTA, completing on the slot's full barrier, after three issues there per earlier successful poll
of the slot's empty barrier, less the batch's loads still to issue. -/
theorem tensor_issue_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {a : Nat} {sp : TensorCopy.Spec} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some d))
    (hk : e.kind = .tensorIssue a sp) :
    ∃ (l : Loader.D) (b : Fin 8) (j : Fin 3), d = .inr (.loader l) ∧ l.site = .load b j ∧
      sp.mbar = InputRing.fullLoc L (g / L.block / 2) (InputRing.slotOf b) ∧
      (∃ base cls origin, sp = stageCopy (Fp16Gemm8192.mapA base cls) origin (g / L.block)
        (L.sharedBase + InputRing.stageOff (InputRing.slotOf b).val j.val) sp.mbar true .two ∧
        L.tensorMaps a = some ⟨1, Fp16Gemm8192.mapA base cls⟩ ∧
        (L.paramObjects "gemm_kernel_param_0" = some (mapParam "gemm_kernel_param_0", a) ∨
          L.paramObjects "gemm_kernel_param_1" = some (mapParam "gemm_kernel_param_1", a))) ∧
      TensorCopy.RoutingOk L (g / L.block) sp ∧
      ((X.tr g).take k).countP (issuesTo (Loader.fullOf L g (InputRing.slotOf b))) + 3 =
        3 * okPolls (Loader.emptyOf L g (InputRing.slotOf b)) ((X.tr g).take k) + j.val := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hop : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact absurd hk (fires_notTensor (eventTmpl_notTensor h) hfire a sp)
    · rfl
  obtain ⟨l, b, j, rfl, hs⟩ := load_state (OpPcsFast.mem kernel_load_pcs hc hop)
  cases o with
  | none => exact absurd hk (fires_none_notTensor hfire a sp)
  | some u =>
    obtain ⟨a', sp', he', hm, base, cls, origin, hsp, hmap, hpar, hroute⟩ :=
      Loader.load_stage hpre hg b j hs hat hc hfire
    rw [he'] at hk
    simp only [Kind.tensorIssue.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨l, b, j, rfl, hs, hm, ⟨base, cls, origin, hsp, hmap, hpar⟩, hroute, ?_⟩
    have c : LoaderTasks.Counts L g l ((X.tr g).take k) :=
      LoaderTasks.run hpre hg htr k (.inr (.loader l)) hσ
    obtain ⟨o', hrun⟩ := hX.thr g hg
    have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨c1, -⟩ := c.exact (by simp [hs, Loader.Site.done])
      (run_noUb_take hrun k hklt)
    have h1 := c1 (InputRing.slotOf b)
    simp only [Loader.remaining, Loader.drained, hs, ↓reduceIte] at h1
    have := j.isLt
    omega

/-- **The MMA thread's MMAs.** An MMA of a followed thread is the MMA thread's MMA at slot `s`,
K step `j`, of its warp's A tile and the B tile of slot `s`, after one more successful poll of
the slot's full barrier than its commits to the slot's empty barrier. -/
theorem mma_issue_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some d)) (hk : e.kind = .tc (.mma dst sp acc mask)) :
    ∃ (m : Mma.D) (s j : Fin 4), d = .inr (.mma m) ∧ m.site = .mma s j ∧ g / L.block % 2 = 0 ∧
      sp = InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val j.val ∧
      ((X.tr g).take k).countP (commitsTo (emptyAt L g s)) + 1 =
        okPolls (Mma.fullOf L g s) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, s, j, rfl, hs⟩ := mma_state (OpPcsFast.mem kernel_mma_pcs hc (fires_tcMma_op hfire hk))
  have hlead : g / L.block % 2 = 0 := by
    rcases hinv.2.2 with h | h | h | h <;> first | exact h | (rw [hs] at h; cases h)
  have he' := Mma.mma_event hpre hg s j hs hat hc hfire
  rw [he'] at hk
  simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
  obtain ⟨-, rfl, -, -⟩ := hk
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp] at hw
  refine ⟨m, s, j, rfl, hs, hlead, by rw [hw.1], ?_⟩
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have h := hC.commit s
  simp only [Mma.pendingCommit, hs, decide_true, ↓reduceIte] at h
  exact h

/-- The state before a commit to slot `s` is the slot's last MMA. -/
theorem Mma.next_commit_pred {m m' : Mma.D} {e : Event} (hn : Mma.next L g m e = some (some m'))
    {s : Fin 4} (h : m'.site = .commit s) : m.site = .mma s 3 := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h; split_ifs at h))
  all_goals (try simp_all)
  all_goals (try (apply Fin.ext; omega))

/-- The state before the MMA of K step `j + 1` of a slot is its MMA of K step `j`. -/
theorem Mma.next_mma_pred {m m' : Mma.D} {e : Event} (hn : Mma.next L g m e = some (some m'))
    {s : Fin 4} (j : Fin 3) (h : m'.site = .mma s ⟨j.val + 1, by omega⟩) :
    m.site = .mma s ⟨j.val, by omega⟩ := by
  obtain ⟨site, w, q, fp, ap, cp, r, x⟩ := m
  cases site
  all_goals simp only [Mma.next] at hn
  all_goals (repeat' split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq, Option.map_eq_some_iff] at hn)
  all_goals (try obtain ⟨_, -, rfl⟩ := hn)
  all_goals (try (unfold Mma.endOfTrip at h; split_ifs at h))
  all_goals (try simp_all)
  all_goals (try exact Fin.ext h.2)

/-- An MMA state with an MMA or commit site after an event: the state before it is an MMA state
whose step is that event. -/
theorem stateAt_mma_pred {g k : Nat} {e : Event} (he : (X.tr g)[k]? = some e) {m' : Mma.D}
    (hσ : Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.mma m'))))
    (hs : m'.site ≠ .elect ∧ m'.site ≠ .exitArrive) :
    ∃ m, Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) ∧ Mma.next L g m e =
      some (some m') := by
  rw [Frame.stateAt_succ he] at hσ
  cases h : Frame.stateAt (code L) X g k with
  | none => rw [h] at hσ; cases hσ
  | some σ =>
    rw [h] at hσ
    simp only [Option.bind_some] at hσ
    cases σ with
    | none => cases hσ
    | some d =>
      change (code L g).next d e = _ at hσ
      rcases d with p | (l | m | sd | cs)
      · rcases Prologue.next_mma hσ with h' | h'
        · exact absurd h' hs.1
        · exact absurd h' hs.2
      · obtain ⟨l', -, hd⟩ := next_of_loader hσ; cases hd
      · obtain ⟨m'', hn, hd⟩ := next_of_mma hσ
        simp only [Sum.inr.injEq, Prologue.Role.mma.injEq] at hd
        subst hd
        exact ⟨m, rfl, hn⟩
      · obtain ⟨s', -, hd⟩ := next_of_sched hσ; cases hd
      · obtain ⟨c', -, hd⟩ := next_of_cons hσ; cases hd

/-- The event a state at an MMA site fires is that MMA. -/
theorem mma_site_event (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g k : Nat}
    {e : Event} {m : Mma.D} {s t : Fin 4} (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some (.inr (.mma m)))) (hs : m.site = .mma s t) :
    ∃ pc dst acc mask, e = ⟨pc, .tc (.mma dst
      (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val t.val) acc mask)⟩ := by
  obtain ⟨tt, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain rfl := Mma.mma_event hpre hg s t hs hat hc hfire
  have hw := role_warp hpre hX hg k (List.getElem?_eq_some_iff.mp he).1.le _ hσ
  simp only [roleWarp] at hw
  exact ⟨_, _, _, _, by rw [hw.1]⟩

/-- One step back from an MMA state at a slot's MMA of K step `t + 1`, or at its commit (`t = 3`):
the state before is at the slot's MMA of K step `t`. -/
theorem mma_back {g k : Nat} {m' : Mma.D} {s t : Fin 4} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g (k + 1) = some (some (.inr (.mma m'))))
    (hs : (t.val = 3 ∧ m'.site = .commit s) ∨ ∃ h : t.val < 3, m'.site =
    .mma s ⟨t.val + 1, by omega⟩) :
    ∃ m, Frame.stateAt (code L) X g k = some (some (.inr (.mma m))) ∧ m.site = .mma s t := by
  have he : (X.tr g)[k]? = some (X.tr g)[k] := List.getElem?_eq_getElem hk
  have hs' : m'.site ≠ .elect ∧ m'.site ≠ .exitArrive := by
    rcases hs with ⟨_, hh⟩ | ⟨_, hh⟩ <;> rw [hh] <;> simp
  obtain ⟨m, hm, hn⟩ := stateAt_mma_pred he hσ hs'
  refine ⟨m, hm, ?_⟩
  rcases hs with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · rw [Mma.next_commit_pred hn hh]; congr; exact Fin.ext (by simp [ht])
  · exact Mma.next_mma_pred hn ⟨t.val, ht⟩ hh

/-- A state at an MMA or commit site is not the first: the thread starts in its prologue. -/
theorem mma_state_pos {g k : Nat} {m : Mma.D} (hσ : Frame.stateAt (code L) X g k =
    some (some (.inr (.mma m)))) :
    0 < k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rw [stateAt_zero] at hσ; cases hσ
  · exact h

/-- **The MMAs of a commit.** A commit of the MMA thread to slot `s`'s empty barrier follows the
slot's four MMAs, right before it: the MMA of K step `t` is `4 - t` events before the commit,
with the same commits to the slot before it. -/
theorem mma_batch_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g jc : Nat} {e : Event} {m : Mma.D} {sp : TcCommit.Spec} {s : Fin 4} (hg : g < L.threads)
    (he : X.get (g, jc) = some e) (hσ : Frame.stateAt (code L) X g jc = some (some (.inr (.mma m))))
    (hk : e.kind = .tc (.commit sp)) (hm : sp.mbar = emptyAt L g s) :
    4 ≤ jc ∧ ∀ t : Fin 4, ∃ pc dst acc mask, X.get (g, jc - 4 + t.val) =
        some ⟨pc, .tc (.mma dst (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val t.val)
          acc mask)⟩ ∧
      ((X.tr g).take (jc - 4 + t.val)).countP (commitsTo (emptyAt L g s)) =
        ((X.tr g).take jc).countP (commitsTo (emptyAt L g s)) ∧
      ((X.tr g).take (jc - 4 + t.val)).countP (commitsTo (emptyAt L g s)) + 1 =
        okPolls (Mma.fullOf L g s) ((X.tr g).take (jc - 4 + t.val)) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨tt, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hsite : m.site = .commit s := by
    have h := commitsTo_iff_site hpre hg hat hc hfire s
    have hct : commitsTo (emptyAt L g s) e = true := by
      obtain ⟨pc, kd⟩ := e
      simp only at hk
      subst hk
      simp [commitsTo, hm]
    rw [hct] at h
    exact of_decide_eq_true h.symm
  have hlen : jc < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  -- Four steps back.
  obtain ⟨k3, rfl⟩ : ∃ k3, jc = k3 + 1 := ⟨jc - 1, by have := mma_state_pos hσ; omega⟩
  obtain ⟨m3, h3, hs3⟩ := mma_back (t := 3) (by omega) hσ (.inl ⟨rfl, hsite⟩)
  obtain ⟨k2, rfl⟩ : ∃ k2, k3 = k2 + 1 := ⟨k3 - 1, by have := mma_state_pos h3; omega⟩
  obtain ⟨m2, h2, hs2⟩ := mma_back (t := 2) (by omega) h3 (.inr ⟨by decide, hs3⟩)
  obtain ⟨k1, rfl⟩ : ∃ k1, k2 = k1 + 1 := ⟨k2 - 1, by have := mma_state_pos h2; omega⟩
  obtain ⟨m1, h1, hs1⟩ := mma_back (t := 1) (by omega) h2 (.inr ⟨by decide, hs2⟩)
  obtain ⟨k0, rfl⟩ : ∃ k0, k1 = k0 + 1 := ⟨k1 - 1, by have := mma_state_pos h1; omega⟩
  obtain ⟨m0, h0, hs0⟩ := mma_back (t := 0) (by omega) h1 (.inr ⟨by decide, hs1⟩)
  have hev : ∀ (i : Nat) (mi : Mma.D) (t : Fin 4), i < (X.tr g).length →
      Frame.stateAt (code L) X g i = some (some (.inr (.mma mi))) → mi.site = .mma s t →
      ∃ pc dst acc mask, X.get (g, i) = some ⟨pc, .tc (.mma dst
        (InputRing.mmaSpec L (g / L.block) (g % L.block / 32) s.val t.val) acc mask)⟩ := by
    intro i mi t hi hσi hsi
    have hei : X.get (g, i) = some (X.tr g)[i] := List.getElem?_eq_getElem hi
    obtain ⟨pc, dst, acc, mask, hk'⟩ := mma_site_event hpre hX hg hei hσi hsi
    exact ⟨pc, dst, acc, mask, by rw [hei, hk']⟩
  obtain ⟨p0, d0, a0, q0, e0⟩ := hev k0 m0 0 (by omega) h0 hs0
  obtain ⟨p1, d1, a1, q1, e1⟩ := hev (k0 + 1) m1 1 (by omega) h1 hs1
  obtain ⟨p2, d2, a2, q2, e2⟩ := hev (k0 + 2) m2 2 (by omega) h2 hs2
  obtain ⟨p3, d3, a3, q3, e3⟩ := hev (k0 + 3) m3 3 (by omega) h3 hs3
  have hstep : ∀ i pc dst spec acc mask, X.get (g, i) = some ⟨pc, .tc (.mma dst spec acc mask)⟩ →
      ((X.tr g).take (i + 1)).countP (commitsTo (emptyAt L g s)) =
        ((X.tr g).take i).countP (commitsTo (emptyAt L g s)) := by
    intro i pc dst spec acc mask hi
    rw [List.take_add_one, show (X.tr g)[i]? = _ from hi]
    simp [commitsTo]
  have hpol : ∀ (i : Nat) (mi : Mma.D) (t : Fin 4),
      Frame.stateAt (code L) X g i = some (some (.inr (.mma mi))) → mi.site = .mma s t →
      ((X.tr g).take i).countP (commitsTo (emptyAt L g s)) + 1 =
        okPolls (Mma.fullOf L g s) ((X.tr g).take i) := by
    intro i mi t hσi hsi
    have hC : Mma.Counts L g mi ((X.tr g).take i) := threadCounts_run hpre hg htr i _ hσi
    have h := hC.commit s
    simp only [Mma.pendingCommit, hsi, decide_true, ↓reduceIte] at h
    exact h
  have o0 := hpol _ _ _ h0 hs0
  have o1 := hpol _ _ _ h1 hs1
  have o2 := hpol _ _ _ h2 hs2
  have o3 := hpol _ _ _ h3 hs3
  have c0 := hstep _ _ _ _ _ _ e0
  have c1 := hstep _ _ _ _ _ _ e1
  have c2 := hstep _ _ _ _ _ _ e2
  have c3 := hstep _ _ _ _ _ _ e3
  have c0' : ((X.tr g).take (k0 + 1)).countP (commitsTo (emptyAt L g s)) =
      ((X.tr g).take k0).countP (commitsTo (emptyAt L g s)) := c0
  have c1' : ((X.tr g).take (k0 + 2)).countP (commitsTo (emptyAt L g s)) =
      ((X.tr g).take (k0 + 1)).countP (commitsTo (emptyAt L g s)) := c1
  have c2' : ((X.tr g).take (k0 + 3)).countP (commitsTo (emptyAt L g s)) =
      ((X.tr g).take (k0 + 2)).countP (commitsTo (emptyAt L g s)) := c2
  have c3' : ((X.tr g).take (k0 + 4)).countP (commitsTo (emptyAt L g s)) =
      ((X.tr g).take (k0 + 3)).countP (commitsTo (emptyAt L g s)) := c3
  refine ⟨by omega, fun ⟨t, ht⟩ => ?_⟩
  have hidx : k0 + 1 + 1 + 1 + 1 - 4 + t = k0 + t := by omega
  simp only [hidx]
  rw [show k0 + 1 + 1 + 1 + 1 = k0 + 4 by omega]
  interval_cases t
  · exact ⟨p0, d0, a0, q0, e0, by simp only [Nat.add_zero]; omega, o0⟩
  · exact ⟨p1, d1, a1, q1, e1, by omega, o1⟩
  · exact ⟨p2, d2, a2, q2, e2, by omega, o2⟩
  · exact ⟨p3, d3, a3, q3, e3, by omega, o3⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
