-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsRdv
public import Kernels.InklingRelDecode.Proof.Protocol.VxLife

@[expose] public section

/-!
# The rendezvous of the softmax loads, on every prefix (`LdRdv`)

`Rd.SRdv` and `Rd.ORdv` (the `tcgen05.wait::ld` after the S load and after the rescale load is
causally before an event of thread 0 with at most `i / 2` arrivals on `p_ready (i % 2)`) are built
by `Rr.sRdv_of` and `Kk.oRdv_of` from `Complete L X`: thread 0 reaches its arrival of iteration `i`
(`Rr.sm_reaches_arrive` from its exit). `ldRdv_of` is the statement on every prefix, guarded as
`Hs.StRdv` is: when thread 0 has more than `i / 2` arrivals on `p_ready (i % 2)` (an event that
reads after the load, a QK or PV MMA of a later iteration, has polled them), the load's wait exists
and is before thread 0's arrival with `i / 2` earlier ones.

The proof is `Hs.stRdv_of` with the load in place of the store: thread 0's arrival of iteration
`i` follows its `bar21` of iteration `i` (a `bar.sync 0, 128`); the load's thread has a barrier-0
event of the same count (`Lk.member_of`), which is after the load by the counts (`Hs.cnt_at`:
the count of `ldS` and `ldO` of iteration `i` is at most that of `bar21`), so the wait after the
load (`Vx.ld_wait_after`) is before it and `Bar.bar128Causal` orders it before the arrival.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Px
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N (cnt0 C0 Dc nIt)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk (DecAgree)
open PTX.Kernels.InklingRelDecode.Proof.EvW (pReady)
open PTX.Kernels.InklingRelDecode.Proof.Hs (p0Of)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The rendezvous of the loads of CTA `c` on a prefix**: a softmax load of iteration `i` (at
`ldS` or `ldO`), when thread 0 has more than `i / 2` arrivals on `p_ready (i % 2)`, is followed by
its `tcgen05.wait::ld`, which is causally before thread 0's arrival with `i / 2` earlier ones. -/
def LdRdv (Q : Params) (L : Launch) (X : Execution) (c : Nat) : Prop :=
  ∀ {t sk pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape}, t < L.threads →
    t / L.block = c → St Q L X t sk = some (some (.d (.sm d))) →
    (d.site = .ldS ∨ d.site = .ldO) → X.get (t, sk) = some ⟨pc, .tc (.ld a vals sh)⟩ →
    d.i / 2 + 1 ≤ arrivals (pReady L c (d.i % 2)) (X.tr (p0Of L c)) →
    ∃ pcw e, X.get (t, sk + 1) = some ⟨pcw, .tc .waitLd⟩ ∧
      baseCausality L X (t, sk + 1) (p0Of L c, e) ∧
      arrivals (pReady L c (d.i % 2)) ((X.tr (p0Of L c)).take e) ≤ d.i / 2

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X) (hD : ∀ c j, DecAgree Q L X c j)
include hpre hX hf hD

/-- **`LdRdv`** of every CTA, on every prefix. -/
theorem ldRdv_of (c : Nat) : LdRdv Q L X c := by
  intro t sk pcl al d vl shl ht htc hσ hst hld hgd
  have hsk : sk < (X.tr t).length := len_of_get hld
  have hb2 : d.i % 2 < 2 := Nat.mod_lt _ (by omega)
  obtain ⟨hpc, hp0m⟩ := Hs.p0_div hpre c
  obtain ⟨kA, eA, heA, harrA, hcA⟩ := CtaBarrier.countP_index (xs := X.tr (p0Of L c))
    (p := arrivesOn (pReady L c (d.i % 2))) (n := d.i / 2) (by unfold arrivals at hgd; omega)
  have heA' : X.get (p0Of L c, kA) = some eA := heA
  have hg0 : p0Of L c < L.threads := event_thread_lt hX heA'
  have hkA : kA < (X.tr (p0Of L c)).length := len_of_get heA'
  obtain ⟨pcA, k⟩ := eA
  cases k with
  | arrive m tx cn rel sc =>
    simp only [arrivesOn, sourceArrive, decide_eq_true_eq] at harrA
    subst harrA
    rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg0 heA'
        ⟨_, _, _, _, _, rfl⟩ with
      ⟨dP, -, j, hj, -, hev⟩ | ⟨dA, hσA, hsA, -, hev⟩ | ⟨dL, P, -, hsL, hsh⟩
    · simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      obtain ⟨-, h, -⟩ := hev
      hs_loc h
    rotate_left
    · unfold EvW.LdShape at hsh
      rw [hsL] at hsh
      simp only [Event.mk.injEq, Kind.arrive.injEq] at hsh
      obtain ⟨-, h, -⟩ := hsh
      hs_loc h
    simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
    obtain ⟨-, hm, -⟩ := hev
    have hm' := hm
    simp only [EvW.pReady, EvD.pReadyOf, EvD.Bar.loc, EvD.Bar.off, EvW.barLoc, EvW.pReadyOff,
      Loc.mk.injEq, true_and] at hm'
    have hmod : dA.i % 2 = d.i % 2 := by omega
    have harr := (Rr.arr_cnt hpre hX hf hg0 hp0m kA hkA.le _ hσA).2 dA rfl (d.i % 2) hb2
    rw [hpc, ← hmod, Hs.below2_mod] at harr
    have hcA' : arrivals (pReady L c (d.i % 2)) ((X.tr (p0Of L c)).take kA) = d.i / 2 := hcA
    rw [hmod] at harr
    have hiA : dA.i = d.i := by omega
    rcases Sv.pred_sm hkA.le hσA with ⟨dt, rfl⟩ | ⟨k1, d1, e1, hk1, he1, hσ1, hn1⟩
    · simp [SmEntry.d0] at hsA
    obtain ⟨hs1, hi1⟩ := next_arrive hn1 hsA
    have he1' : X.get (p0Of L c, k1) = some e1 := he1
    have hev1 := Lk.bar_event hpre hX hf hg0 he1' hσ1 (by rw [hs1]; trivial)
    rw [hs1] at hev1
    have hb1 : X.IsBarrier (p0Of L c, k1) 0 (some 128) Sm.Site.bar21.pc := by
      show X.get (p0Of L c, k1) = _
      rw [he1', hev1]
    have hk1l : k1 ≤ (X.tr (p0Of L c)).length := by omega
    have hI1 := Sv.sm_inv_at hX hf he1' hσ1
    have hin : d1.i < nIt Q L (p0Of L c) := by
      have h26 := B0N.r26_numIters hpre hX hf hg0 he1' hσ1
      have := (hI1.late (by rw [hs1]; trivial)).2.2
      simp only [nIt]
      omega
    have htd : t % L.block < 128 := (hf.reach ht hσ).1
    have htc' : t / L.block = p0Of L c / L.block := by rw [htc, hpc]
    obtain ⟨a, pca, cna, hba, hcnta⟩ := Lk.member_of hpre hX hf hb1 (by simp only; omega)
      (by simp only; omega) htc' htd
      (fun hj => Hs.exit_bound hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hj)
    have hcn := Hs.b128_of hpre hX hf hD hg0 hk1l hσ1 hs1 hin htc' htd hba hcnta
    subst hcn
    have hba' : X.get (t, a) = some ⟨pca, .bar 0 (some 128) .sync⟩ := hba
    have hal : a < (X.tr t).length := len_of_get hba'
    have hC : C0 Q L t = C0 Q L (p0Of L c) := by simp only [C0, B0N.nbQ_cta (Q := Q) htc']
    have hDc : Dc Q L X (t / L.block) = Dc Q L X (p0Of L c / L.block) := by rw [htc']
    have hvt := Hs.cnt_at hpre hX hf hD ht hsk.le hσ
    have hv1 := Hs.cnt_at hpre hX hf hD hg0 hk1l hσ1
    rw [hC, hDc] at hvt
    have hRD : RD (Dc Q L X (p0Of L c / L.block)) d ≤
        RD (Dc Q L X (p0Of L c / L.block)) d1 := by
      rcases hst with hs | hs <;> simp [RD, postR, hs, hs1, ← hi1, hiA]
    have hRD' : ((RD (Dc Q L X (p0Of L c / L.block)) d : Nat) : Int) ≤
        ((RD (Dc Q L X (p0Of L c / L.block)) d1 : Nat) : Int) := by exact_mod_cast hRD
    have hcta : (cnt0 X t a : Int) = cnt0 X (p0Of L c) k1 := by exact_mod_cast hcnta
    have hle : (cnt0 X t sk : Int) ≤ cnt0 X t a := by
      rw [hcta, hvt, hv1, hs1, ← hi1, hiA]
      rcases hst with hs | hs <;> simp only [phi, hs] <;> (try split_ifs) <;> omega
    have hbar : Execution.isBarId 0 ⟨pca, .bar 0 (some 128) .sync⟩ = true := by
      simp [Execution.isBarId]
    have hsa : sk < a := by
      by_contra hlt
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hlt) with hlt | heq
      · have h1 := Hs.cnt0_le (X := X) t (show a + 1 ≤ sk by omega)
        rw [Hs.cnt0_succ hba', hbar] at h1
        simp at h1
        omega
      · subst heq
        rw [hld] at hba'
        cases hba'
    obtain ⟨pcw, hew⟩ := Vx.ld_wait_after hpre hX hf ht
      ⟨a, pca, _, hsa, hba', fun f h => by cases h⟩ hld
    have hwa : sk + 1 < a := by
      rcases Nat.lt_or_eq_of_le (show sk + 1 ≤ a by omega) with h | h
      · exact h
      · subst h
        rw [hba'] at hew
        cases hew
    have he1b : X.get (p0Of L c, k1) = some ⟨Sm.Site.bar21.pc, .bar 0 (some 128) .sync⟩ := by
      rw [he1', hev1]
    have hB := Bar.bar128Causal hpre hX hf.sound hf.tracked (g := t) (p := p0Of L c) (a := a)
      (y := k1) (before := sk + 1) (f := kA) ht hg0 htc' htd (by rw [hp0m]; omega) hba' he1b
      hcnta hwa (by omega) hkA
    exact ⟨pcw, kA, hew, hB, by rw [hcA']⟩
  | _ => simp [arrivesOn, sourceArrive] at harrA

end
end PTX.Kernels.InklingRelDecode.Proof.Px
