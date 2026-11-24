-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvDecl

@[expose] public section

/-! # The MMA warp's broadcasts receive 7

The MMA warp broadcasts its warp index (`shfl.sync.idx` from lane 0) before each half of an
iteration and skips the half when the received word is not 7 (`Mma.Site.qkSkip`, `pvSkip`). By
DEP-WARP-SHFL the word is lane 0's operand at the same instance, or any value when lane 0 exited
before it (`Frame.shfl_src`).

* **The operand.** Every shuffle of a worker is the startup's broadcast or one of the MMA warp's
  two, and all three send the warp index (`worker_shfl`).
* **Lane 0 does not exit first.** Along a worker thread the shuffles are counted (`SH`, `sh_inv`):
  one after the startup; `1 + mmSh d` at an MMA state, where `mmSh` counts the halves whose
  broadcast is done and is `2 n` after the loop (`n` the CTA's `num_iters` when the loop runs,
  `MmLoop` its bounds, `mm_step`); `1 + 2 n` on warp 7 after the role (the exit path), `1` on the
  other workers. A broadcast of iteration `i` has at most `2 n` shuffles before it, so lane 0's
  exit has more (`mma_recv7`).

`mma_recv7`: every broadcast of a thread of warp 7 at an MMA state receives `b32 7`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The shuffle positions -/

def shflPcs : List Nat :=
  [17, 202, 244, 286, 1261, 1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255, 2464, 2512, 2603]

theorem kernel_shfl_pcs : OpPcsFast kernel.code Op.isShfl shflPcs = true := by decide +kernel

theorem shfl_pc {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : Execution.isShfl e = true) : pc ∈ shflPcs :=
  OpPcsFast.mem kernel_shfl_pcs hc (fires_shfl_op hf hs)

local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem worker_shflS : ∀ s : Proof.Worker.Site, s.pc ∈ shflPcs → s = .shfl := by site_cls
theorem idle_shflS : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ shflPcs → False := by site_cls
theorem loader_shflS : ∀ s : Proof.Loader.Site, s.pc ∈ shflPcs → False := by site_cls
theorem exitsite_shflS : ∀ s : Proof.WComp.ExitSite, s.pc ∈ shflPcs → False := by site_cls
theorem mma_shflS : ∀ s : Proof.Mma.Site, s.pc ∈ shflPcs → s = .qkShfl ∨ s = .pvShfl := by
  site_cls

theorem worker_bar1S : ∀ s : Proof.Worker.Site, s.pc ∈ bar1Pcs → s ≠ .ldRole := by site_cls

/-! ### The MMA warp's count of broadcasts -/

/-- `num_iters` as the loop runs it: zero when the loop does not run. -/
def nRun (n : Nat) : Nat := if n = 0 ∨ 2147483646 < n then 0 else n

/-- The bounds of an MMA state: the iteration before the loop is 0; a QK state's iteration is
below `n`, a PV state's in `[1, n]`, and the loop runs (`n` in `[1, 2 ^ 31 - 2]`). -/
def MmLoop (d : Proof.Mma.D) : Prop :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => d.i = 0
  | .qkBar | .kvWait | .qkShfl | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip =>
    d.i < d.n ∧ 1 ≤ d.n ∧ d.n ≤ 2147483646
  | .pvBar | .pWait | .pvShfl | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip =>
    1 ≤ d.i ∧ d.i ≤ d.n ∧ 1 ≤ d.n ∧ d.n ≤ 2147483646
  | _ => True

/-- **The MMA warp's broadcasts done** before a state's event. -/
def mmSh (d : Proof.Mma.D) : Nat :=
  match d.site with
  | .setMaxReg | .ldNum | .bar0 => 0
  | .qkBar | .kvWait | .qkShfl => 2 * d.i - min d.i 1
  | .qkBar2 | .qkElect | .qk _ | .qkCommit | .qkSkip => 2 * d.i + 1 - min d.i 1
  | .pvBar | .pWait | .pvShfl => min (d.i + 1) d.n + d.i - 1
  | .pvBar2 | .pvElect | .pv _ | .pvCommit1 | .pvCommit2 | .pvSkip => min (d.i + 1) d.n + d.i
  | _ => 2 * nRun d.n

/-- A broadcast site of the MMA warp. -/
def isShS : Proof.Mma.Site → Bool
  | .qkShfl | .pvShfl => true
  | _ => false

set_option maxHeartbeats 4000000 in
/-- **An MMA step keeps the bounds and adds its broadcast.** -/
theorem mm_step {d d' : Proof.Mma.D} {e : Event} (hd : d.site ≠ .ldNum) (hL : MmLoop d)
    (h : Proof.Mma.next L g d e = some (some d')) :
    MmLoop d' ∧ d'.n = d.n ∧ mmSh d' = mmSh d + if isShS d.site then 1 else 0 := by
  obtain ⟨site, i, n, tm, pro⟩ := d
  cases site
  all_goals first
    | exact absurd rfl hd
    | (simp only [Proof.Mma.next, Proof.Mma.start, Proof.Mma.afterQk, Proof.Mma.iterNext,
         Proof.Mma.qkNext, Proof.Mma.pvNext] at h
       simp only [MmLoop] at hL
       repeat' split at h
       all_goals first
         | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
         | (cases h; done)
         | (simp only [Option.some.injEq] at h
            subst h
            first
              | (simp [MmLoop, mmSh, isShS, nRun] at hL ⊢; omega)
              | (simp [MmLoop, mmSh, isShS, nRun] at hL ⊢; split_ifs <;> omega)
              | (simp [MmLoop, mmSh, isShS, nRun] at hL ⊢)
))

/-! ### The count along a worker thread -/

/-- The CTA's `num_iters`. -/
abbrev nIt (Q : Params) (L : Launch) (g : Nat) : Nat :=
  Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x)

/-- The broadcasts of a worker's role: `2 n` on warp 7 (the MMA warp), none on the others. -/
def sh7 (Q : Params) (L : Launch) (g : Nat) : Nat :=
  if g % L.block / 32 = 7 then 2 * nRun (nIt Q L g) else 0

/-- **The shuffles of a worker thread** before a state, with the barrier-1 events `c`: one at the
dispatch before a role (at most one barrier-1 event) and in the loader and the idle role,
`1 + mmSh d` at an MMA state, `1 + sh7` at the dispatch after a role and on the exit path. -/
def SH (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Nat → Prop
  | (.inr ⟨.inl (.worker _), .worker _⟩, _), c, s => (c ≤ 1 → s = 1) ∧ (2 ≤ c → s = 1 + sh7 Q L g)
  | (.inr ⟨.inl (.worker _), .idle _⟩, _), _, s => s = 1
  | (.inr ⟨.inl (.worker _), .loader _ _⟩, _), _, s => s = 1
  | (.inr ⟨.inl (.worker _), .mma d _⟩, _), _, s =>
    s = 1 + mmSh d ∧ MmLoop d ∧ (d.site ≠ .setMaxReg → d.site ≠ .ldNum → d.n = nIt Q L g)
  | (.inr ⟨.inl (.worker _), .exit _⟩, _), _, s => s = 1 + sh7 Q L g
  | _, _, _ => True

theorem mma_ret {d : Proof.Mma.D} {P P' : Proof.Loader.Pro} {e : Event}
    (h : Proof.WComp.next L g (.mma d P) e = some (some (.worker ⟨.loop, P'⟩))) :
    d.site = .setMaxRegInc := by
  by_contra hs
  rw [Proof.EvW.next_mma_map P hs] at h
  obtain ⟨a, -, ha⟩ := Proof.EvW.map_map_some h
  cases ha

theorem countP_snoc1 (P : Event → Bool) (l : List Event) (e : Event) :
    (l ++ [e]).countP P = l.countP P + if P e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

set_option maxHeartbeats 1000000 in
/-- **The shuffles of a worker thread along it.** -/
theorem sh_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      SH Q L g σ (((X.tr g).take k).countP (Execution.isBarId 1))
        (((X.tr g).take k).countP Execution.isShfl) := by
  have hb : L.block = 256 := hp.block
  have hb128 : L.block ≠ 128 := by omega
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'0
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hσ' := hσ'0
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake, countP_snoc1, countP_snoc1]
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      have hget : X.get (g, k) = some e := he
      have hb1 : (if Execution.isBarId 1 e then 1 else 0) = b1At ((thread Q L g).pc σ) :=
        bar1_iff hc hf hb128
      have hsh : ∀ hs : Execution.isShfl e = true, (thread Q L g).pc σ ∈ shflPcs :=
        fun hs => shfl_pc hc hf hs
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup enters the worker at the loop's head after its shuffle
        rw [next_start] at hn
        obtain ⟨s', hs', rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j hj
          rcases j with (_ | _) | _
          · trivial
          · have hx : ∃ r, Startup.enterOf s' = some r := by
              simp only [Code.gatedExit] at hj
              cases hq : Startup.enterOf s' with
              | none => rw [hq] at hj; simp at hj
              | some r => exact ⟨r, rfl⟩
            obtain ⟨r, hr⟩ := hx
            have hsr : s'.site = .enter r := by
              simp only [Startup.enterOf] at hr
              split at hr <;> simp_all
            have hshs := succ_enter hs' hsr
            have hev : Startup.Ev L g st e := by
              cases o with
              | none => exact absurd (fires_none_ends hf) hnE
              | some u => exact frag_ev hp hg hJ hat hi hc hf
            obtain ⟨site, tm0, x0, w0⟩ := st
            simp only at hshs
            subst hshs
            simp only [Startup.Ev] at hev
            obtain ⟨recv, ok, rfl⟩ := hev
            have hS : StartRef ⟨.shfl, tm0, x0, w0⟩ n := hJ
            have hn0 : n .shfl = 0 := hS.1
            have hfc := fcount hk0 .shfl
            simp only [cls] at hfc
            have hn0' : ((X.tr g).take k).countP Execution.isShfl = 0 := by
              rw [← hfc]; exact hn0
            have hC1 : ((X.tr g).take k).countP (Execution.isBarId 1) = 0 :=
              w1_inv hp hX hg k hlt _ hk0
            refine ⟨fun _ => ?_, fun h2 => ?_⟩
            · simp [hn0', Execution.isShfl]
            · simp [hC1, Execution.isBarId] at h2
          · trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hW : WSite (b32 0) d := hJ.2.2.1
          have hw7 : g % L.block / 32 < 8 := by
            have := Nat.mod_lt g (show 0 < L.block by omega); omega
          have hRI : RIt d _ := ri_inv hp hX hg k hlt _ hk0
          have hRI' : RIt σw' _ := ri_inv hp hX hg (k + 1) hk _ hσ'0
          rw [htake, countP_snoc1] at hRI'
          have hW1 : _ % 3 = wph d := w1_inv hp hX hg k hlt _ hk0
          cases d with
          | worker wd =>
            have hns : Execution.isShfl e = false := by
              cases hq : Execution.isShfl e
              · rfl
              · have := worker_shflS wd.site (hsh hq)
                obtain ⟨hs, -⟩ := hW
                rcases hs with h | h | h | h | h <;> rw [this] at h <;> cases h
            have hR0' : (_ ≤ 1 → _ = 1) ∧ (2 ≤ _ → _ = 1 + sh7 Q L g) := hR0
            simp only [hns, Bool.false_eq_true, ite_false, Nat.add_zero]
            by_cases hl : wd.site = .ldRole
            · -- the dispatch: a read, into a role or the exit path
              obtain ⟨site, P⟩ := wd
              simp only at hl
              subst hl
              obtain ⟨a, bs, hk', d'', -, hst⟩ := dispatch_succ hσw
              have hW1' : _ % 3 = 1 := hW1
              have hnb : Execution.isBarId 1 e = false := by
                obtain ⟨pc, kd⟩ := e; simp only at hk'; subst hk'; rfl
              simp only [hnb, Bool.false_eq_true, ite_false, Nat.add_zero] at hRI' ⊢
              cases σw' with
              | worker w' => exact hR0'
              | idle d' => exact hR0'.1 (by simp only [RIt] at hRI hRI'; omega)
              | loader d' P' => exact hR0'.1 (by simp only [RIt] at hRI hRI'; omega)
              | mma d' P' =>
                have hs := w_next_mma hσw
                have hc1 := hR0'.1 (by simp only [RIt] at hRI hRI'; omega)
                obtain ⟨site', i', n', tm', pro'⟩ := d'
                simp only at hs
                subst hs
                -- the role's first state
                have hi0 : i' = 0 := by
                  unfold Proof.WComp.roleStart at hst
                  repeat' split at hst
                  all_goals simp only [Option.some.injEq, reduceCtorEq,
                    Proof.WComp.WSt.mma.injEq, Proof.Mma.D.mk.injEq] at hst
                  exact hst.1.2.1.symm
                exact ⟨by rw [hc1]; simp [mmSh], by simp [MmLoop, hi0], fun h => absurd rfl h⟩
              | exit x => exact hR0'.2 (by simp only [RIt] at hRI'; omega)
            · rw [Proof.EvW.next_worker_map hl] at hσw
              obtain ⟨w', -, ha⟩ := Proof.EvW.map_map_some hσw
              subst ha
              -- a barrier-1 event of the dispatch is not at one barrier-1 event
              refine ⟨fun h1 => hR0'.1 (by split at h1 <;> omega), fun h2 => ?_⟩
              by_cases hbb : Execution.isBarId 1 e = true
              · simp only [hbb, ite_true] at h2 ⊢
                have hpc : wd.site.pc ∈ bar1Pcs := by
                  have := hb1
                  simp only [hbb, ite_true, b1At] at this
                  split at this
                  · assumption
                  · omega
                have hne1 : wph (.worker wd) ≠ 1 := by
                  obtain ⟨site, P⟩ := wd
                  have h1 := worker_bar1S site hpc
                  have hbad : site ≠ .bad0 := hRI.2.2.2.1
                  revert h1 hbad
                  cases site <;> simp [wph]
                rcases (by omega : ((X.tr g).take k).countP (Execution.isBarId 1) = 1 ∨
                    2 ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) with h | h
                · exact absurd (by rw [← hW1, h]) hne1
                · exact hR0'.2 h
              · simp only [hbb, Bool.false_eq_true, ite_false, Nat.add_zero] at h2 ⊢
                exact hR0'.2 h2
          | idle di =>
            have hns : Execution.isShfl e = false := by
              cases hq : Execution.isShfl e
              · rfl
              · exact (idle_shflS di.site (hsh hq)).elim
            have hR0' : _ = 1 := hR0
            simp only [hns, Bool.false_eq_true, ite_false, Nat.add_zero]
            have hw6 : g % L.block / 32 < 6 := role_warp hp hX hg k hlt _ hk0
            have h7 : sh7 Q L g = 0 := by simp [sh7]; omega
            rcases role_succ (σ := .idle di) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : di.site ≠ .inc := by intro h; simp [wph, idPh, h] at hph
              rw [Proof.EvW.next_idle_map hs] at hσw
              obtain ⟨a, -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              exact hR0'
            · exact ⟨fun _ => hR0', fun _ => by rw [h7]; exact hR0'⟩
          | loader dl P =>
            have hns : Execution.isShfl e = false := by
              cases hq : Execution.isShfl e
              · rfl
              · exact (loader_shflS dl.site (hsh hq)).elim
            have hR0' : _ = 1 := hR0
            simp only [hns, Bool.false_eq_true, ite_false, Nat.add_zero]
            have hw6 : g % L.block / 32 = 6 := role_warp hp hX hg k hlt _ hk0
            have h7 : sh7 Q L g = 0 := by simp [sh7]; omega
            rcases role_succ (σ := .loader dl P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : dl.site ≠ .setMaxInc := by intro h; simp [wph, ldPh, h] at hph
              rw [Proof.EvW.next_loader_map P hs] at hσw
              obtain ⟨d', -, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              exact hR0'
            · exact ⟨fun _ => hR0', fun _ => by rw [h7]; exact hR0'⟩
          | mma dm P =>
            obtain ⟨hS0, hL0, hN0⟩ := (hR0 : _ = 1 + mmSh dm ∧ MmLoop dm ∧ _)
            have hw7' : g % L.block / 32 = 7 := role_warp hp hX hg k hlt _ hk0
            have hsf : (if Execution.isShfl e then 1 else 0) = if isShS dm.site then 1 else 0 := by
              cases hq : Execution.isShfl e
              · -- no shuffle: no broadcast site
                cases o with
                | none => exact absurd (fires_none_ends hf) hnE
                | some u =>
                  have hev : Proof.EvW.MmShape L g dm e := frag_ev hp hg hJ hat hi hc hf
                  cases hs : isShS dm.site
                  · rfl
                  · exfalso
                    have : dm.site = .qkShfl ∨ dm.site = .pvShfl := by
                      revert hs; cases dm.site <;> simp [isShS]
                    rcases this with h | h <;> simp only [Proof.EvW.MmShape, h] at hev <;>
                      obtain ⟨recv, ok, rfl⟩ := hev <;> simp [Execution.isShfl] at hq
              · rcases mma_shflS dm.site (hsh hq) with h | h <;> simp [isShS, h]
            rcases role_succ (σ := .mma dm P) rfl hσw with ⟨-, hph⟩ | ⟨P', rfl⟩
            · have hs : dm.site ≠ .setMaxRegInc := by intro h; simp [wph, mmPh, h] at hph
              rw [Proof.EvW.next_mma_map P hs] at hσw
              obtain ⟨d', hmn, he2⟩ := Proof.EvW.map_map_some hσw
              subst he2
              by_cases hld : dm.site = .ldNum
              · -- the read of `num_iters`
                cases o with
                | none => exact absurd (fires_none_ends hf) hnE
                | some u =>
                have hev : Proof.EvW.MmShape L g dm e := frag_ev hp hg hJ hat hi hc hf
                simp only [Proof.EvW.MmShape, hld] at hev
                obtain ⟨ac, bs, rfl, hloc, hsz⟩ := hev
                have hw : 128 ≤ g % L.block := by omega
                have hbs := pair_read hp hX hget hw 1 (by rw [hloc]; norm_num [Nat.add_assoc]) hsz
                obtain ⟨site, i, nn, tm, pro⟩ := dm
                simp only at hld
                subst hld
                simp only [Proof.Mma.next, hbs, pairVal, rebuild_b32, Option.some.injEq] at hmn
                subst hmn
                have hlt31 := numIters_lt31 hp (Proof.ProA.cta_lt hp hg).2.2
                  (Proof.ProA.cta L g .x)
                simp only [isShS, Bool.false_eq_true, ite_false] at hsf
                refine ⟨by rw [hS0, hsf]; simp [mmSh], by simp only [MmLoop] at hL0 ⊢; exact hL0,
                  fun _ _ => ?_⟩
                simp only [Proof.Raw.word32Of_b32, Option.getD_some]
                exact Nat.mod_eq_of_lt (by omega)
              · obtain ⟨hL', hn', hsh'⟩ := mm_step hld hL0 hmn
                refine ⟨by rw [hS0, hsf, hsh']; omega, hL', fun h1 h2 => ?_⟩
                rw [hn']
                apply hN0
                · intro h; obtain ⟨site, i, nn, tm, pro⟩ := dm; simp only at h; subst h
                  simp [Proof.Mma.next] at hmn; rw [← hmn] at h2; exact h2 rfl
                · exact hld
            · -- the role's end returns to the dispatch with `2 n` broadcasts
              have hs := mma_ret hσw
              have hrc := role_count hp hX hg hlt rfl hk0
              simp only [wph, mmPh, hs] at hrc
              have hnb : Execution.isBarId 1 e = false := by
                have := hb1
                have hp' : (thread Q L g).pc (.inr ⟨.inl (.worker w), .mma dm P⟩, n) =
                    dm.site.pc := rfl
                rw [hp', hs] at this
                cases hq : Execution.isBarId 1 e
                · rfl
                · simp [hq, b1At] at this; revert this; decide
              simp only [isShS, hs, Bool.false_eq_true, ite_false] at hsf
              simp only [hnb, hsf, Bool.false_eq_true, ite_false, Nat.add_zero]
              have hmm : mmSh dm = 2 * nRun (nIt Q L g) := by
                simp only [mmSh, hs]
                rw [hN0 (by rw [hs]; nofun) (by rw [hs]; nofun)]
              refine ⟨fun h => by simp at hrc; omega, fun _ => ?_⟩
              rw [hS0, hmm, sh7, ite_eq_left_of_eq_true _ _ (eq_true hw7')]
          | exit x =>
            obtain ⟨x', rfl⟩ := exit_succ hσw
            have hns : Execution.isShfl e = false := by
              cases hq : Execution.isShfl e
              · rfl
              · exact (exitsite_shflS x.site (hsh hq)).elim
            simp only [hns, Bool.false_eq_true, ite_false, Nat.add_zero]
            exact hR0
      · exact hJ.elim

/-! ### The broadcast's source -/

/-- **A default-partition state is of a lane of warps 0 to 3.** -/
theorem dp_lane :
    ∀ k, ∀ {tm : Nat} {bw : Value} {d : (Code.withStubs (frag Q L g) Startup.Entry.pc
      (.inl (.dp tm bw))).D} {n : Cls → Nat},
      Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), d⟩, n)) →
        g % L.block < 128 := by
  intro k
  induction k with
  | zero =>
    intro tm bw d n hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    cases Option.some.inj (Option.some.inj hσ)
  | succ k ih =>
    intro tm bw d n hσ'
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [Frame.stateAt_succ he] at hσ'
      rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
      · rw [hk0] at hσ'; cases hσ'
      · rw [hk0] at hσ'; cases hσ'
      · rw [hk0] at hσ'
        have hn : (thread Q L g).next σ e = some (some _) := hσ'
        obtain ⟨x, n0⟩ := σ
        rcases x with st | ⟨i, d0⟩
        · rw [next_start] at hn
          obtain ⟨s', -, hs'⟩ := mm_some hn
          simp only [Prod.mk.injEq] at hs'
          obtain ⟨hs', -⟩ := hs'
          simp only [Code.enter] at hs'
          split at hs'
          · rename_i j hj
            cases hs'
            simp only [Code.gatedExit] at hj
            cases hq : Startup.enterOf s' with
            | none => rw [hq] at hj; simp at hj
            | some r =>
              rw [hq] at hj
              simp only [Option.map_some, Option.some.injEq] at hj
              split at hj
              · rename_i ii hsel
                cases hj
                cases r with
                | dp =>
                  simp only [sel] at hsel
                  split at hsel
                  · rename_i hG
                    simp only [Gate, Bool.and_eq_true, decide_eq_true_eq] at hG
                    exact hG.2
                  · cases hsel
                | worker =>
                  simp only [sel] at hsel
                  split at hsel <;> cases hsel
              · cases hj
          · cases hs'
        · obtain ⟨d', hd'⟩ := next_same_role hn
          simp only at hd'
          have := (Sigma.mk.inj (Sum.inr.inj hd')).1
          subst this
          exact ih hk0
    · have ht : (X.tr g).take (k + 1) = (X.tr g).take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have heq : Frame.stateAt (thread Q L) X g (k + 1) = Frame.stateAt (thread Q L) X g k := by
        simp only [Frame.stateAt]; rw [ht]
      rw [heq] at hσ'
      exact ih hσ'

/-- **A worker's exit is fired from the exit path's return.** -/
theorem worker_exit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} (hE : X.get (h, j) = some ⟨pc, .exit⟩) (hw : 4 ≤ h % L.block / 32) :
    ∃ tm P n, Frame.stateAt (thread Q L) X h j =
      some (some (.inr ⟨.inl (.worker tm), .exit ⟨.ret, P⟩⟩, n)) := by
  have hb : L.block = 256 := hp.block
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hE (fun f h => by cases h)
  have hpc := ret_pc' hc hf rfl
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hm := startup_special st.site (List.mem_append_right _ hpc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h' | h' | h' <;>
      rw [show (thread Q L h).pc _ = st.site.pc from rfl, h'] at hpc <;>
      simp [retPcs, Startup.Site.pc] at hpc
  · rename_i i
    cases i with
    | dp tm bw =>
      have := dp_lane j hσ
      omega
    | worker w =>
      obtain ⟨P, hP⟩ := worker_state_special d (List.mem_append_right _ hpc)
      subst hP
      exact ⟨w, P, n, hσ⟩
  · exact hJ.elim

/-- **Every broadcast of the MMA warp receives `b32 7`**: the source, lane 0 of warp 7, made the
shuffle of the same instance (its exit has `1 + 2 n` shuffles before it, the broadcast at most
`2 n`), and every worker's shuffle sends its warp index. -/
theorem mma_recv7 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {mode : ShflMode} {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩) {tm : Value}
    {d : Proof.Mma.D} {P : Proof.Loader.Pro} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.worker tm), .mma d P⟩, n))) :
    recv = b32 7 := by
  have hb : L.block = 256 := hp.block
  have hb32 : L.block % 32 = 0 := by rw [hb]
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hw7 : g % L.block / 32 = 7 := role_warp hp hX hg k hlen _ hσ
  obtain ⟨σ, t, ins, o, hσ', hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  have hev : Proof.EvW.MmShape L g d ⟨pc, .shfl mode a b c recv ok⟩ := frag_ev hp hg hJ hat hi hc hf
  have hpc := shfl_pc hc hf (by simp [Execution.isShfl])
  have hsite := mma_shflS d.site hpc
  have hshape : mode = .idx ∧ b = 0 ∧ c = 31 := by
    rcases hsite with h | h <;> simp only [Proof.EvW.MmShape, h] at hev <;>
      obtain ⟨recv', ok', heq⟩ := hev <;>
      simp only [Event.mk.injEq, Kind.shfl.injEq] at heq <;> exact ⟨heq.2.1, heq.2.2.2.1,
        heq.2.2.2.2.1⟩
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  -- the broadcast's count
  obtain ⟨hS, hL, hN⟩ := (sh_inv hp hX hg k hlen _ hσ : _ = 1 + mmSh d ∧ MmLoop d ∧ _)
  have hdn : d.n = nIt Q L g := by
    apply hN <;> rcases hsite with h | h <;> rw [h] <;> nofun
  have hbound : 1 + mmSh d ≤ 2 * nRun (nIt Q L g) ∧ 1 ≤ nIt Q L g := by
    rcases hsite with h | h <;> simp only [MmLoop, mmSh, h] at hL ⊢ <;> rw [← hdn] <;>
      simp only [nRun] <;> split_ifs <;> omega
  have hcv : ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = 0 :=
    List.countP_eq_zero.mpr fun e he' => by
      obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he')
      simp [novote hX (i := (g, i)) hi']
  have IH : Frame.GoodUpTo (thread Q L) (fun g => Ref Q L g) X (g % L.block / 32)
      (((X.tr g).take k).countP Execution.isShfl + 0) :=
    fun h j hh _ => good_all' hp hX hh.1 j
  obtain ⟨j, pc', b', c', r', o', hget, hG, hcs, -⟩ := Frame.shfl_src (C := thread Q L)
    (J := fun g => Ref Q L g) hb32 hX hg rfl he rfl IH
    (fun _ _ _ _ _ he' hv _ _ _ => by rw [novote hX he'] at hv; cases hv)
    (fun h j' pcx hh hcta hx _ hs _ => by
      have hw4 : 4 ≤ h % L.block / 32 := by rw [hh.2]; omega
      obtain ⟨tm', P', n', hσx⟩ := worker_exit hp hX hx hw4
      have hlx : j' < (X.tr h).length := (List.getElem?_eq_some_iff.mp hx).1
      have hSx : _ = 1 + sh7 Q L h := sh_inv hp hX hh.1 j' hlx _ hσx
      have h7 : sh7 Q L h = 2 * nRun (nIt Q L g) := by
        simp only [sh7, hh.2, hw7, ite_true, nIt]
        have : h / L.block = g / L.block := hcta
        simp only [Proof.ProA.cta, this]
      unfold Frame.cnt at hs
      omega)
  -- the source's shuffle sends the warp index
  have hsl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hsT, hsW, hsC, -, -⟩ := Frame.lane_facts hb32 hg hw7 hsl
  set src := g - laneOf L g + (shflSource ShflMode.idx (laneOf L g) 0 31).1 with hsrc
  have hlj : j < (X.tr src).length := (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨σs, ts, inss, os, hσs, hJs, hats, his, hcs', hfs⟩ :=
    ev_state hp hX hget (fun f h => by cases h)
  cases os with
  | none => exact absurd (fires_none_ends hfs) (by simp [Ends])
  | some us =>
  have hpcs := shfl_pc hcs' hfs (by simp [Execution.isShfl])
  have hevs := frag_ev hp hsT hJs hats his hcs' hfs
  obtain ⟨xs, ns'⟩ := σs
  rcases xs with st | ⟨_ | r, ds⟩
  · -- the startup's shuffle
    have hs : st.site = .shfl := by
      revert hpcs
      obtain ⟨site, tm0, x0, w0⟩ := st
      cases site with
      | enter r => exact fun _ => hJs.elim
      | shfl => exact fun _ => rfl
      | _ => intro h; simp [shflPcs, Startup.Site.pc] at h
    have h' : Startup.Ev L src st _ := hevs
    simp only [Startup.Ev, hs] at h'
    obtain ⟨recv', ok', heq⟩ := h'
    simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at heq
    simp [heq.2.1, hsW]
  · rename_i i
    cases i with
    | dp tm' bw' =>
      have := dp_lane j hσs
      omega
    | worker w =>
      cases ds with
      | mma dm Pm =>
        have h' : Proof.EvW.MmShape L src dm _ := hevs
        rcases mma_shflS dm.site hpcs with h | h <;> simp only [Proof.EvW.MmShape, h] at h' <;>
          obtain ⟨recv', ok', heq⟩ := h' <;>
          simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at heq <;>
          simp [heq.2.1, Proof.Worker.warpOf, hsW]
      | worker ww =>
        exfalso
        have := worker_shflS ww.site hpcs
        obtain ⟨hs0, -⟩ := (hJs.2.2.1 : WSite _ (.worker ww))
        rcases hs0 with h | h | h | h | h <;> rw [this] at h <;> cases h
      | idle di => exact (idle_shflS di.site hpcs).elim
      | loader dl Pl => exact (loader_shflS dl.site hpcs).elim
      | exit x => exact (exitsite_shflS x.site hpcs).elim
  · exact hJs.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
