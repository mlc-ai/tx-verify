-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixPro
public import Kernels.InklingRelDecode.Proof.Interface.PrefixBias
public import Kernels.InklingRelDecode.Proof.Interface.PrefixBt
public import Kernels.InklingRelDecode.Proof.Interface.ClassSm
public import Kernels.InklingRelDecode.Proof.Thread.DCompFollows
public import Kernels.InklingRelDecode.Proof.Interface.PrefixShflD

@[expose] public section

/-!
# `Premises` from the prefix induction

`Premises` (`Premises.lean`) says that no thread's machine leaves its run at a value-dependent
event. The induction along each thread (`weakTracked_of`, `PrefixWeak.lean`) proves the machines
are tracked from the local fact `hnext`: at the state before an event, given `Good` at the thread's
earlier events and the launch bytes of the event's own read, the machine's successor is not
`some none`.

`Discharged s` lists the states whose `hnext` is proved here: the prologue's three request-word
loads, its exit to the softmax region (`bar18`), its 64 query loads (`PrefixPro.lean`), its six
block-table loads (`PrefixBt.lean`), the softmax region's 128 bias loads (`PrefixBias.lean`), the
epilogue's tile load, every state of the MMA warp (its machine follows the thread for every loaded
`num_iters` word and every received broadcast word), every state of the loader (its machine
follows the thread for every loaded word), every worker state but the dispatch of a worker whose
inherited Tensor Memory base word has no room for the 512 columns (`WComp.baseOk`; the dispatch
follows every role byte on every warp), every state of the common start (it follows every loaded
base word), the prologue's last event `bar18` with a good base word (`ProA.wGood`; on any other
word the prologue stops there), and every state of the prologue and of the softmax region at
which their machines never return `some none` (`ProA.next_follows`, `DComp.sm_next_follows`).
Every other followed state is a base-word stop (`discharged_or_stop`), which no thread reaches
(`Interface.tracked_holds`). `premises_of_tracked` assembles `Premises` from the tracking.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A query load does not leave the run.** -/
theorem pro_ldq_next_ne (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k0 k : Nat} (hk : k < 64)
    {dt : ProA.Dat} {e : Event} (hg : g < L.threads) (he : X.get (g, k0) = some e)
    (hσ : St Q L X g k0 = some (some (.d (.pro ⟨ProA.ldqSite k, dt⟩))))
    (hgood : ∀ j < k0, Good Q L mem0 X (g, j)) (hL : LaunchRead Q mem0 X (g, k0)) :
    (threadCode L g Q).next (.d (.pro ⟨ProA.ldqSite k, dt⟩)) e ≠ some none := by
  obtain ⟨d', hn, -⟩ := ldq_loaded_at hpre hX hS hT hk hg he hσ hgood hL
  refine next_pro_ne_of ?_ (by rw [hn]; simp)
  show ProA.ldqSite k ≠ ProA.Site.bar18
  interval_cases k <;> decide

/-- **The epilogue's tile load does not leave the run**: the load returns the 64 words of its
shape (`Epi.shape`). -/
theorem epi_ld_next_ne (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k : Nat} {d : Epi.D} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (hs : d.site = .ld) :
    (threadCode L g Q).next (.d (.epi d)) e ≠ some none := by
  obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState, hs])
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsh := Epi.shape hb (fired_epi hF)
  unfold Epi.Shape at hsh
  rw [hs] at hsh
  obtain ⟨vals, hlen, rfl⟩ := hsh
  rw [next_d]
  change ((Epi.next d _).map (Option.map DComp.St.epi)).map (Option.map TSt.d) ≠ some none
  simp [Epi.next, hs, hlen]

/-- **The states whose `hnext` is proved**: the prologue's request-word loads, its exit to the
softmax region, its query loads and its six block-table loads (`PrefixBt.lean`), the softmax
region's 128 bias loads (`PrefixBias.lean`), the epilogue's tile load, every state of the MMA
warp (`WComp.mma_next_follows`), every state of the
loader (`WComp.loader_next_follows`: it follows every loaded word), the
worker's, idle roles' and exit role's states (the worker's broadcast of the warp index by
`worker_shfl_next_ne`: lane 0's operand is the warp index; the dispatch follows every role byte on
every warp, `WComp.ldRole_next_follows`) but the dispatch of a worker whose inherited Tensor
Memory base word has no room for the 512 columns (`WComp.baseOk`), the common
start's states (its broadcast by `dstart_shfl_next_ne`), the prologue's `bar18` with a good base
word (`ProA.wGood`), every epilogue
state (its broadcast follows every received word, `Raw.laneOk`), the prologue's states but its
loads (its broadcasts follow every word) (`ProA.mayLeave`), and every softmax region state
(`DComp.smMayLeave` lists only the bias loads, which are discharged separately; its broadcast
follows every received word, `Raw.laneOk`, the wait for its S load every S word, and the
shuffle of the row maximum every received word)
(`*_next_follows`). -/
def Discharged : TSt → Prop
  | .d (.pro d) => d.site = .ldCu0 ∨ d.site = .ldCu1 ∨ d.site = .ldSk ∨
      (d.site = .bar18 ∧ ProA.wGood d.dt = true) ∨
      (∃ k < 64, d.site = ProA.ldqSite k) ∨ (∃ k < 6, d.site = ProA.lbSite k) ∨
      ProA.mayLeave d.site = false
  | .d (.sm d) => (∃ j, d.site = .pre j) ∨ (∃ j, d.site = .nxt j) ∨
      DComp.smMayLeave d.site = false
  | .d (.epi _) => True
  | .w (.mma _ _) => True
  | .w (.loader _ _) => True
  | .w (.worker w) => (w.site = .bar0 ∨ w.site = .ld0 ∨ w.site = .bar1 ∨ w.site = .loop ∨
      w.site = .bar2 ∨ w.site = .bad0 ∨ w.site = .bad1) ∨ w.site = .shfl ∨
      (w.site = .ldRole ∧ WComp.baseOk w.P)
  | .w (.idle _) => True
  | .w (.exit _) => True
  | .d (.dstart d) => (d.site ≠ .shfl ∧ d.site ≠ .toProA) ∨ d.site = .shfl

/-- A worker state whose composed successor is not `some none` is not one of the thread. -/
theorem w_follows {g : Nat} {s : WComp.WSt} {e : Event} (h : WComp.next L g s e ≠ some none) :
    (threadCode L g Q).next (.w s) e ≠ some none := by
  rw [next_w]
  intro h'
  apply h
  revert h'
  cases WComp.next L g s e with
  | none => simp
  | some o => cases o <;> simp

/-- **`hnext` at the `Discharged` states.** -/
theorem discharged_next_ne (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k : Nat} {s : TSt} {e : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (hσ : St Q L X g k = some (some s))
    (hpo : ∀ j < k, Good Q L mem0 X (g, j)) (hL : LaunchRead Q mem0 X (g, k))
    (hd : Discharged s) : (threadCode L g Q).next s e ≠ some none := by
  have he' : X.get (g, k) = some e := he
  cases s with
  | w s =>
    cases s with
    | mma d P =>
      rw [next_w]
      have h := WComp.mma_next_follows (L := L) (g := g) (e := e) (d := d) P
      intro h'
      apply h
      revert h'
      cases WComp.next L g (.mma d P) e with
      | none => simp
      | some o => cases o <;> simp
    | loader d P =>
      rw [next_w]
      have h := WComp.loader_next_follows (L := L) (g := g) (e := e) (d := d) P
      intro h'
      apply h
      revert h'
      cases WComp.next L g (.loader d P) e with
      | none => simp
      | some o => cases o <;> simp
    | worker w =>
      rcases hd with hd | hd | ⟨hd, hb⟩
      · exact w_follows (WComp.worker_next_follows hd)
      · obtain ⟨site, P⟩ := w
        simp only at hd
        subst hd
        exact worker_shfl_next_ne hX hS hT hpre hg he hσ
      · obtain ⟨site, P⟩ := w
        simp only at hd hb
        subst hd
        exact w_follows (WComp.ldRole_next_follows hb)
    | idle d => exact w_follows (WComp.idle_next_follows d)
    | exit x => exact w_follows (WComp.exit_next_follows x)
  | d s =>
    cases s with
    | dstart d =>
      rcases hd with hd | hd
      swap
      · exact dstart_shfl_next_ne hpre hX hS hT hg he hσ hd
      rw [next_d]
      have h := DComp.dstart_next_follows (L := L) (g := g) (Q := Q) (e := e) hd.1 hd.2
      intro h'
      apply h
      revert h'
      cases DComp.next L g Q (.dstart d) e with
      | none => simp
      | some o => cases o <;> simp
    | sm d =>
      rcases hd with h | h | h
      · exact sm_bias_next_ne hpre hX hS hT hg he' hσ (Or.inl h) hL
      · exact sm_bias_next_ne hpre hX hS hT hg he' hσ (Or.inr h) hL
      · rw [next_d]
        have h' := DComp.sm_next_follows (L := L) (g := g) (Q := Q) (e := e) h
        intro h''
        apply h'
        revert h''
        cases DComp.next L g Q (.sm d) e with
        | none => simp
        | some o => cases o <;> simp
    | epi d =>
      by_cases hl : d.site = .ld
      · exact epi_ld_next_ne hpre hX hS hT hg he' hσ hl
      · rw [next_d]
        have h := DComp.epi_next_follows (L := L) (g := g) (Q := Q) (e := e) hl
        intro h'
        apply h
        revert h'
        cases DComp.next L g Q (.epi d) e with
        | none => simp
        | some o => cases o <;> simp
    | pro d =>
      rcases hd with h | h | h | ⟨h, hw⟩ | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | h
      · exact pro_words_next_ne hpre hX hS hT hg he' hσ hpo hL (Or.inl h) (by simp [h])
      · exact pro_words_next_ne hpre hX hS hT hg he' hσ hpo hL (Or.inr (Or.inl h)) (by simp [h])
      · exact pro_words_next_ne hpre hX hS hT hg he' hσ hpo hL (Or.inr (Or.inr (Or.inl h)))
          (by simp [h])
      · exact pro_words_next_ne hpre hX hS hT hg he' hσ hpo hL (Or.inr (Or.inr (Or.inr h)))
          (fun _ => hw)
      · obtain ⟨site, dt⟩ := d
        simp only at h
        subst h
        exact pro_ldq_next_ne hpre hX hS hT hj hg he' hσ hpo hL
      · obtain ⟨site, dt⟩ := d
        simp only at h
        subst h
        exact pro_lb_next_ne hpre hX hS hT hj hg he' hσ hpo hL
      · rw [next_d]
        have h' := DComp.pro_next_follows (L := L) (g := g) (Q := Q) (e := e) h
        intro h''
        apply h'
        revert h''
        cases DComp.next L g Q (.pro d) e with
        | none => simp
        | some o => cases o <;> simp

/-- **`Premises` from the tracking of the machines**: a machine that follows every thread does not
leave its run at any event of a followed state, and no template is undefined behaviour. -/
theorem premises_of_tracked (ht : Frame.Tracked (code L Q) X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hL : LdRng Q L X)
    (hW : RoleWarps Q L X) : Premises Q L X where
  worker := by
    refine ⟨fun {g k s e} hg he hσ hn => ?_⟩
    have h1 := ht g (k + 1) hg
    rw [Frame.stateAt_succ he, hσ] at h1
    simp only [Option.bind_some] at h1
    apply h1
    show (WComp.next L g s e).map (Option.map TSt.w) = some none
    rw [hn]
    rfl
  default := by
    refine ⟨fun {g k s e} hg he hσ hn => ?_⟩
    have h1 := ht g (k + 1) hg
    rw [Frame.stateAt_succ he, hσ] at h1
    simp only [Option.bind_some] at h1
    apply h1
    show (DComp.next L g Q s e).map (Option.map TSt.d) = some none
    rw [hn]
    rfl
  tmplOk := hT
  ldRng := hL
  roleWarp := hW

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
