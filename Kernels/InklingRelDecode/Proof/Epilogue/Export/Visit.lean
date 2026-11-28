-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Common.Data
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
import Kernels.InklingRelDecode.Proof.Epilogue.AddrValue
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
public import Kernels.InklingRelDecode.Proof.Lib.Rows
import Kernels.InklingRelDecode.Flow.Code.Part041
import Lemmas.Flow.StoreKind
import Lemmas.Flow.StoreGlobal
import Lemmas.Kernel.FrameEnd

@[expose] public section

/-! # A complete epilogue lane visits every store of its row

A complete data lane ends with an exit, whose state is the epilogue's last site; walking the
epilogue machine back from there, a lane whose row loads has fired the store of every word and,
when it is a leading lane, the LSE store.  -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
open PTX PTX.Flow PTX.Frame Epilogue Epilogue.Control

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites an epilogue site continues at. -/
private def outs (v l : Bool) : Site → List Site
  | .wait => [.wait, .shfl, firstStore v l] | .shfl => [.load] | .load => [.waitLd]
  | .waitLd => [firstStore v l] | .lse => [.store 0] | .store j => [storeAt (j.val + 1)]
  | .join => [.setMax] | .setMax => [.roleWord] | .roleWord => [.sync1] | .sync1 => [.sync0]
  | .sync0 => [.dealloc, .exit] | .dealloc => [.exit] | .exit => []

private theorem next_outs {e : Entry} {d old : D} {ev : Event}
    (h : Control.next e L g old ev = some (some d)) :
    d.site ∈ outs e.valid (lead (g % L.block)) old.site := by
  obtain ⟨site, rcv⟩ := old
  cases site <;> simp only [Control.next] at h
  all_goals try (obtain rfl := Option.some.inj (Option.some.inj h); simp [outs, storeAt]; done)
  · split at h
    · split at h
      · obtain rfl := Option.some.inj (Option.some.inj h)
        simp only [outs, List.mem_cons, List.not_mem_nil, or_false]
        split_ifs <;> simp
      · obtain rfl := Option.some.inj (Option.some.inj h)
        simp [outs]
    · cases h
  · split at h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      simp [outs]
    · cases h
  · obtain rfl := Option.some.inj (Option.some.inj h)
    simp only [outs, List.mem_cons, List.not_mem_nil, or_false]
    split_ifs <;> simp
  · cases h

private theorem mem_sites (s : Site) : s ∈ allSites := by
  cases s <;> simp [allSites]

private theorem pred_exit (v l : Bool) : ∀ o ∈ allSites, Site.exit ∈ outs v l o →
    o = .sync0 ∨ o = .dealloc := by cases v <;> cases l <;> decide +kernel

private theorem pred_dealloc (v l : Bool) : ∀ o ∈ allSites, Site.dealloc ∈ outs v l o →
    o = .sync0 := by cases v <;> cases l <;> decide +kernel

private theorem pred_sync0 (v l : Bool) : ∀ o ∈ allSites, Site.sync0 ∈ outs v l o →
    o = .sync1 := by cases v <;> cases l <;> decide +kernel

private theorem pred_sync1 (v l : Bool) : ∀ o ∈ allSites, Site.sync1 ∈ outs v l o →
    o = .roleWord := by cases v <;> cases l <;> decide +kernel

private theorem pred_roleWord (v l : Bool) : ∀ o ∈ allSites, Site.roleWord ∈ outs v l o →
    o = .setMax := by cases v <;> cases l <;> decide +kernel

private theorem pred_setMax (v l : Bool) : ∀ o ∈ allSites, Site.setMax ∈ outs v l o →
    o = .join := by cases v <;> cases l <;> decide +kernel

private theorem pred_join (l : Bool) : ∀ o ∈ allSites, Site.join ∈ outs true l o →
    o = .store 63 := by cases l <;> decide +kernel

private theorem pred_store (v l : Bool) : ∀ j : Fin 64, ∀ i : Fin 64, i.val = j.val + 1 →
    ∀ o ∈ allSites, Site.store i ∈ outs v l o → o = .store j := by
  cases v <;> cases l <;> decide +kernel

private theorem pred_store0 (v : Bool) : ∀ o ∈ allSites, Site.store 0 ∈ outs v true o →
    o = .lse := by cases v <;> decide +kernel

/-- **The state of a data lane at pc 2855 is the epilogue's exit site.** -/
private theorem exit_shape (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (lane : g % L.block < 128) {k : Nat} (hk : k ≤ (X.tr g).length) {s : (thread Q L g).D}
    (hs : stateAt (thread Q L) X g k = some (some s)) (hpc : (thread Q L g).pc s = 2855) :
    ∃ w ent d n, s = epiState w ent d n ∧ d.site = Site.exit := by
  obtain ⟨σ, n⟩ := s
  rcases σ with ⟨st, tm, x, w⟩ | ⟨r, sub⟩
  · exfalso
    change st.pc = 2855 at hpc
    revert hpc
    cases st <;> first | decide | (rename_i r; cases r <;> decide)
  · rcases r with r | r
    · cases r with
      | prologue w =>
        rcases sub with s | ⟨e, s | ⟨⟨⟩, s⟩⟩
        · exfalso
          have range := s.site.pc_range
          change s.site.pc = 2855 at hpc
          omega
        · exfalso
          have range := s.site.pc_range
          change s.site.pc = 2855 at hpc
          rcases range with h | h
          · omega
          · rw [h] at hpc
            exact absurd hpc (by decide)
        · refine ⟨w, e, s, n, rfl, ?_⟩
          obtain ⟨site, v⟩ := s
          change site.pc = 2855 at hpc
          change site = Site.exit
          cases site <;> first | rfl | (exfalso; revert hpc; decide) |
            (simp only [Site.pc, storePc] at hpc; omega)
      | dispatch w x =>
        exfalso
        have := (worker_warp hp hX hk hs).1
        omega
    · exact (no_stub hp hX hk hs).elim

/-- The lane is at the epilogue site `s` before its event `k`, which is at the site's pc. -/
private def At (Q : Params) (L : Launch) (X : Execution) (g : Nat) (w : Value)
    (ent : Softmax.Control.Entry) (k : Nat) (s : Site) : Prop :=
  ∃ d n ev, stateAt (thread Q L) X g k = some (some (epiState w ent d n)) ∧ d.site = s ∧
    X.get (g, k) = some ev ∧ ev.pc = s.pc

/-- **The site before**: an event of a lane past its first site is preceded by an event at a
site it continues from. -/
private theorem back_step (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {w ent k s kx}
    (hnu : NoUbBefore X g kx) (hk : k ≤ kx) (hkx : kx ≤ (X.tr g).length)
    (hAt : At Q L X g w ent k s) (off : s ≠ Site.wait) :
    ∃ u o, u < k ∧ At Q L X g w ent u o ∧
      s ∈ outs (epiEntry ent (g % L.block)).valid (lead (g % L.block)) o := by
  obtain ⟨d, n, ev, hs, hsite, -, -⟩ := hAt
  have later : d ≠ ({} : D) := fun h => off (by rw [← hsite, h])
  obtain ⟨u, old, cnt, ev', hu, hs', get, mv⟩ := epi_prev (by omega) later hs
  have clean : ∀ f, ev'.kind ≠ .ub f := hnu u (by omega) ev' get
  have pc := event_pcU (fun g h => thread_sound hp h) hX get hs' clean
  refine ⟨u, old.site, by omega, ⟨old, cnt, ev', hs', rfl, get, pc⟩, ?_⟩
  rw [← hsite]
  exact next_outs mv



private theorem step_to (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {w ent k s o kx} (hnu : NoUbBefore X g kx) (hk : k ≤ kx) (hkx : kx ≤ (X.tr g).length)
    (hAt : At Q L X g w ent k s) (off : s ≠ Site.wait)
    (h : ∀ o' ∈ allSites, s ∈ outs (epiEntry ent (g % L.block)).valid (lead (g % L.block)) o' →
      o' = o) : ∃ u, u < k ∧ At Q L X g w ent u o := by
  obtain ⟨u, o', hu, hA, hm⟩ := back_step hp hX hnu hk hkx hAt off
  obtain rfl := h o' (mem_sites o') hm
  exact ⟨u, hu, hA⟩

/-- **A complete lane whose row loads fired every store and, leading, the LSE store.** -/
private theorem visit_stores (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {w ent kx}
    (hnu : NoUbBefore X g kx) (hkx : kx ≤ (X.tr g).length)
    (hv : (epiEntry ent (g % L.block)).valid = true) (hAt : At Q L X g w ent kx Site.exit) :
    (∀ j : Fin 64, ∃ u, u < kx ∧ At Q L X g w ent u (Site.store j)) ∧
      (lead (g % L.block) = true → ∃ u, u < kx ∧ At Q L X g w ent u Site.lse) := by
  have e0 : kx ≤ kx := le_rfl
  obtain ⟨u1, o1, hu1, hA1, hm1⟩ := back_step hp hX hnu e0 hkx hAt (by decide)
  obtain ⟨u2, hu2, hA2⟩ : ∃ u, u < kx ∧ At Q L X g w ent u Site.sync0 := by
    rcases pred_exit _ _ o1 (mem_sites o1) hm1 with rfl | rfl
    · exact ⟨u1, hu1, hA1⟩
    · obtain ⟨u, hu, hA⟩ := step_to hp hX hnu (by omega) hkx hA1 (by decide)
        (fun o' h1 h2 => pred_dealloc _ _ o' h1 h2)
      exact ⟨u, by omega, hA⟩
  obtain ⟨u3, hu3, hA3⟩ := step_to hp hX hnu (by omega) hkx hA2 (by decide)
    (fun o' h1 h2 => pred_sync0 _ _ o' h1 h2)
  obtain ⟨u4, hu4, hA4⟩ := step_to hp hX hnu (by omega) hkx hA3 (by decide)
    (fun o' h1 h2 => pred_sync1 _ _ o' h1 h2)
  obtain ⟨u5, hu5, hA5⟩ := step_to hp hX hnu (by omega) hkx hA4 (by decide)
    (fun o' h1 h2 => pred_roleWord _ _ o' h1 h2)
  obtain ⟨u6, hu6, hA6⟩ := step_to hp hX hnu (by omega) hkx hA5 (by decide)
    (fun o' h1 h2 => pred_setMax _ _ o' h1 h2)
  obtain ⟨u7, hu7, hA7⟩ := step_to hp hX hnu (by omega) hkx hA6 (by decide)
    (fun o' h1 h2 => pred_join _ o' h1 (by rw [hv] at h2; exact h2))
  have down : ∀ j : Nat, ∀ hj : j < 64, ∀ u, u ≤ kx → At Q L X g w ent u (Site.store ⟨j, hj⟩) →
      (∀ i : Fin 64, i.val ≤ j → ∃ u', u' ≤ u ∧ At Q L X g w ent u' (Site.store i)) ∧
        (lead (g % L.block) = true → ∃ u', u' ≤ u ∧ At Q L X g w ent u' Site.lse) := by
    intro j
    induction j with
    | zero =>
      intro hj u hu hA
      refine ⟨fun i hi => ⟨u, le_rfl, ?_⟩, fun hl => ?_⟩
      · have : i = ⟨0, hj⟩ := Fin.ext (by show i.val = 0; omega)
        rw [this]; exact hA
      · obtain ⟨u', hu', hA'⟩ := step_to hp hX hnu hu hkx hA (fun h => by cases h)
          (fun o' h1 h2 => pred_store0 _ o' h1 (by rw [hl] at h2; exact h2))
        exact ⟨u', by omega, hA'⟩
    | succ j ih =>
      intro hj u hu hA
      obtain ⟨u', hu', hA'⟩ := step_to hp hX hnu hu hkx hA (fun h => by cases h)
        (fun o' h1 h2 => pred_store _ _ ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl o' h1 h2)
      obtain ⟨c1, c2⟩ := ih (by omega) u' (by omega) hA'
      refine ⟨fun i hi => ?_, fun hl => ?_⟩
      · by_cases hij : i.val = j + 1
        · exact ⟨u, le_rfl, by have : i = ⟨j + 1, hj⟩ := Fin.ext hij; rw [this]; exact hA⟩
        · obtain ⟨u'', h1, h2⟩ := c1 i (by omega)
          exact ⟨u'', by omega, h2⟩
      · obtain ⟨u'', h1, h2⟩ := c2 hl
        exact ⟨u'', by omega, h2⟩
  obtain ⟨c1, c2⟩ := down 63 (by omega) u7 (by omega) hA7
  refine ⟨fun j => ?_, fun hl => ?_⟩
  · obtain ⟨u, h1, h2⟩ := c1 j (by have := j.isLt; omega)
    exact ⟨u, by omega, h2⟩
  · obtain ⟨u, h1, h2⟩ := c2 hl
    exact ⟨u, by omega, h2⟩

private def stChk (j : Nat) : Bool := match kernel.code[storePc j]? with
  | some ⟨_, .mem a⟩ => decide (GlobalStore a (2380 + j) (1832 + j))
  | _ => false

private theorem stChk_all : ∀ j : Fin 64, stChk j.val = true := by decide +kernel

/-- **A store site's event is a write.** -/
private theorem store_kind (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {k w ent d n}
    {ev : Event} (hs : stateAt (thread Q L) X g k = some (some (epiState w ent d n)))
    (get : X.get (g, k) = some ev) (clean : ∀ f, ev.kind ≠ .ub f) (j : Fin 64)
    (site : d.site = Site.store j) : ∃ a bs, ev = ⟨storePc j.val, .wr a bs⟩ := by
  have hpc := event_pcU (fun g h => thread_sound hp h) hX get hs clean
  change ev.pc = d.site.pc at hpc
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_siteU (fun g h => thread_sound hp h) hX get hs
    clean
  change kernel.code[d.site.pc]? = some ins at hc
  change Fires d.site.pc _ _ _ at hf
  rw [site] at hc hf hpc
  have hk := stChk_all j
  unfold stChk at hk
  rw [show Site.pc (Site.store j) = storePc j.val from rfl] at hc hf
  rw [hc] at hk
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [] at hk <;> try contradiction
  obtain ⟨hr, hsp, hb, hkd, hsem, -, -, hsrc⟩ := of_decide_eq_true hk
  obtain ⟨acc, bs, hw⟩ := fires_st_kind hr (sp := .global) (by simpa using hsp) hb hkd hsem hsrc hf
    clean
  obtain ⟨pc, kd⟩ := ev
  change kd = _ at hw
  change pc = _ at hpc
  subst hw hpc
  exact ⟨acc, bs, rfl⟩

/-- **The LSE site's event is a write.** -/
private theorem lse_kind (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) {k w ent d n}
    {ev : Event} (hs : stateAt (thread Q L) X g k = some (some (epiState w ent d n)))
    (get : X.get (g, k) = some ev) (clean : ∀ f, ev.kind ≠ .ub f) (site : d.site = Site.lse) :
    ∃ a bs, ev = ⟨2682, .wr a bs⟩ := by
  have hpc := event_pcU (fun g h => thread_sound hp h) hX get hs clean
  change ev.pc = d.site.pc at hpc
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_siteU (fun g h => thread_sound hp h) hX get hs
    clean
  change kernel.code[d.site.pc]? = some ins at hc
  change Fires d.site.pc _ _ _ at hf
  rw [site] at hc hf hpc
  rw [show Site.pc Site.lse = 2682 from rfl] at hc hf hpc
  obtain ⟨mm, hmm, hgs⟩ : ∃ mm, ins.op = .mem mm ∧ GlobalStore mm 2379 1831 := by
    rw [Flow.code_2682] at hc
    obtain rfl := (Option.some.inj hc).symm
    exact ⟨_, rfl, by decide⟩
  rw [hmm] at hf
  obtain ⟨hr, hsp, hb, hkd, hsem, -, -, hsrc⟩ := hgs
  obtain ⟨acc, bs, hw⟩ := fires_st_kind hr (sp := .global) (by simpa using hsp) hb hkd hsem hsrc hf
    clean
  obtain ⟨pc, kd⟩ := ev
  change kd = _ at hw
  change pc = _ at hpc
  subst hw hpc
  exact ⟨acc, bs, rfl⟩

private theorem lead_iff : ∀ t : Fin 256, lead t.val = true ↔ t.val / 16 % 2 = 0 := by
  decide +kernel

/-- **A complete data lane whose row loads fired the stores of all its words**, and, when it
leads (bit 4 of its index clear), the LSE store. -/
public theorem store_visit (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hc : Complete L X) (hcl : ¬ ClcCanceled L X g) (hg : g < L.threads)
    (lane : g % L.block < 128)
    (valid : Lib.QRowValid Q L (g / L.block) (Lib.rowM (g % L.block))) :
    (∀ j : Fin 64, ∃ k a bs, X.get (g, k) = some ⟨2751 + j.val + j.val / 2, .wr a bs⟩) ∧
      (g % L.block / 16 % 2 = 0 → ∃ k a bs, X.get (g, k) = some ⟨2682, .wr a bs⟩) := by
  obtain ⟨kx, pc, hk, he⟩ := Frame.Complete.exit_last hc hg hcl
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (fun pc' f h => by cases h) ⟨control_tracked hp hX g kx hg, fun _ _ => trivial⟩
  obtain ⟨t, ins, o, -, -, hins, hf⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (fun f => nofun)
  have ret := Lib.ret_pc' hins hf rfl
  have hpc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (fun f => nofun)
  have p2855 : (thread Q L g).pc s = 2855 := by simpa [Lib.retPcs] using ret
  obtain rfl : pc = 2855 := hpc.trans p2855
  have hkx : kx ≤ (X.tr g).length := by omega
  obtain ⟨w, ent, d, n, rfl, hsite⟩ := exit_shape hp hX lane hkx hs p2855
  have hnu : NoUbBefore X g kx := Frame.noUbBefore_of_get hX he
  have nums := reached_numbers hp hX hg hkx hs
  have hv : (epiEntry ent (g % L.block)).valid = true := by
    obtain ⟨-, -, hq⟩ := nums
    have h10 := hp.qLenLe _ (Lib.coordinate_bounds hp hg).2.2
    obtain ⟨h60, htok⟩ := valid
    have e1 : Softmax.Control.row (g % L.block) = Lib.rowM (g % L.block) := Lib.rowM_eq _
    have e2 : Softmax.Control.token (g % L.block) = Lib.tokM (g % L.block) := Lib.tokOf_eq _
    simp only [epiEntry, Softmax.Control.validRow, Softmax.Control.tokenFits, e1, e2, hq,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h60, htok, by omega⟩
  obtain ⟨c1, c2⟩ := visit_stores hp hX hnu hkx hv ⟨d, n, ⟨2855, .exit⟩, hs, hsite, he, rfl⟩
  have clean : ∀ u, u < kx → ∀ ev, X.get (g, u) = some ev → ∀ f, ev.kind ≠ .ub f := hnu
  refine ⟨fun j => ?_, fun hl => ?_⟩
  · obtain ⟨u, hu, d', n', ev, hs', hsite', get, -⟩ := c1 j
    obtain ⟨a, bs, hev⟩ := store_kind hp hX hs' get (clean u hu ev get) j hsite'
    exact ⟨u, a, bs, hev ▸ get⟩
  · have hl' : lead (g % L.block) = true :=
      (lead_iff ⟨g % L.block, by have := hp.block; omega⟩).2 hl
    obtain ⟨u, hu, d', n', ev, hs', hsite', get, -⟩ := c2 hl'
    obtain ⟨a, bs, hev⟩ := lse_kind hp hX hs' get (clean u hu ev get) hsite'
    exact ⟨u, a, bs, hev ▸ get⟩

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Export
