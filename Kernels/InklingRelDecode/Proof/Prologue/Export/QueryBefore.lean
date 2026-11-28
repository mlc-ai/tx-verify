-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.FollowSub
import Kernels.InklingRelDecode.Proof.Prologue.QueryChain
import Kernels.InklingRelDecode.Proof.Prologue.QueryStoreAt
public import Kernels.InklingRelDecode.Proof.Lib.QTile

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g u : Nat}

private theorem only_bar18 (s : Site) : 573 = s.pc → s = .bar18 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- Every state back along the chain from the releasing barrier has an earlier state. -/
private theorem chain_back (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (sync : X.get (g,u) = some ⟨573,.bar 1 none .sync⟩) :
    ∀ n ≤ 36, ∃ v, (n = 0 ∨ v < u) ∧ v ≤ u ∧ ∃ w d c,
      Frame.stateAt (thread Q L) X g v = some (some (proState w d c)) ∧
        d.site = chainSite (36 - n) := by
  have len : u < (X.tr g).length := (List.getElem?_eq_some_iff.mp sync).1
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
      hX sync (by simp) ⟨control_tracked hp hX g u (Frame.lt_of_get hX sync),fun _ _ => trivial⟩
    have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX sync hs (by simp)
    obtain ⟨w,d,c,rfl⟩ :=
      (pc ▸ state_role s).prologue (by decide : 27 < 573) (by decide : 573 < 574)
    refine ⟨u, .inl rfl, le_rfl, w, d, c, hs, ?_⟩
    rw [only_bar18 _ pc]
    rfl
  | succ n ih =>
    intro hn
    obtain ⟨v, -, vu, w, d, c, hs, site⟩ := ih (by omega)
    have later : d ≠ {} := by
      rintro rfl
      have : ∀ n ≤ 35, chainSite (36 - n) ≠ .sMax := by decide +kernel
      exact this n (by omega) site.symm
    obtain ⟨v', old, cnt, ev, eq, prev, -, step⟩ := pro_prev (by omega) later hs
    refine ⟨v', .inr (by omega), by omega, w, old, cnt, prev, ?_⟩
    have tail := storeTail_next step
    have hd : storeTail d.site = 37 - n := by
      rw [site, storeTail_chain _ (by omega)]
      omega
    rcases tail with h | h
    · omega
    · have := chainSite_tail old.site (by omega)
      rw [this]
      congr 1
      omega

/-- The store of a state on the way to the releasing barrier has fired, at its lane's word. -/
private theorem store_event (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (sync : X.get (g,u) = some ⟨573,.bar 1 none .sync⟩) {v w d c} (before : v < u)
    (hs : Frame.stateAt (thread Q L) X g v = some (some (proState w d c))) (i : Fin 8)
    (j : Fin 4) (site : d.site = .stq i j) :
    ∃ a bs, X.get (g,v) = some ⟨526+6*i.val,.wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, queryAddress L g i + 4 * j.val⟩ ∧ a.size = 4 := by
  have hk : u < (X.tr g).length := (List.getElem?_eq_some_iff.mp sync).1
  have get := List.getElem?_eq_getElem (l := X.tr g) (i := v) (by omega)
  have clean := Frame.noUbBefore_of_get hX sync v before _ get
  obtain ⟨t,ins,o,ht,-,hc,fire⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX get hs clean
  have pc := EventFrame.fires_source_pc fire
  obtain ⟨kind,loc⟩ := query_store_at hp i j site ht hc fire
  rcases kind with ⟨f,bad⟩ | ⟨a,bs,wr⟩
  · exact (clean f bad).elim
  · obtain ⟨loc,size⟩ := loc a bs wr
    refine ⟨a,bs,?_,loc,size⟩
    have ev : (X.tr g)[v] = ⟨526+6*i.val,.wr a bs⟩ := by
      generalize (X.tr g)[v] = e at wr pc
      obtain ⟨epc,ek⟩ := e
      simp only at wr pc
      subst wr
      rw [pc, site]
      rfl
    exact get.trans (congrArg some ev)

/-- **A lane at the releasing barrier has stored every query word**: each store of the chain
fired before the barrier, at its lane's word. -/
public theorem query_before_sync (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (sync : X.get (g,u) = some ⟨573,.bar 1 none .sync⟩) (i : Fin 8) (j : Fin 4) :
    ∃ v < u, ∃ a bs, X.get (g,v) = some ⟨526+6*i.val,.wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block, L.sharedBase + Lib.qSwz (g % L.block) +
        (196608 + 2048 * Lib.qGroup i) + 4 * j.val⟩ ∧ a.size = 4 := by
  obtain ⟨v,lt,-,w,d,c,hs,site⟩ := chain_back hp hX sync (36 - (4 * i.val + j.val)) (by omega)
  have lt : v < u := lt.resolve_left (by have := i.isLt; have := j.isLt; omega)
  have chain : chainSite (36 - (36 - (4 * i.val + j.val))) = .stq i j := by
    have := i.isLt
    have := j.isLt
    rw [show 36 - (36 - (4 * i.val + j.val)) = 4 * i.val + j.val by omega]
    have lt32 : 4 * i.val + j.val < 32 := by omega
    have e1 : (4 * i.val + j.val) / 4 = i.val := by omega
    have e2 : (4 * i.val + j.val) % 4 = j.val := by omega
    simp only [chainSite, lt32, ↓reduceDIte, e1, e2]
  obtain ⟨a,bs,get,loc,size⟩ := store_event hp hX sync lt hs i j (site.trans chain)
  exact ⟨v,lt,a,bs,get,loc,size⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
