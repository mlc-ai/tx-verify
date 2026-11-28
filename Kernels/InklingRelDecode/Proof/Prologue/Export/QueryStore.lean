-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.QTile
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.ReadFacts
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Common.Where
import Kernels.InklingRelDecode.Proof.Prologue.QueryAddress
import Kernels.InklingRelDecode.Proof.Prologue.QueryStoreAt
import Kernels.InklingRelDecode.Proof.Prologue.Export.QueryLane
import Kernels.InklingRelDecode.Proof.Common.RankOrder
import Lemmas.Flow.Store

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Proof Control

private theorem store_site (s : Site) (i : Fin 8) : s.pc=526+6*i.val → ∃ j, s=.stq i j := by
  revert i
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- The state of a query store: its site is the store of its sub-word, at its lane's word. -/
private theorem store_state {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (i : Fin 8)
    (he : X.get (g,k) = some ⟨526+6*i.val,.wr a bs⟩) :
    ∃ w d n, ∃ j : Fin 4, Frame.stateAt (thread Q L) X g k = some (some (proState w d n)) ∧
      d.site = .stq i j ∧ a.loc = ⟨.shared, g/L.block, queryAddress L g i + 4*j.val⟩ ∧
      a.size = 4 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
  change 526+6*i.val = _ at pc
  obtain ⟨w,d,n,rfl⟩ := (pc ▸ state_role s).prologue (by omega) (by omega)
  change _ = d.site.pc at pc
  obtain ⟨j,site⟩ := store_site d.site i pc.symm
  obtain ⟨t,ins,o,ht,_,hc,fire⟩ := Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hs
    (by simp)
  obtain ⟨addr,size⟩ := (query_store_at hp i j site ht hc fire).2 _ _ rfl
  exact ⟨w,d,n,j,hs,site,addr,size⟩

/-- Each element of a vector store stays in the query tile. The two bounds
exclude any overlap with the count pair, even at the last byte of the tile. -/
public theorem query_store {Q L m X g k a bs} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (i : Fin 8)
    (he : X.get (g,k) = some ⟨526+6*i.val,.wr a bs⟩) :
    (∃ j : Fin 4, a.loc = ⟨.shared,g/L.block,
      L.sharedBase + Lib.qSwz (g%L.block) + (196608+2048*Lib.qGroup i) + 4*j.val⟩) ∧
    a.size=4 ∧ L.sharedBase+196608 ≤ a.loc.addr ∧ a.loc.addr+a.size ≤ L.sharedBase+212992 := by
  obtain ⟨-,-,-,j,-,-,addr,size⟩ := store_state hp hX i he
  have range := queryAddress_range hp g i
  exact ⟨⟨j,addr⟩,size,by rw [addr]; dsimp only; omega,by rw [addr,size]; dsimp only; omega⟩

/-- **A query word is stored once**: two query stores of one location are one event. -/
public theorem query_once {Q L m X g k g' k' a a' bs bs'} {i i' : Fin 8} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (he : X.get (g,k) = some ⟨526+6*i.val,.wr a bs⟩)
    (he' : X.get (g',k') = some ⟨526+6*i'.val,.wr a' bs'⟩) (loc : a.loc = a'.loc) :
    g = g' ∧ k = k' := by
  obtain ⟨w,d,n,j,hs,site,addr,-⟩ := store_state hp hX i he
  obtain ⟨w',d',n',j',hs',site',addr',-⟩ := store_state hp hX i' he'
  have lane := query_lane hp hX hf he
  have lane' := query_lane hp hX hf he'
  rw [addr, addr'] at loc
  obtain ⟨-, cta, off⟩ := Loc.mk.inj loc
  have hm : g % L.block = g' % L.block ∧ i = i' ∧ j = j' := by
    have := Lib.qOff_inj (m := i.val) (m' := i'.val) (t := g % L.block) (t' := g' % L.block)
      (w := j.val) (w' := j'.val) (b := 0) (b' := 0) i.isLt i'.isLt (by omega) (by omega)
      j.isLt j'.isLt (by omega) (by omega) (by unfold queryAddress at off; omega)
    omega
  have gs : g = g' := by
    have := Nat.div_add_mod g L.block
    have := Nat.div_add_mod g' L.block
    rw [cta, hm.1] at *
    omega
  subst gs
  obtain ⟨-, rfl, rfl⟩ := hm
  have same : Prologue.measure d' = Prologue.measure d := by
    unfold Prologue.measure
    rw [site, site']
  have wr : (⟨526+6*i.val,.wr a bs⟩ : Event).counts = true := rfl
  have wr' : (⟨526+6*i.val,.wr a' bs'⟩ : Event).counts = true := rfl
  have len := (List.getElem?_eq_some_iff.mp he).1
  have len' := (List.getElem?_eq_some_iff.mp he').1
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy k k' with h | h | h
  · have := later_rank hp hX hf words he wr hs h len'.le hs'
    change 75 + softMaxRank + Prologue.measure d' < 75 + softMaxRank + Prologue.measure d at this
    omega
  · exact h
  · have := later_rank hp hX hf words he' wr' hs' h len.le hs
    change 75 + softMaxRank + Prologue.measure d < 75 + softMaxRank + Prologue.measure d' at this
    omega

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
