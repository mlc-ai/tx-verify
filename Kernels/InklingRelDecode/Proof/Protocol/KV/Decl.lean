-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Handoff
public import Lemmas.Protocol.SingleTmaRing.Hyp

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow

/-- Distinct missing preload issues receive distinct out-of-trace positions. -/
noncomputable def position (X : Execution) (g : Nat) (f : Event → Bool) (n : Nat) :=
  if n < (X.tr g).countP f then nthEv X f g n else (X.tr g).length + n

theorem position_at {X g k f e} (he : Execution.get X (g,k) = some e) (hf : f e = true) :
    position X g f (((X.tr g).take k).countP f) = k := by
  have hn := nthEv_eq he hf
  have hl := (List.getElem?_eq_some_iff.mp he).1
  have hc := (nthEv_lt_iff (X := X) (p := f) (g := g)).mp (hn ▸ hl)
  simpa [position,hc] using hn

theorem position_injective (X : Execution) (g : Nat) (f : Event → Bool) :
    Function.Injective (position X g f) := by
  intro i j hij
  by_cases hi : i < (X.tr g).countP f <;> by_cases hj : j < (X.tr g).countP f
  all_goals simp only [position,hi,hj,↓reduceIte] at hij
  · obtain ⟨_,_,_,ci⟩ := nthEv_spec (X := X) hi
    obtain ⟨_,_,_,cj⟩ := nthEv_spec (X := X) hj
    rw [← ci,← cj,hij]
  · have := nthEv_lt_iff.mpr hi
    omega
  · have := nthEv_lt_iff.mpr hj
    omega
  · omega

noncomputable def preCopy (L : Launch) (X : Execution) (c : Nat) (s : Fin 3) (i : Fin 8) : EvId :=
  let g := leader L X c (i.val / 4)
  (g,position X g (issuesTo (Ring.ready.obj L c s)) (i.val % 4))

noncomputable def decl (Q : Params) (L : Launch) (X : Execution) (c : Nat) : SingleTmaRing.Decl :=
  { depth := 3, full := Ring.ready.obj L c, empty := Ring.empty.obj L c
    ap := c*L.block + 192, cp := leader L X c 6, cm := leader L X c 7
    n := 8, bytes := 8192, δ := preload Q L c
    pArr := fun s => (c*L.block,position X (c*L.block) (arrivesOn (Ring.ready.obj L c s)) 0)
    pCp := preCopy L X c }

theorem leader_warp {Q L m X c w} (hp : Pre Q L m) (hc : c < L.grid) (hw : w < 8) :
    let g := leader L X c w
    g < L.threads ∧ g / L.block = c ∧ g % L.block / 32 = w := by
  unfold leader
  split
  · rename_i h
    obtain ⟨hg,hh,hr,_⟩ := h.choose_spec
    exact ⟨hg,hh,hr⟩
  · simp only [Launch.threads,hp.block]
    omega

theorem precopy_inj {Q L m X c} (hp : Pre Q L m) (hc : c < L.grid) (s : Fin 3) :
    Function.Injective (preCopy L X c s) := by
  intro i j h
  have ⟨hg,hk⟩ := Prod.mk.inj h
  obtain ⟨_,_,hwi⟩ := leader_warp (X := X) hp hc (by omega : i.val/4 < 8)
  obtain ⟨_,_,hwj⟩ := leader_warp (X := X) hp hc (by omega : j.val/4 < 8)
  rw [hg,hwj] at hwi
  rw [hg] at hk
  have hmod := position_injective _ _ _ hk
  apply Fin.ext
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
