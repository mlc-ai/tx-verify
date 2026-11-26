-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.RowMaxPeer
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.PExchange
public import Lemmas.Tcgen05.TcFence
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Pex
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar1
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.SyncId
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Ord

@[expose] public section

/-! # The partner's peer store of a block

A lane `g` of warpgroup 0 that read the peer word `k0` of block `r` (after `r + 1` events of its
pair barrier `10 + warp % 2`) has its partner `tid ^^^ 64` (`w0Partner`) at the pair barrier's event
after `r` of its own (`barId_arrive`), at pc 475; the events before it are the stores
`pst 7 .. pst 0` of the code's chain (`w0_prev_bar1`, `w0_prev_pst`), so the partner's store
`pst k0` of block `r` exists (`peer_store`), and it is the only one with `r` pair-barrier events
before it (`w0_next_pst`: the barrier at pc 475 follows). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  {h : Nat} (hwh : warp L h < 4) (id : Nat)
include hp hX hFw hwh

/-- The stores `pst k` and the pair barrier's neighbours are no barrier events of any id but the
barrier at pc 475. -/
private theorem pst_notBar {j : Nat} {f : Event} (hf : X.get (h, j) = some f) {k : Nat}
    (hk : k < 8) (hpc : f.pc = 403 + 10 * k) : Execution.isBarId id f = false := by
  by_contra hc
  have hb : Execution.isBar f = true := by
    obtain ⟨pc, kd⟩ := f
    cases kd <;> simp_all [Execution.isBarId, Execution.isBar]
  have hat : MbarRow.Wg0At L h f.pc := ⟨hwh, by omega, by omega⟩
  rcases barRow_wg0 hp hX hFw (Frame.lt_of_get hX hf) hf hat hb with ⟨hm, -⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
  · simp only [BarRow.wg0NineSites, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · omega
  · omega

omit hp hX hFw hwh in
private theorem count_succ {j : Nat} {f : Event} (hf : X.get (h, j) = some f)
    (hn : Execution.isBarId id f = false) :
    ((X.tr h).take (j + 1)).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id) := by
  have hsp : (X.tr h).take (j + 1) = (X.tr h).take j ++ [f] := by
    have hf' : (X.tr h)[j]? = some f := hf
    rw [List.take_add_one, hf']; rfl
  rw [hsp, List.countP_append]
  simp [hn]

end

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  {h N : Nat} (hwh : warp L h < 4) (hv : W0Valid P.scale ((X.tr h).take N)) (id : Nat)
include hp hX hFw hwh hv

/-- **Back from the pair barrier's event**: the `d + 1` events before the event at pc 475 at
index `i` are the stores `pst 7 .. pst (7 - d)`, none a barrier event. -/
private theorem pst_back {i r : Nat} {e : Event} (he : X.get (h, i) = some e)
    (hu : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 475) (hN : i ≤ N)
    (hc : ((X.tr h).take i).countP (Execution.isBarId id) = r) :
    ∀ d ≤ 7, ∃ j f, j + d + 1 = i ∧ X.get (h, j) = some f ∧ f.pc = 473 - 10 * d ∧
      ((X.tr h).take j).countP (Execution.isBarId id) = r := by
  have hnf : ∀ {j : Nat} {f : Event}, X.get (h, j) = some f → (∀ u, f.kind ≠ .ub u) →
      103 ≤ f.pc → f.pc < 1842 → ∃ j', j = j' + 1 := fun {j f} hf hu' h1 h2 => by
    cases j with
    | zero => exact (Wg0.w0_not_first hp hX hFw hf hu' ⟨h1, h2⟩).elim
    | succ j' => exact ⟨j', rfl⟩
  have hal := noUbBefore_of_get hX he
  intro d
  induction d with
  | zero =>
    intro _
    obtain ⟨j, rfl⟩ := hnf he hu (by omega) (by omega)
    obtain ⟨f, hf, hfpc⟩ := Wg0.w0_prev_bar1 hp hX hFw hwh he hu hpc
      (Wg0.W0Valid.take_le hv (by omega))
    refine ⟨j, f, rfl, hf, hfpc, ?_⟩
    rw [← count_succ id hf (pst_notBar hp hX hFw hwh id hf (k := 7) (by omega) (by omega))]
    exact hc
  | succ d ih =>
    intro hd
    obtain ⟨j, f, hji, hf, hfpc, hcj⟩ := ih (by omega)
    have huf := hal.ne (by omega) hf
    obtain ⟨j', rfl⟩ := hnf hf huf (by omega) (by omega)
    obtain ⟨f', hf', hf'pc⟩ := Wg0.w0_prev_pst hp hX hFw hwh (k := 6 - d) (by omega) hf huf
      (by omega) (Wg0.W0Valid.take_le hv (by omega))
    refine ⟨j', f', by omega, hf', by omega, ?_⟩
    rw [← count_succ id hf' (pst_notBar hp hX hFw hwh id hf' (k := 6 - d) (by omega) hf'pc)]
    exact hcj

/-- **Forward from a store**: from the store `pst k0` at index `a` with `r` barrier events before it
and a later event `b` at the same pc, the barrier at pc 475 lies between them, so `b` has
more than `r` barrier events before it. -/
private theorem pst_forward {a b r k0 : Nat} {f g' : Event} (hk0 : k0 < 8)
    (hf : X.get (h, a) = some f) (hfpc : f.pc = 403 + 10 * k0)
    (hca : ((X.tr h).take a).countP (Execution.isBarId id) = r) (hab : a < b)
    (hN : b ≤ N)
    (hg : X.get (h, b) = some g') (hgu : ∀ u, g'.kind ≠ .ub u) (hgpc : g'.pc = 403 + 10 * k0)
    (hbar : ∀ {j : Nat} {e : Event}, X.get (h, j) = some e → (∀ u, e.kind ≠ .ub u) →
      e.pc = 475 → Execution.isBarId id e = true) :
    r + 1 ≤ ((X.tr h).take b).countP (Execution.isBarId id) := by
  have key : ∀ t ≤ 8 - k0, a + t < b ∧ ∃ e, X.get (h, a + t) = some e ∧
      e.pc = (if t = 8 - k0 then 475 else 403 + 10 * (k0 + t)) ∧
      ((X.tr h).take (a + t)).countP (Execution.isBarId id) = r := by
    intro t
    induction t with
    | zero => intro _; exact ⟨by omega, f, hf, by simp [hfpc]; omega, hca⟩
    | succ t ih =>
      intro ht
      obtain ⟨hlt, e, he, hepc, hce⟩ := ih (by omega)
      have hlen : b < (X.tr h).length := (List.getElem?_eq_some_iff.mp hg).1
      have hl2 : a + t + 1 < (X.tr h).length := by omega
      obtain ⟨e', he'⟩ : ∃ e', X.get (h, a + t + 1) = some e' :=
        ⟨_, List.getElem?_eq_getElem hl2⟩
      have hue' : ∀ u, e'.kind ≠ .ub u := by
        by_cases hbb : a + t + 1 = b
        · rw [hbb, hg] at he'
          cases he'
          exact hgu
        · exact noUb_kind_of_lt hX he' (k := b) (by omega) hlen
      have hnext := Wg0.w0_next_pst hp hX hFw hwh (k := k0 + t) (by omega) he
        (by rw [hepc]; simp only [show t ≠ 8 - k0 by omega, ↓reduceIte]) he' hue'
        (Wg0.W0Valid.take_le hv (by omega))
      have hne : e'.pc ≠ 403 + 10 * k0 := by
        rw [hnext]; split_ifs <;> omega
      have hbne : a + t + 1 ≠ b := fun hb => by
        rw [hb] at he'
        rw [hg] at he'
        cases he'
        exact hne hgpc
      refine ⟨by omega, e', he', ?_, ?_⟩
      · rw [hnext]
        by_cases h1 : t + 1 = 8 - k0
        · simp [h1, show k0 + t = 7 by omega]
        · simp [h1, show k0 + t < 7 by omega]; omega
      · have hs := count_succ id he (pst_notBar hp hX hFw hwh id he (k := k0 + t) (by omega)
          (by rw [hepc]; simp only [show t ≠ 8 - k0 by omega, ↓reduceIte]))
        rw [← hce]
        exact hs
  obtain ⟨hlt, e, he, hepc, hce⟩ := key (8 - k0) le_rfl
  have h475 : e.pc = 475 := by simpa using hepc
  have hs := count_succ id he
  have hbe := hbar he
    (noUb_kind_of_lt hX he (k := b) (by omega) (List.getElem?_eq_some_iff.mp hg).1) h475
  have hsp : (X.tr h).take (a + (8 - k0) + 1) = (X.tr h).take (a + (8 - k0)) ++ [e] := by
    have hf' : (X.tr h)[a + (8 - k0)]? = some e := he
    rw [List.take_add_one, hf']; rfl
  have h1 : ((X.tr h).take (a + (8 - k0) + 1)).countP (Execution.isBarId id) = r + 1 := by
    rw [hsp, List.countP_append, hce]
    simp [hbe]
  have h2 : (X.tr h).take (a + (8 - k0) + 1) = ((X.tr h).take b).take (a + (8 - k0) + 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [← h1, h2]
  exact (List.take_sublist _ _).countP_le

end

/-- An event with `r` barrier events before it, after a barrier event with `r` before it, is no
event of that count. -/
private theorem lt_of_count {h i' j' r id : Nat} {X : Execution} {f : Event}
    (hf : X.get (h, i') = some f) (hb : Execution.isBarId id f = true)
    (hc : ((X.tr h).take i').countP (Execution.isBarId id) = r)
    (hc' : ((X.tr h).take j').countP (Execution.isBarId id) = r)
    (hne : i' ≠ j') : j' < i' := by
  by_contra hge
  have hlt : i' < j' := by omega
  have hsp : (X.tr h).take (i' + 1) = (X.tr h).take i' ++ [f] := by
    have hf'' : (X.tr h)[i']? = some f := hf
    rw [List.take_add_one, hf'']; rfl
  have h1 : ((X.tr h).take (i' + 1)).countP (Execution.isBarId id) = r + 1 := by
    rw [hsp, List.countP_append, hc]
    simp [hb]
  have h2 : (X.tr h).take (i' + 1) = ((X.tr h).take j').take (i' + 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have := (List.take_sublist (i' + 1) ((X.tr h).take j')).countP_le
    (p := Execution.isBarId id)
  rw [← h2, h1, hc'] at this
  omega

/-- **The partner's peer store `k0` of block `r` exists and is unique** (valid rows): after `r + 1`
pair-barrier events of lane `g`, the partner lane has the store at pc `403 + 10 k0` after `r`
pair-barrier events of its own, and every such store has the same index. -/
theorem peer_store (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : BarRows P L X) {g k r k0 : Nat}
    (hw : warp L g < 4) (hk : k < (X.tr g).length) (hk0 : k0 < 8)
    (hnp : ((X.tr g).take k).countP (Execution.isBarId (10 + warp L g % 2)) = r + 1)
    (hrR : r < blocksOf P L (g / L.block)) (hv : W0Below P L X (w0Partner L g) g k) :
    ∃ j f, X.get (w0Partner L g, j) = some f ∧ f.pc = 403 + 10 * k0 ∧
      ((X.tr (w0Partner L g)).take j).countP (Execution.isBarId (10 + warp L g % 2)) = r ∧
      Relation.TransGen (TcMma.TcStep L X) (w0Partner L g, j) (g, k) ∧
      ∀ j' f', X.get (w0Partner L g, j') = some f' → (∀ u, f'.kind ≠ .ub u) →
        f'.pc = 403 + 10 * k0 →
        ((X.tr (w0Partner L g)).take j').countP (Execution.isBarId (10 + warp L g % 2)) = r →
        j' = j := by
  have hg : g < L.threads := by
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    exact Frame.lt_of_get hX he
  obtain ⟨hs, hwh, hdiv, hmod⟩ := w0Partner_facts hp hw hg
  set h := w0Partner L g with hh
  have hwg := warp_tid hp g
  have hwhh := warp_tid hp h
  have hb := hp.block
  have hpar : warp L h % 2 = warp L g % 2 := by
    have key : ∀ x < 128, (x ^^^ 64) / 32 = x / 32 ^^^ 2 := by decide
    have e1 : h % L.block / 32 = g % L.block / 32 ^^^ 2 := by
      rw [hmod]
      exact key _ (by omega)
    rw [hwhh, hwg, e1, xor2_mod _ (by omega)]
  have hmem : barIn (10 + warp L g % 2) ((h % L.block) / 32) = true := by
    have hp2 : warp L g % 2 < 2 := Nat.mod_lt _ (by omega)
    have h4 : h % L.block / 32 < 4 := by rw [← hwhh]; exact hwh
    have h5 : (h % L.block / 32) % 2 = warp L g % 2 := by rw [← hwhh, hpar]
    simp only [barIn]
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  obtain ⟨i', pc', hget, hci, hbc⟩ := barId_arrive hp hX hR hs hmem hk (n := r) (by omega)
    (fun ⟨j, pcx, hx⟩ => by
      have := wg0_pairExit hp hX hFw hwh hx
      rw [hdiv, hpar] at this
      omega)
  have h475 : pc' = 475 := by
    rcases bar_cls (bar_use hR hs.1 hget rfl) with ⟨-, hc⟩ | ⟨-, hu⟩ | ⟨hw4, -⟩
    · simp [BarRow.Cta] at hc
    · rcases hu with ⟨-, h9⟩ | ⟨h5, -⟩ | ⟨-, h12⟩
      · simp [BarRow.Sync] at h9
        omega
      · exact h5
      · simp at h12
        omega
    · omega
  obtain ⟨i1, rfl⟩ : ∃ i1, i' = i1 + 1 := by
    cases i' with
    | zero => exact (Wg0.w0_not_first hp hX hFw hget (fun _ h => by cases h)
        ⟨by simp only [h475]; omega, by simp only [h475]; omega⟩).elim
    | succ i1 => exact ⟨i1, rfl⟩
  have hvi : W0Valid P.scale ((X.tr h).take (i1 + 1)) := by
    have hl : i1 + 1 < (X.tr h).length := (List.getElem?_eq_some_iff.mp hget).1
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (h, i1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem (by omega : i1 < (X.tr h).length)⟩
    exact (hv i1 e1 he1 (.single (.inl (hbc i1 (by omega))))).1
  have hal0 := noUbBefore_of_get hX hget
  obtain ⟨j, f, hji, hf, hfpc, hcj⟩ := pst_back hp hX hFw hwh hvi (10 + warp L g % 2) hget
    (fun _ h => by cases h) h475 le_rfl hci (7 - k0) (by omega)
  have hf403 : f.pc = 403 + 10 * k0 := by omega
  have hbar : ∀ {j : Nat} {e : Event}, X.get (h, j) = some e → (∀ u, e.kind ≠ .ub u) →
      e.pc = 475 → Execution.isBarId (10 + warp L g % 2) e = true := fun {j e} he hu hpc => by
    rw [← hpar]
    exact wg0_bar1_of_pc hp hX hFw hwh he hu hpc
  have huf := hal0.ne (by omega) hf
  refine ⟨j, f, hf, hf403, hcj, .single (.inl (hbc j (by omega))),
    fun j' f' hf' hu' hpc' hc' => ?_⟩
  rcases Nat.lt_trichotomy j' j with hlt | heq | hgt
  · have := pst_forward hp hX hFw hwh hvi (10 + warp L g % 2) hk0 hf' hpc' hc' hlt
      (by omega) hf huf hf403 hbar
    omega
  · exact heq
  · have hne : i1 + 1 ≠ j' := fun hq => by
      rw [hq] at hget
      rw [hget] at hf'
      cases hf'
      simp only at hpc'
      omega
    have hlt' := lt_of_count hget (hbar hget (fun _ h => by cases h) h475) hci hc' hne
    have := pst_forward hp hX hFw hwh hvi (10 + warp L g % 2) hk0 hf hf403 hcj hgt
      (by omega) hf' hu' hpc' hbar
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
