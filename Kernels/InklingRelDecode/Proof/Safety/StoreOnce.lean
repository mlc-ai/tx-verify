-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.AsyncWrites
public import Kernels.InklingRelDecode.Proof.Bound.Epi

@[expose] public section

/-!
# An output element has one store event

Two global stores of an execution whose footprints overlap are stores of one output element
(`Interface.global_writes_same_element`): the epilogue registers of their threads give one split,
token, head and column. Then they are one event:

* **The element determines the thread.** A thread `g` of the default partition is its CTA
  `(split, kv head, request)` and its index `tid < 128`. The token is the request's first token
  plus `tokM tid`, which is below the request's query length for a stored row, so two requests
  have disjoint tokens (`cu_seqlens_q` is monotone); the head is `6 kv + rowM tid % 6`, the row
  `rowM tid = 16 (tid / 32 % 4) + tid % 16`, the column `64 (tid / 16 % 2) + j`. These determine
  `kv`, `rowM tid`, `tid / 16 % 2` and so `tid`.
* **A thread stores each element once.** The epilogue is a straight line of sites whose rank
  falls at every store (`Bound.Epi.rank_step`) and stays in the epilogue, so a site is not
  visited twice.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### One thread, one store per site -/

/-- A step from an epilogue state is an epilogue step. -/
theorem epi_next_of {g k : Nat} {e : Event} {d : Epi.D} {s' : TSt}
    (he : (X.tr g)[k]? = some e) (hσ : St Q L X g k = some (some (.d (.epi d))))
    (hσ' : St Q L X g (k + 1) = some (some s')) :
    ∃ d', Epi.next d e = some (some d') ∧ s' = .d (.epi d') := by
  have h := Frame.stateAt_succ (C := code L Q) (X := X) (g := g) he
  simp only [St] at hσ hσ'
  rw [hσ, hσ'] at h
  simp only [Option.bind_some, Flow.Code.toMachine] at h
  simp only [TSt.next, DComp.next] at h
  cases hn : Epi.next d e with
  | none => simp [hn] at h
  | some o =>
    cases o with
    | none => simp [hn] at h
    | some d' =>
      simp only [hn, Option.map_some, Option.some.injEq] at h
      exact ⟨d', rfl, h⟩

/-- **From an epilogue state the thread stays in the epilogue, and the rank does not rise.** -/
theorem epi_reach (ht : Frame.Tracked (code L Q) X) {g : Nat} (hg : g < L.threads) {k : Nat}
    {d : Epi.D} (hσ : St Q L X g k = some (some (.d (.epi d)))) {m : Nat} (hkm : k ≤ m)
    (hm : m ≤ (X.tr g).length) {s : TSt} (hs : St Q L X g m = some (some s)) :
    ∃ d', s = .d (.epi d') ∧ Bound.Epi.rank d' ≤ Bound.Epi.rank d := by
  induction m, hkm using Nat.le_induction generalizing s with
  | base => rw [hσ] at hs; cases hs; exact ⟨d, rfl, le_refl _⟩
  | succ m hkm ih =>
    obtain ⟨s1, hs1⟩ := Frame.stateAt_live ht hg hs (Nat.le_succ m)
    obtain ⟨d1, rfl, hr⟩ := ih (by omega) hs1
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[m]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨d2, hn, rfl⟩ := epi_next_of he hs1 hs
    have := Bound.Epi.rank_step hn
    exact ⟨d2, rfl, by omega⟩

/-- **A site of the epilogue is not visited twice along a thread**: after a counted event at an
epilogue state, every later epilogue state has a smaller rank. -/
theorem epi_once (ht : Frame.Tracked (code L Q) X) {g : Nat} (hg : g < L.threads) {k k' : Nat}
    {e : Event} (he : (X.tr g)[k]? = some e) (hc : e.counts = true) {d d' : Epi.D}
    (hσ : St Q L X g k = some (some (.d (.epi d)))) (hlt : k < k') (hk' : k' ≤ (X.tr g).length)
    (hσ' : St Q L X g k' = some (some (.d (.epi d')))) :
    Bound.Epi.rank d' < Bound.Epi.rank d := by
  obtain ⟨s1, hs1⟩ := Frame.stateAt_live ht hg hσ' (show k + 1 ≤ k' by omega)
  obtain ⟨d1, rfl, hn, -⟩ : ∃ d1, s1 = .d (.epi d1) ∧ Epi.next d e = some (some d1) ∧ True := by
    obtain ⟨d1, hn, hs⟩ := epi_next_of he hσ hs1
    exact ⟨d1, hs, hn, trivial⟩
  have hstep := Bound.Epi.rank_step hn
  simp only [hc, ite_true] at hstep
  obtain ⟨d2, hd2, hr⟩ := epi_reach ht hg hs1 (show k + 1 ≤ k' by omega) hk' hσ'
  cases hd2
  omega

/-! ### An output element determines its thread -/

theorem cta_inj {b c c' : Nat}
    (hx : c / (kvHeads * b) = c' / (kvHeads * b)) (hy : c / b % kvHeads = c' / b % kvHeads)
    (hz : c % b = c' % b) : c = c' := by
  have h1 : c / b / kvHeads = c' / b / kvHeads := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm b kvHeads]
    exact hx
  have h2 : c / b = c' / b := by
    have a1 := Nat.div_add_mod (c / b) kvHeads
    have a2 := Nat.div_add_mod (c' / b) kvHeads
    rw [h1, hy] at a1
    omega
  have a3 := Nat.div_add_mod c b
  have a4 := Nat.div_add_mod c' b
  rw [h2, hz] at a3
  omega

theorem qStart_mono (hpre : Pre Q L mem0) {r r' : Nat} (h : r ≤ r') (hb : r' ≤ Q.b) :
    Q.qStart r ≤ Q.qStart r' := by
  induction r', h using Nat.le_induction with
  | base => exact le_refl _
  | succ r' h ih =>
    have := ih (by omega)
    have := hpre.cuMono r' (by omega)
    omega

/-- Two valid rows of one token index have one request. -/
theorem request_inj (hpre : Pre Q L mem0) {z z' t t' : Nat} (hz : z < Q.b) (hz' : z' < Q.b)
    (hl : t < Q.qLen z) (hl' : t' < Q.qLen z') (hT : Q.qStart z + t = Q.qStart z' + t') :
    z = z' := by
  by_contra hne
  unfold Params.qLen at hl hl'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := qStart_mono hpre (show z + 1 ≤ z' by omega) (by omega)
    have := hpre.cuMono z hz
    omega
  · have := qStart_mono hpre (show z' + 1 ≤ z by omega) (by omega)
    have := hpre.cuMono z' hz'
    omega

/-- A valid row's token is below its request's length. -/
theorem valid_tok {g : Nat} {pr : Epi.Prm} (hm : Epi.Means Q L g pr) (hrv : pr.rv = true) :
    Epi.tokM (g % L.block) < Q.qLen (ProA.cta L g .z) := by
  rw [hm.rv] at hrv
  simp only [decide_eq_true_eq] at hrv
  exact hrv.2

/-- **Two threads that store one element are one thread.** -/
theorem thread_inj (hpre : Pre Q L mem0) {g g' : Nat} (hg : g < L.threads) (hg' : g' < L.threads)
    (hd : g % L.block < 128) (hd' : g' % L.block < 128)
    (hl : Epi.tokM (g % L.block) < Q.qLen (ProA.cta L g .z))
    (hl' : Epi.tokM (g' % L.block) < Q.qLen (ProA.cta L g' .z)) {j j' : Nat} (hj : j < 64)
    (hj' : j' < 64) (hx : Epi.outSplit L g = Epi.outSplit L g')
    (ht : Epi.outToken Q L g = Epi.outToken Q L g') (hh : Epi.outHead L g = Epi.outHead L g')
    (hc : Epi.outCol0 L g + j = Epi.outCol0 L g' + j') : g = g' := by
  obtain ⟨cx, cy, cz⟩ := ProA.cta_coords hpre hg
  obtain ⟨cx', cy', cz'⟩ := ProA.cta_coords hpre hg'
  obtain ⟨-, hy2, hz2⟩ := ProA.cta_lt hpre hg
  obtain ⟨-, hy2', hz2'⟩ := ProA.cta_lt hpre hg'
  have hz : ProA.cta L g .z = ProA.cta L g' .z :=
    request_inj hpre hz2 hz2' hl hl' ht
  simp only [Epi.outToken, hz] at ht
  simp only [Epi.outHead, Epi.headM, Epi.outCol0, Epi.halfM, Epi.tokM, Epi.rowM] at hh hc ht hl
  have hblock := hpre.block
  unfold kvHeads at hy2 hy2'
  have hyy : ProA.cta L g .y = ProA.cta L g' .y := by
    have := hblock
    rw [hblock] at hh
    omega
  have hc0 : g / L.block = g' / L.block := by
    refine cta_inj (b := Q.b) ?_ ?_ ?_
    · rw [← cx, ← cx']
      exact hx
    · rw [← cy, ← cy']
      exact hyy
    · rw [← cz, ← cz']
      exact hz
  rw [hblock] at hc0 hd hd' hh hc ht hl
  omega

/-! ### The store events -/

theorem lead_half : ∀ t : Nat, t < 128 → t &&& 16 = 0 → t / 16 % 2 = 0 := by decide

/-- **An output element has one store event.** -/
theorem storeOnce (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : StoreOnce X := by
  intro g k g' k' pc pc' a a' bs bs' he he' hsp hsp' hov
  obtain ⟨l, hc, hc'⟩ := hov
  have hg := Frame.lt_of_get hX he
  have hg' := Frame.lt_of_get hX he'
  obtain ⟨d, d', hσ, hσ', hcase⟩ := global_writes_same_element hpre hf hg hg' he he' hsp hsp' hc hc'
  obtain ⟨d0, hσ0, -, hm, hrv, -⟩ := hf.global_wr hg he hsp
  obtain ⟨d0', hσ0', -, hm', hrv', -⟩ := hf.global_wr hg' he' hsp'
  rw [hσ] at hσ0
  rw [hσ'] at hσ0'
  have e1 := DComp.St.epi.inj (TSt.d.inj (Option.some.inj (Option.some.inj hσ0)))
  have e2 := DComp.St.epi.inj (TSt.d.inj (Option.some.inj (Option.some.inj hσ0')))
  subst e1 e2
  obtain ⟨hdef, -⟩ := hf.reach hg hσ
  obtain ⟨hdef', -⟩ := hf.reach hg' hσ'
  have hl := valid_tok hm hrv
  have hl' := valid_tok hm' hrv'
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hk2 : k' < (X.tr g').length := (List.getElem?_eq_some_iff.mp he').1
  obtain ⟨-, -, -, -, hi, -⟩ := Frame.fired_site hf.sound hX he hσ
  obtain ⟨-, -, -, -, hi', -⟩ := Frame.fired_site hf.sound hX he' hσ'
  have hi2 : Epi.Inv d := hi.2.1
  have hi2' : Epi.Inv d' := hi'.2.1
  have hgg : g = g' ∧ d.site = d'.site := by
    rcases hcase with ⟨j, j', hs, hs', hx, ht, hh, hcol⟩ | ⟨hs, hs', hx, ht, hh⟩
    · have := thread_inj hpre hg hg' hdef hdef' hl hl' j.isLt j'.isLt hx ht hh hcol
      subst this
      have hjj : j = j' := Fin.ext (by
        simp only [Epi.outCol0] at hcol
        omega)
      subst hjj
      exact ⟨rfl, by rw [hs, hs']⟩
    · have hl1 : d.pr.lead = true := hi2.lead hs
      have hl2 : d'.pr.lead = true := hi2'.lead hs'
      simp only [Epi.Prm.lead, decide_eq_true_eq] at hl1 hl2
      rw [hm.tid] at hl1
      rw [hm'.tid] at hl2
      have hmod1 : g % L.block % Epi.M32 = g % L.block := Nat.mod_eq_of_lt (by
        have : g % L.block < 128 := hdef
        unfold Epi.M32; omega)
      have hmod2 : g' % L.block % Epi.M32 = g' % L.block := Nat.mod_eq_of_lt (by
        have : g' % L.block < 128 := hdef'
        unfold Epi.M32; omega)
      rw [hmod1] at hl1
      rw [hmod2] at hl2
      have h1 := lead_half _ hdef hl1
      have h2 := lead_half _ hdef' hl2
      have hcol : Epi.outCol0 L g + 0 = Epi.outCol0 L g' + 0 := by
        simp only [Epi.outCol0, Epi.halfM]
        omega
      have := thread_inj hpre hg hg' hdef hdef' hl hl' (j := 0) (j' := 0) (by omega)
        (by omega) hx ht hh hcol
      subst this
      exact ⟨rfl, by rw [hs, hs']⟩
  obtain ⟨rfl, hsite⟩ := hgg
  by_contra hne
  have hkk : k ≠ k' := fun h => hne (by rw [h])
  rcases Nat.lt_or_gt_of_ne hkk with hlt | hlt
  · have := epi_once hf.tracked hg (e := ⟨pc, .wr a bs⟩) he rfl hσ hlt hk2.le hσ'
    simp only [Bound.Epi.rank, hsite] at this
    omega
  · have := epi_once hf.tracked hg (e := ⟨pc', .wr a' bs'⟩) he' rfl hσ' hlt hk.le hσ
    simp only [Bound.Epi.rank, hsite] at this
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
