-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace

@[expose] public section

/-!
# Every output word of a valid row is stored (result layer, part 2f)

A thread of the default partition passes the epilogue's sites in order. `exists_oStore` and
`exists_lseStore` say for every valid row and word there is a thread, in the
CTA `(split, kv_head, request)`, whose epilogue visits the store site of the word, and the event it
fires there is the store of `Spec`'s footprint.

* `next_site`, `next_pass`, `epi_pred`, `visits`: the epilogue's sites have positions
  (`sitePos`); a state at or past the position of a store site (`stO j`; `stLse` for a storing
  lane) had visited it, since the epilogue is entered at the poll and advances one site at a time
  (`Epi.next`).
* `thread_of_cta`, `tid_of_row`: the thread of an output row and half.
* `exists_oStore`, `exists_lseStore`: a complete execution has the store event of every valid
  word, with `Epi.shape_stO_loc` / `shape_stLse_loc` giving its footprint.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof

noncomputable section

def sitePos : Epi.Site → Nat
  | .wait => 0 | .shfl => 1 | .ld => 2 | .waitLd => 3 | .stLse => 4 | .stO k => 5 + k.val
  | .bar1 => 69 | .setMaxInc => 70 | .stTab => 71 | .bar2 => 72 | .bar3 => 73
  | .dealloc => 74 | .exit => 75

theorem next_site {d d' : Epi.D} {e : Event} (hn : Epi.next d e = some (some d')) :
    d'.pr = { d.pr with bw := d'.pr.bw } ∧ d'.sk = d.sk ∧ (d.site = .ld ∨ d'.o = d.o) ∧
      (d'.site = d.site ∨ sitePos d'.site = sitePos d.site + 1 ∨
        ((d.site = .waitLd ∨ (d.site = .wait ∧ d.sk = true)) ∧ d'.site = d.stores) ∨
        (d.site = .bar3 ∧ d'.site = .exit)) := by
  obtain ⟨site, pr, o, sk⟩ := d
  cases site with
  | wait =>
    simp only [Epi.next] at hn
    split at hn <;> try cases hn
    rename_i _ _ ok _ _ _
    split at hn
    · split at hn
      · split at hn
        · rename_i hsk
          cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inr (.inl ⟨.inr ⟨rfl, hsk⟩, rfl⟩))⟩
        · split at hn
          · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
          · cases hn
      · cases hn
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inl rfl⟩
  | shfl =>
    simp only [Epi.next] at hn
    split at hn <;> try cases hn
    split at hn
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
    · cases hn
  | ld =>
    simp only [Epi.next] at hn
    split at hn <;> try cases hn
    split at hn
    · cases hn; exact ⟨rfl, rfl, .inl rfl, .inr (.inl rfl)⟩
    · cases hn
  | waitLd =>
    simp only [Epi.next] at hn
    split at hn
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inr (.inl ⟨.inl rfl, rfl⟩))⟩
    · cases hn
  | stLse =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | stO k =>
    simp only [Epi.next, Epi.stNext] at hn
    split at hn
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl (by simp [sitePos]; omega))⟩
    · cases hn
      refine ⟨rfl, rfl, .inr rfl, .inr (.inl ?_)⟩
      have : k.val = 63 := by omega
      simp [sitePos, this]
  | bar1 =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | setMaxInc =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | stTab =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | bar2 =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | bar3 =>
    simp only [Epi.next] at hn
    split at hn
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
    · cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inr (.inr ⟨rfl, rfl⟩))⟩
  | dealloc =>
    simp only [Epi.next] at hn
    cases hn; exact ⟨rfl, rfl, .inr rfl, .inr (.inl rfl)⟩
  | exit =>
    simp [Epi.next] at hn

theorem sitePos_inj {a b : Epi.Site} (h : sitePos a = sitePos b) : a = b := by
  cases a <;> cases b <;> simp [sitePos] at h ⊢ <;> omega

/-- Passing a store site: the successor is the site, or the predecessor had passed it. -/
theorem next_pass {t : Epi.Site} (ht : 4 ≤ sitePos t ∧ sitePos t ≤ 68) {d d' : Epi.D}
    {e : Event} (hrv : d.pr.rv = true) (hl : t = .stLse → d.pr.lead = true)
    (hn : Epi.next d e = some (some d')) (hp : sitePos t ≤ sitePos d'.site) :
    d'.site = t ∨ sitePos t ≤ sitePos d.site := by
  obtain ⟨-, -, -, h⟩ := next_site hn
  rcases h with h | h | ⟨-, h⟩ | ⟨hs, h⟩
  · exact .inr (by rw [← h]; exact hp)
  · by_cases hq : sitePos t = sitePos d'.site
    · exact .inl (sitePos_inj hq).symm
    · right; omega
  · left
    have p4 : sitePos .stLse = 4 := rfl
    have p5 : sitePos (.stO 0) = 5 := rfl
    unfold Epi.D.stores at h
    by_cases hlead : d.pr.lead = true
    · simp only [hrv, hlead, ↓reduceIte] at h
      rw [h] at hp ⊢
      rw [p4] at hp
      have : sitePos t = sitePos .stLse := by rw [p4]; omega
      exact (sitePos_inj this).symm
    · have hlead' : d.pr.lead = false := by simpa using hlead
      simp only [hrv, hlead', Bool.false_eq_true, ↓reduceIte] at h
      rw [h] at hp ⊢
      rw [p5] at hp
      by_cases h4 : sitePos t = 4
      · exact absurd (hl (sitePos_inj (by rw [h4, p4]))) hlead
      · have : sitePos t = sitePos (.stO 0) := by rw [p5]; omega
        exact (sitePos_inj this).symm
  · right
    have h3 : sitePos d.site = 73 := by rw [hs]; rfl
    omega

variable {L : Launch} {g : Nat} {Q : Params}

theorem epi_pred {s0 : Interface.TSt} {e : Event} {d : Epi.D}
    (h : (Interface.threadCode L g Q).next s0 e = some (some (.d (.epi d)))) :
    (∃ d0, s0 = .d (.epi d0) ∧ Epi.next d0 e = some (some d)) ∨
    (∃ dsm : Sm.D, s0 = .d (.sm dsm) ∧
      d = if (DComp.exitIn L g dsm).skip then Epi.D.startSk (Br.prm (DComp.exitIn L g dsm))
        else Epi.D.start (Br.prm (DComp.exitIn L g dsm))) := by
  cases s0 with
  | w s =>
    rw [Interface.next_w] at h
    cases hh : WComp.next L g s e with
    | none => rw [hh] at h; simp at h
    | some o =>
      cases o with
      | none => rw [hh] at h; simp at h
      | some s' => rw [hh] at h; simp at h
  | d s =>
    rw [Interface.next_d] at h
    cases hh : DComp.next L g Q s e with
    | none => rw [hh] at h; simp at h
    | some o =>
      cases o with
      | none => rw [hh] at h; simp at h
      | some s' =>
        rw [hh] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have h' : s' = .epi d := by cases s' <;> simp_all [Interface.TSt.d.injEq]
        subst h'
        cases s with
        | dstart d0 =>
          simp only [DComp.next, DComp.dstartNext] at hh
          rcases hn : DStart.next L g d0 e with _ | _ | d'
          · simp [hn] at hh
          · simp [hn] at hh
          · simp only [hn, Option.map_some] at hh
            split_ifs at hh <;> simp at hh
        | pro d0 =>
          simp only [DComp.next, DComp.proNext] at hh
          split_ifs at hh
          all_goals simp at hh
        | sm d0 =>
          right
          refine ⟨d0, rfl, ?_⟩
          simp only [DComp.next, DComp.smNext] at hh
          split_ifs at hh with hl
          · unfold DComp.exitNext at hh
            split_ifs at hh with hnf hsk
            · simp only [hsk, ↓reduceIte]
              simpa using hh.symm
            · simp only [hsk, Bool.false_eq_true, ↓reduceIte]
              simpa using hh.symm
          · rcases hn : Sm.next L g d0 e with _ | _ | d'
            · simp [hn] at hh
            · simp [hn] at hh
            · simp [hn] at hh
        | epi d0 =>
          left
          refine ⟨d0, rfl, ?_⟩
          simp only [DComp.next] at hh
          cases hn : Epi.next d0 e with
          | none => rw [hn] at hh; simp at hh
          | some o =>
            cases o with
            | none => rw [hn] at hh; simp at hh
            | some d1 =>
              rw [hn] at hh
              simp only [Option.map_some, DComp.St.epi.injEq, Option.some.injEq] at hh
              rw [hh]

theorem visits {X : Execution} {t : Epi.Site} (ht : 4 ≤ sitePos t ∧ sitePos t ≤ 68)
    (hrv : ∀ {k : Nat} {d : Epi.D}, Interface.St Q L X g k = some (some (.d (.epi d))) →
      d.pr.rv = true)
    (hl : t = .stLse → ∀ {k : Nat} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.lead = true) :
    ∀ (k : Nat) (d : Epi.D), Interface.St Q L X g k = some (some (.d (.epi d))) →
      sitePos t ≤ sitePos d.site →
      ∃ k' ≤ k, ∃ d' : Epi.D, Interface.St Q L X g k' = some (some (.d (.epi d'))) ∧
        d'.site = t := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hσ hp
    have hne : (Interface.TSt.d (.epi d)) ≠ (Interface.code L Q g).init := by
      simp only []
      split_ifs <;> simp
    obtain ⟨k0, e, s0, hk0, he, hσ0, hn⟩ := Interface.stateAt_pred hσ hne
    rcases epi_pred hn with ⟨d0, rfl, hnx⟩ | ⟨dsm, -, hd⟩
    · rcases next_pass ht (hrv hσ0) (fun h => hl h hσ0) hnx hp with h | h
      · exact ⟨k, le_rfl, d, hσ, h⟩
      · obtain ⟨k', hk', d', h1, h2⟩ := ih k0 hk0 d0 hσ0 h
        exact ⟨k', by omega, d', h1, h2⟩
    · exfalso
      have h0 : sitePos d.site = 0 := by rw [hd]; split_ifs <;> rfl
      omega

/-! ### The thread of an output row -/

variable {mem0 : Mem0}

/-- **The thread of a CTA and a thread index**: the CTA `(split, kv_head, request)` of the grid has
the thread `cta · block + tid`, below `L.threads`. -/
theorem thread_of_cta (hpre : Pre Q L mem0) {r s kvh tid : Nat} (hr : r < Q.b)
    (hs : s < Q.splits) (hk : kvh < 2) (htid : tid < 128) :
    ∃ g, g < L.threads ∧ g % L.block = tid ∧ ProA.cta L g .x = s ∧ ProA.cta L g .y = kvh ∧
      ProA.cta L g .z = r := by
  have hB : 0 < Q.b := by omega
  have hblk := hpre.block
  set c := s * (2 * Q.b) + kvh * Q.b + r with hc
  have h1 : kvh * Q.b ≤ 1 * Q.b := Nat.mul_le_mul_right _ (by omega)
  have h2 : c < (s + 1) * (2 * Q.b) := by rw [Nat.succ_mul]; omega
  have h3 : (s + 1) * (2 * Q.b) ≤ Q.splits * (2 * Q.b) := Nat.mul_le_mul_right _ hs
  have hcg : c < L.grid := by
    rw [hpre.grid]
    have : Q.splits * kvHeads * Q.b = Q.splits * (2 * Q.b) := by unfold kvHeads; ring
    omega
  have hg : c * L.block + tid < L.threads := by
    unfold Launch.threads
    have : (c + 1) * L.block ≤ L.grid * L.block := Nat.mul_le_mul_right _ hcg
    rw [Nat.succ_mul] at this
    omega
  refine ⟨c * L.block + tid, hg, ?_, ?_⟩
  · rw [show c * L.block + tid = tid + L.block * c by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (c * L.block + tid) / L.block = c := by
    rw [show c * L.block + tid = tid + L.block * c by ring, Nat.add_mul_div_left _ _ (by omega)]
    have : tid / L.block = 0 := Nat.div_eq_of_lt (by omega)
    omega
  obtain ⟨hx, hy, hz⟩ := ProA.cta_coords hpre hg
  rw [hdiv] at hx hy hz
  have hcr : c = r + Q.b * (2 * s + kvh) := by rw [hc]; ring
  have hcs : c = (kvh * Q.b + r) + (kvHeads * Q.b) * s := by unfold kvHeads; rw [hc]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, hcs, Nat.add_mul_div_left _ _ (by unfold kvHeads; omega),
      Nat.div_eq_of_lt (by unfold kvHeads; omega)]
    simp
  · rw [hy, hcr, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hr]
    unfold kvHeads
    omega
  · rw [hz, hcr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The thread index of a tile row and half: `tid = 32 · (row / 16) + 16 · half + row % 16`. -/
theorem tid_of_row {m half : Nat} (hm : m < 64) (hhalf : half < 2) :
    ∃ tid, tid < 128 ∧ Epi.rowM tid = m ∧ Epi.halfM tid = half := by
  refine ⟨32 * (m / 16) + 16 * half + m % 16, by omega, ?_, ?_⟩
  · unfold Epi.rowM
    omega
  · unfold Epi.halfM
    omega

/-- A thread index of the first half row is a storing lane. -/
theorem lead_of_half : ∀ t : Nat, t < 128 → t / 16 % 2 = 0 → t &&& 16 = 0 := by decide

/-! ### The store events of a complete execution -/

variable {X : Execution}

/-- **A thread of a valid row has a store event at a store site**: a complete execution's thread
exits from the epilogue's return, so it visited the site, and the event fired there. -/
theorem store_event (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hf : Interface.ThreadFacts Q L mem0 X) {g : Nat}
    (hg : g < L.threads) (hdef : g % L.block < 128) {t : Epi.Site}
    (ht : 4 ≤ sitePos t ∧ sitePos t ≤ 68)
    (hrv : ∀ {k : Nat} {d : Epi.D}, Interface.St Q L X g k = some (some (.d (.epi d))) →
      d.pr.rv = true)
    (hl : t = .stLse → ∀ {k : Nat} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.lead = true) :
    ∃ (k : Nat) (d : Epi.D) (e : Event) (u : TState), (X.tr g)[k]? = some e ∧
      Interface.St Q L X g k = some (some (.d (.epi d))) ∧ d.site = t ∧
      Epi.Fired L g d e (some u) := by
  obtain ⟨kx, pcx, hex, hcase⟩ := Interface.exit_of_complete hX hf.sound hf.tracked hcomp hg
  obtain ⟨dx, hσx, hsx⟩ : ∃ d : Epi.D, Interface.St Q L X g kx = some (some (.d (.epi d))) ∧
      d.site = .exit := by
    rcases hcase with h | ⟨x, hσx, -⟩
    · exact h
    · exfalso
      obtain ⟨t', ins, o, hat, hinv, hc, hf'⟩ := Frame.fired_site hf.sound hX hex hσx
      exact hinv.1 hdef
  have hp : sitePos t ≤ sitePos dx.site := by
    rw [hsx]
    show sitePos t ≤ 75
    omega
  obtain ⟨k', hk', d', hσ', hs'⟩ := visits ht hrv hl kx dx hσx hp
  have hne : k' ≠ kx := by
    rintro rfl
    rw [hσx] at hσ'
    have := Option.some.inj (Option.some.inj hσ')
    have h2 : d' = dx := by cases this; rfl
    rw [h2, hsx] at hs'
    have : sitePos t = 75 := by rw [← hs']; rfl
    omega
  have hlen : kx < (X.tr g).length := (List.getElem?_eq_some_iff.mp hex).1
  obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k']? = some e' :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hnx : ¬ Interface.ExitState (.d (.epi d')) := by
    show ¬ d'.site = .exit
    rw [hs']
    intro h
    have : sitePos t = 75 := by rw [h]; rfl
    omega
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he' hσ' hnx
  exact ⟨k', d', e', u, he', hσ', hs', Interface.fired_epi hF⟩

/-- **A complete execution stores every word of `OPart` of a valid row.** -/
theorem exists_oStore (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hf : Interface.ThreadFacts Q L mem0 X) {r s tok head dc : Nat}
    (hr : r < Q.b) (hs : s < Q.splits) (ht : tok < Q.qLen r) (hh : head < heads)
    (hd : dc < headDim) :
    ∃ (g k pc : Nat) (bs : List Byte), g < L.threads ∧
      X.get (g, k) = some ⟨pc, .wr (EvD.wordAcc (oLoc Q s (Q.qStart r + tok) head dc)) bs⟩ := by
  have hqle := hpre.qLenLe r hr
  have hh' : head < 12 := hh
  have hd' : dc < 128 := hd
  obtain ⟨tid, htid, hrow, hhalf⟩ := tid_of_row (m := 6 * tok + head % 6) (half := dc / 64)
    (by omega) (by omega)
  obtain ⟨g, hg, hgt, hx, hy, hz⟩ := thread_of_cta hpre (kvh := head / 6) hr hs (by omega) htid
  have hvalid : Epi.rowM (g % L.block) < 60 ∧
      Epi.tokM (g % L.block) < Q.qLen (ProA.cta L g .z) := by
    rw [hgt, hz]
    unfold Epi.tokM
    rw [hrow]
    omega
  have hrv : ∀ {k : Nat} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.rv = true := by
    intro k d hσ
    have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
    rw [hm.rv]
    exact decide_eq_true hvalid
  obtain ⟨k, d', e, u, he, hσ, hs', hF⟩ := store_event hX hcomp hf hg
    (by rw [hgt]; exact htid) (t := .stO ⟨dc % 64, by omega⟩)
    (by simp only [sitePos]; omega) hrv (fun h => by cases h)
  have hm : Epi.Means Q L g d'.pr := (hf.reach hg hσ).2
  obtain ⟨v', -, he2⟩ := Epi.shape_stO_loc hpre hg hm hF hs'
  have e1 : Epi.outSplit L g = s := hx
  have e2 : Epi.outToken Q L g = Q.qStart r + tok := by
    show Q.qStart (ProA.cta L g .z) + Epi.tokM (g % L.block) = _
    rw [hz, hgt]
    unfold Epi.tokM
    rw [hrow]
    omega
  have e3 : Epi.outHead L g = head := by
    show Epi.headM (ProA.cta L g .y) (g % L.block) = _
    unfold Epi.headM
    rw [hy, hgt, hrow]
    omega
  have e4 : Epi.outCol0 L g + dc % 64 = dc := by
    show 64 * Epi.halfM (g % L.block) + dc % 64 = _
    rw [hgt, hhalf]
    omega
  rw [e1, e2, e3, e4] at he2
  exact ⟨g, k, _, v'.toBytes, hg, by rw [Execution.get]; show (X.tr g)[k]? = _; rw [he, he2]⟩

/-- **A complete execution stores the word of `LsePart` of a valid row.** -/
theorem exists_lseStore (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hcomp : Complete L X) (hf : Interface.ThreadFacts Q L mem0 X) {r s tok head : Nat}
    (hr : r < Q.b) (hs : s < Q.splits) (ht : tok < Q.qLen r) (hh : head < heads) :
    ∃ (g k pc : Nat) (bs : List Byte), g < L.threads ∧
      X.get (g, k) = some ⟨pc, .wr (EvD.wordAcc (lseLoc Q s (Q.qStart r + tok) head)) bs⟩ := by
  have hqle := hpre.qLenLe r hr
  have hh' : head < 12 := hh
  obtain ⟨tid, htid, hrow, hhalf⟩ := tid_of_row (m := 6 * tok + head % 6) (half := 0)
    (by omega) (by omega)
  obtain ⟨g, hg, hgt, hx, hy, hz⟩ := thread_of_cta hpre (kvh := head / 6) hr hs (by omega) htid
  have hvalid : Epi.rowM (g % L.block) < 60 ∧
      Epi.tokM (g % L.block) < Q.qLen (ProA.cta L g .z) := by
    rw [hgt, hz]
    unfold Epi.tokM
    rw [hrow]
    omega
  have hrv : ∀ {k : Nat} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.rv = true := by
    intro k d hσ
    have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
    rw [hm.rv]
    exact decide_eq_true hvalid
  have hlead : ∀ {k : Nat} {d : Epi.D},
      Interface.St Q L X g k = some (some (.d (.epi d))) → d.pr.lead = true := by
    intro k d hσ
    have hm : Epi.Means Q L g d.pr := (hf.reach hg hσ).2
    unfold Epi.Prm.lead
    rw [hm.tid, hgt]
    have h1 := lead_of_half tid htid (by simpa [Epi.halfM] using hhalf)
    exact decide_eq_true (by unfold Epi.M32; rw [Nat.mod_eq_of_lt (by omega)]; exact h1)
  obtain ⟨k, d', e, u, he, hσ, hs', hF⟩ := store_event hX hcomp hf hg
    (by rw [hgt]; exact htid) (t := .stLse) (by simp only [sitePos]; omega) hrv
    (fun _ {_ _} hσ => hlead hσ)
  have hm : Epi.Means Q L g d'.pr := (hf.reach hg hσ).2
  obtain ⟨v', -, he2⟩ := Epi.shape_stLse_loc hpre hg hm hF hs'
  have e1 : Epi.outSplit L g = s := hx
  have e2 : Epi.outToken Q L g = Q.qStart r + tok := by
    show Q.qStart (ProA.cta L g .z) + Epi.tokM (g % L.block) = _
    rw [hz, hgt]
    unfold Epi.tokM
    rw [hrow]
    omega
  have e3 : Epi.outHead L g = head := by
    show Epi.headM (ProA.cta L g .y) (g % L.block) = _
    unfold Epi.headM
    rw [hy, hgt, hrow]
    omega
  rw [e1, e2, e3] at he2
  exact ⟨g, k, _, v'.toBytes, hg, by rw [Execution.get]; show (X.tr g)[k]? = _; rw [he, he2]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Out
