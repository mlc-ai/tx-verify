-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QRoute
public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Gate
public import Kernels.InklingRelDecode.Proof.Prologue.Data.QuerySite
public import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Lemmas.Flow.IssueNext

@[expose] public section

/-! # The strict barrier before the preload blocks -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem bar2_tags : (∀ τ ∈ Data.tags (.pb 0 0), τ ∈ Data.tags .bar2) ∧
    (ctlLive 316).isSublist (ctlLive 189) = true := by decide +kernel

/-- No step: the site's facts at a pc are among the facts of the site before. -/
theorem site_subAt (c : Control.D) (v : Data.Vals) (s s' : Site) (pc a : Nat)
    (ht : ∀ τ ∈ Data.tags s', τ ∈ Data.tags s) (hl : (ctlLive s'.pc).isSublist (ctlLive pc) =
        true) :
    SegQ kernel Assumptions.all L g (QT proQt) a (dFactsAt Q L g w (dq c v s) pc) a
      (dFacts Q L g w (dq c v s')) := by
  refine SegQ.sub fun q hq' => ?_
  rcases List.mem_append.mp hq' with h | h
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
    rw [tag_val_site (Q := Q) (L := L) (g := g) c v s' s τ]
    exact List.mem_append_left _ (List.mem_map_of_mem
      (f := fun τ => (τ.reg, τ.val Q L g (dq c v s))) (ht τ hτ))
  · exact List.mem_append_right _ (mem_facts_sub hl h)


theorem pre_bounds {m} (hp : Pre Q L m) (hg : g < L.threads) (r : Nat)
    (hr : r = reqOf L g) : Q.qStart r ≤ Q.qStart (r + 1) ∧ Q.qStart (r + 1) < 2 ^ 32 ∧
    Q.qLen r ≤ Q.seqK r ∧ Q.seqK r + 511 < 2 ^ 31 := by
  obtain ⟨-, -, hz⟩ := Lib.coordinate_bounds hp hg
  have hz' : r < Q.b := hr ▸ hz
  refine ⟨hp.cuMono r hz', ?_, hp.qLenSeq r hz', hp.seqRange r hz'⟩
  have := (Lib.qStart_mono hp (r := r + 1) (r' := Q.b) (by omega) le_rfl).trans hp.cuEnd
  have := hp.nTokRange
  omega

/-- **The barrier before the preload blocks** strictly steps to the first block or to the
query entry. -/
theorem step_bar2 {m} (hp : Pre Q L m) (hg : g < L.threads) (hw0 : w = b32 0) (d : Data.D)
    (hs : d.c.site = .bar2) (hk : Ok Q L g d) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a0, b0, c0, won, bcast⟩, vs⟩ := d
  cases hs
  have ha : a0 = b32 (Q.qStart (reqOf L g)) := hk.1.first (by change 34 < 180; decide)
  have hb : b0 = b32 (Q.qStart (reqOf L g + 1)) := hk.1.last (by change 37 < 180; decide)
  have hc : c0 = b32 (Q.seqK (reqOf L g)) := hk.1.seq (by change 41 < 180; decide)
  subst ha hb hc
  obtain ⟨h1, h2, h3, h4⟩ := pre_bounds hp hg _ rfl
  obtain ⟨hx, -, -⟩ := Lib.coordinate_bounds hp hg
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let A := Q.qStart (reqOf L g)
  let Y := Q.qStart (reqOf L g + 1)
  let P := Q.seqK (reqOf L g)
  let c : Control.D := (dS .bar2 A Y P won bcast vs).c
  let sB : Site := if preloadN Q L g c = 0 then querySite (g % L.block) c 0 else .pb 0 0
  have hnext : ∀ e, (Data.code Q L g w).next (dS .bar2 A Y P won bcast vs) e = some (some
      ⟨{c with site := sB}, vs⟩) := fun _ => rfl
  have pay : Payload {c with site := sB} := payload_next (Q := Q) (L := L) (g := g) (d := c) (e :=
      ⟨0, .exit⟩) rfl hpay
    (fun j h => by cases h)
  by_cases hn : preloadN Q L g c = 0
  · have eB : sB = querySite (g % L.block) c 0 := by simp [sB, hn]
    obtain ⟨hi, hle, -, hsite, hoff, hon⟩ := Data.querySite_spec (g % L.block) c 0 (by omega)
    rw [eB, hsite] at hnext pay
    have hinv : Control.Inv (g % L.block) {c with site := qSiteAt hi} := by
      unfold qSiteAt
      split
      · exact hon (by omega)
      · trivial
    have hsub : (qSiteAt hi).sub = 0 := by unfold qSiteAt; split <;> rfl
    have hb := gate_bra_q (Q := Q) (L := L) (g := g) (w := w) A Y P won bcast vs
    rw [show decide (nB (Q := Q) (L := L) (g := g) A Y P won bcast vs ≠ 0) = false by
      simpa using hn] at hb
    have hb' : SegQ kernel Assumptions.all L g (QT proQt) 189 (dFactsAt Q L g w
        (dS .bar2 A Y P won bcast vs) 189) 316 (dFactsAt Q L g w (dS .bar2 A Y P won bcast vs) 189)
        := by simpa using hb
    refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := dS .bar2 A Y P won bcast vs) (dn := ⟨{c with site := qSiteAt hi}, vs⟩) Flow.code_180
      (fun h => fires_barSyncN_next h) hnext rfl rfl hsub rfl ⟨hinv, pay⟩ (fun _ _ => typed_nil')
      (by decide +kernel : Code.afterWrites proQt 180 [] [] = true) ?_ e ins hat ⟨hI, hpay⟩ hc hq hw
      hf
    have fin : SegQ kernel Assumptions.all L g (QT proQt) 316
        (dFactsAt Q L g w (dS .bar2 A Y P won bcast vs) 189) (qSiteAt hi).pc
        (dFacts Q L g w ⟨{c with site := qSiteAt hi}, vs⟩) :=
      SegQ.comp (b := 316) (G := [(525, Data.scaleVal L)] ++ facts Q L g w c 316)
        (SegQ.sub fun q hq' => ?_) (qentry hp hw0 c vs hk.qBytes hi hle fun n hn' => hoff n (by
            omega) hn')
    refine dFacts_seg (pre := []) (SegQ.comp (b := 182) (G := dFactsAt Q L g w
      (dS .bar2 A Y P won bcast vs) 182) (gate_a A Y P won bcast vs) ?_)
    refine SegQ.comp (b := 183) (G := dFactsAt Q L g w (dS .bar2 A Y P won bcast vs) 183)
      (gate_d A Y P won bcast vs (reqOf L g) rfl rfl rfl h1 h2 h3 h4 hp.splitsPos hx
        hp.splitsRange) ?_
    refine SegQ.comp (b := 185) (G := dFactsAt Q L g w (dS .bar2 A Y P won bcast vs) 185)
      (gate_c A Y P won bcast vs) ?_
    exact SegQ.comp (b := 189) (G := dFactsAt Q L g w (dS .bar2 A Y P won bcast vs) 189)
      (gate_f A Y P won bcast vs) (hb'.comp fin)
    rcases List.mem_append.mp hq' with h | h
    · rcases List.mem_singleton.mp h with rfl
      exact List.mem_append_left _ (List.mem_map.mpr ⟨.scale, (by decide +kernel : Data.Tag.scale
          ∈ Data.tags .bar2), rfl⟩)
    · exact List.mem_append_right _ (mem_facts_sub (c := c) (pc := 189) bar2_tags.2 h)
  · have eB : sB = .pb 0 0 := by simp [sB, hn]
    rw [eB] at hnext pay
    obtain ⟨ht, hl⟩ := bar2_tags
    refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
      (d := dS .bar2 A Y P won bcast vs) (dn := ⟨{c with site := .pb 0 0}, vs⟩) Flow.code_180
      (fun h => fires_barSyncN_next h) hnext rfl rfl rfl rfl ⟨trivial, pay⟩ (fun _ _ => typed_nil')
      (by decide +kernel : Code.afterWrites proQt 180 [] [] = true) ?_ e ins hat ⟨hI, hpay⟩ hc hq hw
      hf
    exact dFacts_seg (pre := []) ((gate_ne (Q := Q) (L := L) (g := g) (w := w) A Y P won bcast vs
      (reqOf L g) rfl rfl rfl h1 h2 h3 h4 hp.splitsPos hx hp.splitsRange hn).comp
      (site_subAt c vs .bar2 (.pb 0 0) 192 192 ht (by decide +kernel)))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
