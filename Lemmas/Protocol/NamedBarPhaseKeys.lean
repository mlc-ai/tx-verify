-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarPhase
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Protocol.NamedBarArrive

@[expose] public section

/-!
# The generations of a loop group of a named barrier, from the sources of its events

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/BarLaneKeys.lean`):
the execution side of `NamedBarPhase.lean`. A barrier `id` whose arrivals follow `PhSources` (each
arrival event has no count, or the loop group's count and a loop warp and a source ordinal at
least `start`) has, for the loop group's warps, the library's key discipline: a recorded arrival
of a loop warp is in the generation equal to its source ordinal (`D_arrival_key`), a passed
arrival releases it, and a reached arrival of a loop warp whose generation was released by another
passed loop arrival of the same ordinal is recorded in it (`D_key_of_released`). From them:

* `D_same_ordinal_witness`: two loop-warp `bar.sync` events of one CTA and one ordinal, the second
  passed: the first is a `Witness` of the return of the second (the form of
  `Mbar.Bar128Witness`);
* `D_same_ordinal_baseCausality`: what the first thread did before its arrival happens before what
  the second does after passing its own.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

section Exec

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {D : Finset Nat} {cD : Option Nat} {start id : Nat}

/-- **The sources of the arrivals on `id`**: an arrival event has no count, or the loop group's
count, a loop warp and a source ordinal at least `start`. -/
def PhSources (L : Launch) (X : Execution) (D : Finset Nat) (cD : Option Nat) (start id : Nat) :
    Prop :=
  ∀ e pc cnt, X.IsBarArrival e id cnt pc → e.1 < L.threads →
    SrcOk D cD start ((e.1 % L.block) / 32)
      (((X.tr e.1).take e.2).countP (Execution.isBarId id)) cnt

/-- **The history of a CTA follows `SrcOk`.** -/
theorem PhSources.protocol (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    {c : Nat} (hc : c < L.grid) : PhProtocol D cD start id (X.barriers c) := by
  intro k warp cnt lanes hk
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 c hc
  obtain ⟨s, t, hat, hp⟩ := run_at_record hlast hk
  obtain ⟨e, he⟩ := perform_ref_exists hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  obtain ⟨hql, hq2, hqw, ⟨pc, hbar⟩, hord, -⟩ := record_ordinal hX hc hlast hk hat hq
  have hthr : q.2.1 < L.threads := by
    rw [hq2]
    exact cta_thread_lt hc hql
  have hmod : q.2.1 % L.block = q.1 := by
    rw [hq2, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hql]
  have := hS q.2 pc cnt hbar hthr
  rwa [hmod, hqw, ← hord] at this

variable {nD : Nat}

/-- **The generation of a recorded loop-warp arrival is its source ordinal.** -/
theorem D_arrival_key (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD) {e : EvId} {pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get e = some ⟨pc, .bar id cnt m⟩) (hw : (e.1 % L.block) / 32 ∈ D) {key : Nat}
    (hk : CtaBarArrivalK L X e key) :
    key = id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id) := by
  have hid : key % 16 = id := by
    obtain ⟨count', pc', mode', he'⟩ := hk.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans he))).2).1
  have hidl : id < 16 := by
    obtain ⟨index, s, warp, cnt', lanes, g, hr, hs, hm, hphase, t, ht⟩ := hk.2.2
    have := hX.ctaBar.arrival_id_lt hr
    rw [hid] at this
    exact this
  have hg := hk.1
  have hc := cta_lt hg
  have hgen := hk.2.2
  rw [hid] at hgen
  obtain ⟨index, s, warp, cnt', lanes, g, hr, hs, hm, hphase, t, ht⟩ := hgen
  have href : e ∈ (Record.arrival id warp cnt' lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩
  have hprot := hS.protocol hX hc
  have hgl := gen_of_record hD hcard hnD hcD hprot hs ht
  obtain ⟨hgb, hthread, -⟩ := ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hr)) (g, e) hm
  have hlane := (perform_arrival_lanes ht).2.1 (g, e) hm
  have hocc := cta_prefix_id_arrival_count (id := id) hX hc hr href hs hgb hthread hlane.2.2 rfl
  simp only at hlane
  rw [hlane.2.1] at hocc
  have hwarp : (e.1 % L.block) / 32 = warp := by
    have hmod : e.1 % L.block = g := by
      rw [hthread, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hgb]
    rw [hmod, hlane.2.1]
  rw [hwarp] at hw
  have := hgl (.inl hw)
  omega

variable [hK : Fact K.NoBarArrive]

variable (hX : Consistent L K A mem0 X) (hS : PhSources L X D cD start id)
    (hD : D ⊆ Finset.range (warps L.block)) (hcard : D.card = nD) (hnD : nD ≠ warps L.block)
    (hcD : target L.block cD = .ok nD)
include hX hS hD hcard hnD hcD

/-- **A reached loop-warp arrival has its key once its generation is released.** A `bar.sync`
event of a loop warp whose source ordinal's generation was released is in that generation: it is
recorded there, or it is its thread's last event and the released generation has a record of
its lane. -/
theorem D_key_of_released {e : EvId} {pc : Nat} {cnt : Option Nat} (he : X.IsBarrier e id cnt pc)
    (hge : e.1 < L.threads) (hw : (e.1 % L.block) / 32 ∈ D)
    (hd : Released L.block (X.barriers (e.1 / L.block)) id
      (((X.tr e.1).take e.2).countP (Execution.isBarId id))) :
    CtaBarK L X e (id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
  have hb := block_pos_of_thread_lt hge
  have hc : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hge
  have hlocal : e.1 % L.block < L.block := Nat.mod_lt _ hb
  set c := e.1 / L.block with hcdef
  have hprot := hS.protocol hX hc
  have hthr : c * L.block + e.1 % L.block = e.1 := by
    rw [hcdef, Nat.mul_comm]
    exact Nat.div_add_mod e.1 L.block
  by_cases hrec : e ∈ (X.barriers c).flatMap Record.refs
  · obtain ⟨gen, hk⟩ := recorded_arrivalK hX he hge hrec
    have hkey := D_arrival_key hX hS hD hcard hnD hcD he hw hk
    rw [hkey] at hk
    exact hX.ctaBarK_of_arrival hK.out hk
  · exfalso
    have hno : ∀ j pc', X.get (c * L.block + e.1 % L.block, j) ≠ some ⟨pc', .exit⟩ := by
      intro j pc' hj
      rw [hthr] at hj
      have hlast := Execution.exit_last hX hge hj
      have hel := len_of_get he
      have hne : e.2 ≠ j := by
        intro heq
        have h2 : X.get e = some ⟨pc, .bar id cnt .sync⟩ := he
        have h3 : X.get (e.1, e.2) = some ⟨pc', .exit⟩ := by rw [heq]; exact hj
        rw [h2] at h3
        cases h3
      obtain ⟨key, hkey, -⟩ := ctaBarDone_of_returned hX he (by omega)
      obtain ⟨i, s, warp, count, lanes, g', hi, -, hm, -⟩ := hkey.2.2
      exact hrec (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi,
        List.mem_map.mpr ⟨(g', e), hm, rfl⟩⟩)
    obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 c hc
    have hlt : ((X.tr e.1).take e.2).countP (Execution.isBarId id) <
        (last.slots id).generation := released_generation_lt hlast hd
    have hlive : e.1 % L.block ∉ last.exited := by
      intro hm
      obtain ⟨a, ha⟩ := run_exited_mem hlast hm
      obtain ⟨-, hy, pcx, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ ha
      have hae : a = (c * L.block + e.1 % L.block, a.2) := Prod.ext hy rfl
      exact hno a.2 pcx (hae ▸ hget)
    obtain ⟨i, cnt', lanes, e', hi, hmem, hord, -⟩ := completed_D_record hD hcard hnD hcD hprot
      hlast hlt hlocal hw hlive
    obtain ⟨s1, t1, hat, hp1⟩ := run_at_record hlast hi
    obtain ⟨hql, hq2, hqw, ⟨pce, hbar⟩, hord', -⟩ := record_ordinal hX hc hlast hi hat
      (q := (e.1 % L.block, e')) hmem
    have hee : e'.1 = e.1 := by
      have := hq2
      simp only at this
      rw [this, hthr]
    obtain ⟨mode, hget⟩ := hbar
    have hbar' : X.IsBarrier e' id cnt' pce := hX.isBarrier_of_arrival hK.out ⟨mode, hget⟩
    have hee' : e' = (e.1, e'.2) := Prod.ext hee rfl
    have he'' : X.IsBarrier (e.1, e'.2) id cnt' pce := hee' ▸ hbar'
    rw [hee] at hord'
    have hordEq : ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
        ((X.tr e.1).take e'.2).countP (Execution.isBarId id) := hord.symm.trans hord'
    have h2 : e.2 = e'.2 := source_ordinal_unique (X := X) he he'' hordEq
    have hef : e' = e := Prod.ext hee h2.symm
    exact hrec (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi,
      List.mem_map.mpr ⟨(e.1 % L.block, e'), hmem, hef⟩⟩)


/-- **Two loop-warp arrivals of one ordinal are in one generation**: a reached `bar.sync` of one
thread and a passed `bar.sync` of another thread of the same CTA, both of loop warps with the same
source ordinal, have the same key, and the generation is released. -/
theorem D_same_key {e f : EvId} {pc pc' : Nat} {cnt cnt' : Option Nat} (hsame : SameCta L e.1 f.1)
    (he : X.IsBarrier e id cnt pc) (hf : X.IsBarrier f id cnt' pc')
    (hpassed : f.2 + 1 < (X.tr f.1).length) (hwe : (e.1 % L.block) / 32 ∈ D)
    (hwf : (f.1 % L.block) / 32 ∈ D)
    (hordinal : ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ key ic, CtaBarK L X e key ∧ CtaBarK L X f key ∧
      CompletesAt L.block (X.barriers (f.1 / L.block)) ic (key % 16) (key / 16) := by
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkeq := D_arrival_key hX hS hD hcard hnD hcD hf hwf (CtaBarK.arrival hkf)
  have hid : key % 16 = id := by
    obtain ⟨count', pc'', he'⟩ := hkf.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hf))).2).1
  have hlt : id < 16 := by omega
  have hmod : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id := by
    omega
  have hdiv : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by omega
  have hrel : Released L.block (X.barriers (f.1 / L.block)) id
      (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
    unfold CtaBarDone at hdone
    rw [hkeq, hmod, hdiv] at hdone
    exact hdone
  have hrele : Released L.block (X.barriers (e.1 / L.block)) id
      (((X.tr e.1).take e.2).countP (Execution.isBarId id)) := by
    rw [hsame.2.2, hordinal]
    exact hrel
  have hke := D_key_of_released hX hS hD hcard hnD hcD he hsame.1 hwe hrele
  rw [hordinal, ← hkeq] at hke
  obtain ⟨ic, hic⟩ := hdone
  exact ⟨key, ic, hke, hkf, hic⟩

/-- **The witness form**: the first arrival is a witness of the return of the second's passed
`bar.sync` (the arrival is counted by the release the `bar.sync` waits for). -/
theorem D_same_ordinal_witness {e f : EvId} {pc pc' : Nat} {cnt cnt' : Option Nat}
    (hsame : SameCta L e.1 f.1) (he : X.IsBarrier e id cnt pc) (hf : X.IsBarrier f id cnt' pc')
    (hpassed : f.2 + 1 < (X.tr f.1).length) (hwe : (e.1 % L.block) / 32 ∈ D)
    (hwf : (f.1 % L.block) / 32 ∈ D)
    (hordinal : ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    Witness L X (.thread e) f := by
  obtain ⟨key, ic, hke, hkf, hic⟩ := D_same_key hX hS hD hcard hnD hcD hsame he hf hpassed hwe
    hwf hordinal
  exact Witness.of_ctaBarCounted hkf hic (CtaBarK.arrival hke) hsame.2.2

/-- **The base-causality form**: what the first thread did before its arrival happens before
what the second thread does after passing its own. -/
theorem D_same_ordinal_baseCausality {g h i j before after pc pc' : Nat} {cnt cnt' : Option Nat}
    (hsame : SameCta L g h) (he : X.IsBarrier (g, i) id cnt pc)
    (hf : X.IsBarrier (h, j) id cnt' pc') (hpassed : j + 1 < (X.tr h).length)
    (hwe : (g % L.block) / 32 ∈ D) (hwf : (h % L.block) / 32 ∈ D)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id)) (hbefore : before < i) (hafter : j < after)
    (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  obtain ⟨key, ic, hke, hkf, -⟩ := D_same_key hX hS hD hcard hnD hcD hsame he hf hpassed hwe hwf
    hordinal
  have hs : CtaBarSync L X (g, before) (h, after) :=
    ⟨hsame, key, i, j, CtaBarK.arrival hke, hkf, hbefore, hafter, hlen⟩
  exact Relation.TransGen.single (Or.inr (Or.inl hs))

end Exec

end
end PTX.NamedBar
