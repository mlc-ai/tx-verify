-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarLedger
public import Lemmas.CtaBarrier.CtaBarrierIdentity

@[expose] public section

/-! # Released named barriers and their synchronization keys

A released generation of a named resource is a completion in the checked history of its
CTA. The release supplies a matching real arrival record for every participant lane that
never exits, including lanes which have not passed their barrier yet
(`released_member_key`). Any arrival reached at the released ordinal then has that
generation's key (`reached_key_of_release`). One passed participant fixes the key of every reached
participant at the same source ordinal (`reached_same_key_of_passed`), which yields memory
synchronization between them through the released barrier (`reached_same_ordinal_baseCausality`).
The participant count is a parameter `n` with `p.card = n`, the participants' thread-count
operand `count` decodes to it (`target L.block count = .ok n`), and the block size is the
launch's `L.block`. -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [hK : Fact K.NoBarArrive]

/-- A release supplies a matching history record for each participant lane that never exits,
including lanes which have not themselves passed their barrier yet. -/
theorem released_member_key (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {c id phase : Nat} (hc : c < L.grid) (hid : id < 16)
    (hd : Released L.block (X.barriers c) id phase)
    (hp : ∀ i, CompletesAt L.block (X.barriers c) i id phase →
      Protocol count p id ((X.barriers c).take (i + 1)))
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32)
    {g : Nat} (hg : g < L.block) (hw : g / 32 ∈ p)
    (hno : ∀ j pc, X.get (c * L.block + g, j) ≠ some ⟨pc, .exit⟩) :
    ∃ (e : EvId) (pc : Nat), e.1 = c * L.block + g ∧ X.IsBarrier e id count pc ∧
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) = phase ∧
      CtaBarK L X e (id + 16 * phase) := by
  obtain ⟨index, r, s, t, hr, hs, ht, hbefore, hafter⟩ := hd
  have hcomplete : CompletesAt L.block (X.barriers c) index id phase :=
    ⟨r, s, t, hr, hs, ht, hbefore, hafter⟩
  have hprot := hp index hcomplete
  have hrun : run L.block {} ((X.barriers c).take (index + 1)) = .ok t := by
    rw [List.take_add_one, hr]
    rw [run_append, hs]
    simp [run, ht, Except.bind]
  have hlive : g ∉ t.exited := by
    intro hm
    obtain ⟨a, ha⟩ := run_exited_mem hrun hm
    obtain ⟨-, hy, pc, hget⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_mem_take ha)
    obtain ⟨y1, y2⟩ := a
    simp only at hy
    subst hy
    exact hno y2 pc hget
  obtain ⟨i, lanes, e, hrec, hmember, hgen⟩ :=
    completed_participant_record (phase := phase) hprot hn hcount hcard hbound hrun
      (by rw [hafter]; omega) hg hw hlive
  have hi : i < index + 1 := by
    have hh := (List.getElem?_eq_some_iff.mp hrec).1
    simp only [List.length_take] at hh
    omega
  have hreal : (X.barriers c)[i]? = some (.arrival id (g / 32) count lanes) := by
    simpa only [List.getElem?_take, ite_eq_left hi] using hrec
  have href : e ∈ (Record.arrival id (g / 32) count lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hmember, rfl⟩
  have hsrc := ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hreal)) (g, e) hmember
  obtain ⟨pc, he⟩ := hsrc.2.2
  replace he := hX.isBarrier_of_arrival hK.out he
  have hthread : e.1 = c * L.block + g := hsrc.2.1
  have hpref : Protocol count p id ((X.barriers c).take i) := by
    have hh : Protocol count p id (((X.barriers c).take (index + 1)).take i ++
        ((X.barriers c).take (index + 1)).drop i) := by simpa using hprot
    have hp' := hh.prefix
    simpa only [List.take_take, Nat.min_eq_left (by omega : i ≤ index + 1)] using hp'
  have hkeySource := source_key hX hn hcount hc hreal href hpref hcard hbound hw
  have hgenFull : GenerationOf L.block (X.barriers c) e id phase := by
    have hh := hgen.append (ys := (X.barriers c).drop (index + 1))
    simpa only [List.take_append_drop] using hh
  have hctae : e.1 / L.block = c := cta_ref_cta hX hc hreal href
  have hge : e.1 < L.threads := by
    rw [hthread]
    exact cta_thread_lt hc hg
  have hkey : CtaBarK L X e (id + 16 * phase) := by
    apply hX.ctaBarK_of_arrival hK.out
    apply CtaBarArrivalK.of_generation hX.ctaBar hge hid
    rw [hctae]
    exact hgenFull
  have heq := CtaBarK.key_unique hX.ctaBar hkeySource hkey
  exact ⟨e, pc, hthread, he, by omega, hkey⟩

/-- A merely reached source arrival has its real key once the group's matching phase was
released by any participant. Passing this source thread is unnecessary. -/
theorem reached_key_of_release (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {e : EvId} {id pc phase : Nat} (hid : id < 16)
    (he : X.IsBarrier e id count pc) (hge : e.1 < L.threads)
    (hw : (e.1 % L.block) / 32 ∈ p)
    (hordinal : ((X.tr e.1).take e.2).countP (Execution.isBarId id) = phase)
    (hd : Released L.block (X.barriers (e.1 / L.block)) id phase)
    (hp : ∀ i, CompletesAt L.block (X.barriers (e.1 / L.block)) i id phase →
      Protocol count p id ((X.barriers (e.1 / L.block)).take (i + 1)))
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) :
    CtaBarK L X e (id + 16 * phase) := by
  have hb := block_pos_of_thread_lt hge
  have hc : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hge
  have hlocal : e.1 % L.block < L.block := Nat.mod_lt _ hb
  set c := e.1 / L.block with hcdef
  by_cases hrec : ∃ (k : Nat) (r : Record EvId), (X.barriers c)[k]? = some r ∧ e ∈ r.refs
  · -- the arrival's record precedes the completion of generation `phase`
    obtain ⟨k, r, hr, href⟩ := hrec
    obtain ⟨index, r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩ := hd
    have hprot := hp index ⟨r0, s0, t0, hr0, hs0, ht0, hbefore, hafter⟩
    have hrun : run L.block {} ((X.barriers c).take (index + 1)) = .ok t0 := by
      rw [List.take_add_one, hr0, run_append, hs0]
      simp [run, ht0, Except.bind]
    obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
    obtain ⟨sk, tk, hsk, htk⟩ := run_at_record hlast hr
    cases r with
    | exit x y =>
      exfalso
      have hy : y = e := by simpa only [Record.refs, List.mem_singleton, eq_comm] using href
      obtain ⟨-, -, pc', hget⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hr)
      rw [hy] at hget
      have h2 : X.get e = some ⟨pc, .bar id count⟩ := he
      rw [h2] at hget
      cases hget
    | arrival id' w cnt lanes =>
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp href
      obtain ⟨hql, hqt, pcq, mq, hqbar⟩ :=
        ((hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hr)) q hq
      have hlane := (perform_arrival_lanes htk).2.1 q hq
      have hqe' : q.2 = e := hqe
      rw [hqe'] at hqbar hqt
      have h2 : X.get e = some ⟨pc, .bar id count⟩ := he
      have h3 : X.get e = some ⟨pcq, .bar id' cnt mq⟩ := hqbar
      rw [h2] at h3
      simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h3
      obtain ⟨-, rfl, hcnt, -⟩ := h3
      subst cnt
      have hql' : q.1 = e.1 % L.block := by
        rw [hqt, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hql]
      have hwq : w = e.1 % L.block / 32 := by rw [← hql', hlane.2.1]
      have hocc := cta_prefix_id_arrival_count (id := id) hX hc hr href hsk hql hqt
        hlane.2.2 rfl
      rw [hordinal, hlane.2.1] at hocc
      have hki : k ≤ index := by
        by_contra hlt
        have hl := hprot.run_ledger hn hcount hcard hbound hrun
        have hlive : q.1 ∉ t0.exited := fun hm => hlane.2.2 (exited_prefix
          (i := index + 1) (j := k) (by omega) (by unfold At; exact hrun) hsk hm)
        have hbal := hl.balance (q.1 / 32) (by rw [hlane.2.1]; exact hwq ▸ hw)
          (warpLive_of_lane hql hlive)
        have hmono : idArrivals ((X.barriers c).take (index + 1)) id (q.1 / 32) ≤
            idArrivals ((X.barriers c).take k) id (q.1 / 32) :=
          (List.take_sublist_take_left (by omega)).countP_le
        rw [hlane.2.1] at hbal hmono
        omega
      have hrk : ((X.barriers c).take (index + 1))[k]? =
          some (.arrival id w count lanes) := by
        rw [List.getElem?_take_of_lt (by omega)]
        exact hr
      have hpw := hprot _ (List.mem_of_getElem? hrk) rfl
      have hpref : Protocol count p id ((X.barriers c).take k) := fun r' hr' =>
        hprot r' ((List.take_sublist_take_left (by omega : k ≤ index + 1)).subset hr')
      have hkey := source_key hX hn hcount hc hr href hpref hcard hbound hpw.1
      rwa [hordinal] at hkey
  · -- no record: the thread ends at this arrival, so it never exits
    have hno : ∀ j pc', X.get (c * L.block + e.1 % L.block, j) ≠ some ⟨pc', .exit⟩ := by
      intro j pc' hj
      have hthr : c * L.block + e.1 % L.block = e.1 := by
        rw [hcdef, Nat.mul_comm]
        exact Nat.div_add_mod e.1 L.block
      rw [hthr] at hj
      have hlast := Execution.exit_last hX hge hj
      have hel := len_of_get he
      have hne : e.2 ≠ j := by
        intro heq
        have h2 : X.get e = some ⟨pc, .bar id count⟩ := he
        have h3 : X.get (e.1, e.2) = some ⟨pc', .exit⟩ := by rw [heq]; exact hj
        rw [h2] at h3
        cases h3
      obtain ⟨key, hkey, -⟩ := ctaBarDone_of_returned hX he (by omega)
      obtain ⟨i, s, warp, count, lanes, g', hi, -, hm, -⟩ := hkey.2.2
      exact hrec ⟨i, _, hi, List.mem_map.mpr ⟨(g', e), hm, rfl⟩⟩
    obtain ⟨f, pc', hthread, hf, hocc, hkey⟩ :=
      released_member_key hX hn hcount hc hid hd hp hcard hbound hlocal hw hno
    have hfg : f.1 = e.1 := by
      have hh := Nat.mod_add_div e.1 L.block
      rw [hcdef, Nat.mul_comm] at hthread
      omega
    have hf' : X.IsBarrier (e.1, f.2) id count pc' := by
      simpa only [← hfg] using hf
    have hocc' : ((X.tr e.1).take f.2).countP (Execution.isBarId id) = phase := by
      simpa only [hfg] using hocc
    have hindex := source_ordinal_unique he hf' (hordinal.trans hocc'.symm)
    have hef : e = f := Prod.ext hfg.symm hindex
    simpa only [← hef] using hkey

/-- One participant passing is enough to identify the keys of all reached participants at
the same actual source ordinal. The other source trace may end at its barrier; it need not
already have returned. -/
theorem reached_same_key_of_passed (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {e f : EvId} {id pc pc' : Nat}
    (hid : id < 16) (hsame : SameCta L e.1 f.1)
    (he : X.IsBarrier e id count pc) (hf : X.IsBarrier f id count pc')
    (hpassed : f.2 + 1 < (X.tr f.1).length)
    (hw : (e.1 % L.block) / 32 ∈ p) (hfproto : PrefixFor L X count p id f)
    (hordinal : ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id))
    (hp : ∀ i, CompletesAt L.block (X.barriers (f.1 / L.block)) i id
        (((X.tr f.1).take f.2).countP (Execution.isBarId id)) →
      Protocol count p id ((X.barriers (f.1 / L.block)).take (i + 1)))
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) :
    ∃ key, CtaBarK L X e key ∧ CtaBarK L X f key := by
  have hkf := passed_key hX hn hcount hf hpassed hfproto hcard hbound
  set k := ((X.tr f.1).take f.2).countP (Execution.isBarId id)
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkeyeq := CtaBarK.key_unique hX.ctaBar hkey hkf
  rw [hkeyeq] at hdone
  have hmod : (id + 16 * k) % 16 = id := by omega
  have hdiv : (id + 16 * k) / 16 = k := by omega
  change Released L.block (X.barriers (f.1 / L.block)) ((id + 16 * k) % 16)
    ((id + 16 * k) / 16) at hdone
  rw [hmod, hdiv] at hdone
  have hcta : e.1 / L.block = f.1 / L.block := hsame.2.2
  have hd : Released L.block (X.barriers (e.1 / L.block)) id k := by
    rw [hcta]
    exact hdone
  have hp' : ∀ i, CompletesAt L.block (X.barriers (e.1 / L.block)) i id k →
      Protocol count p id ((X.barriers (e.1 / L.block)).take (i + 1)) := by
    rw [hcta]
    exact hp
  have hke := reached_key_of_release hX hn hcount hid he hsame.1 hw hordinal hd hp' hcard hbound
  exact ⟨id + 16 * k, hke, hkf⟩

/-- Memory ordering through a released named barrier. A reached arrival of one CTA-local
thread and a passed arrival of another thread in the same CTA, at equal source ordinals,
order the accesses before the first arrival before the accesses after the second. The
first thread's trace may end at its own barrier arrival. The caller supplies no key,
phase, or desired-resource identity hypothesis. -/
theorem reached_same_ordinal_baseCausality (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : target L.block count = .ok n)
    {p : Finset Nat} {g h i j before after id pc pc' : Nat}
    (hid : id < 16) (hsame : SameCta L g h)
    (he : X.IsBarrier (g, i) id count pc)
    (hf : X.IsBarrier (h, j) id count pc')
    (hpassed : j + 1 < (X.tr h).length) (hw : (g % L.block) / 32 ∈ p)
    (hfproto : PrefixFor L X count p id (h, j))
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hp : ∀ idx, CompletesAt L.block (X.barriers (h / L.block)) idx id
        (((X.tr h).take j).countP (Execution.isBarId id)) →
      Protocol count p id ((X.barriers (h / L.block)).take (idx + 1)))
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32)
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  obtain ⟨key, hke, hkf⟩ := reached_same_key_of_passed hX hn hcount hid hsame he hf hpassed hw
    hfproto hordinal hp hcard hbound
  have hs : CtaBarSync L X (g, before) (h, after) :=
    ⟨hsame, key, i, j, CtaBarK.arrival hke, hkf, hbefore, hafter, hlen⟩
  exact Relation.TransGen.single (Or.inr (Or.inl hs))

end
end PTX.NamedBar
