-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarSync

@[expose] public section

/-! # A named barrier from the sources of its arrivals

A kernel describes a named barrier `id` by its group (`Shape`): the participant warps `p` of each
CTA, each passing the thread-count operand `count` that decodes to the number of participant
warps; and by the sources of its arrivals (`Sources`): every arrival on `id` of a thread of the
launch, by `bar.sync` or by `bar.arrive`, is a lane of a participant warp passing `count`. Neither
says which participants wait, so a group may mix both forms.

From the sources alone, every arrival record of a CTA's history of `id` is a participant warp's
(`Sources.recorded`), so the history and its prefixes follow the group's protocol
(`Sources.protocol`, `Sources.completed`, `Sources.prefixFor`). For a kernel without `bar.arrive`
the library's generation lemmas then apply with no further kernel fact: the generation of an
arrival is its source ordinal (`Sources.key`), a passed generation is released
(`Sources.passed_released`), a participant lane that never exits has an arrival of every released
generation (`Sources.member_key`), so a passed generation has every participant's arrival of its
ordinal (`Sources.member_arrival`), and two arrivals with the same ordinal, one of them passed,
order what the first thread did before its arrival before what the second does after
(`Sources.same_ordinal_baseCausality`).

A few facts about counting barrier arrivals along a trace close the file (`countP_last`,
`isBarId_form`, `countP_bar_split`). -/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

/-- The group of named barrier `id`: its participant warps `p`, at least one, of a CTA, each
passing the thread-count operand `count` that decodes to their number. -/
structure Shape (L : Launch) (count : Option Nat) (p : Finset Nat) (id : Nat) : Prop where
  pos : 0 < p.card
  target : target L.block count = .ok p.card
  bound : ∀ w ∈ p, w < L.block / 32
  id_lt : id < 16

/-- The sources of the arrivals on named barrier `id`: every arrival, by `bar.sync` or by
`bar.arrive`, of a thread of the launch is a lane of a participant warp of `p` passing the
thread-count operand `count`. -/
def Sources (L : Launch) (X : Execution) (count : Option Nat) (p : Finset Nat) (id : Nat) :
    Prop :=
  ∀ e pc cnt, X.IsBarArrival e id cnt pc → e.1 < L.threads →
    (e.1 % L.block) / 32 ∈ p ∧ cnt = count

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {count : Option Nat} {p : Finset Nat} {id : Nat}

/-- A `bar.sync` arrival is an arrival. -/
theorem Sources.sync (hS : Sources L X count p id) {e : EvId} {pc : Nat} {cnt : Option Nat}
    (he : X.IsBarrier e id cnt pc) (hg : e.1 < L.threads) :
    (e.1 % L.block) / 32 ∈ p ∧ cnt = count :=
  hS e pc cnt ⟨.sync, he⟩ hg

/-- The CTA of a thread of the launch. -/
theorem cta_lt {g : Nat} (hg : g < L.threads) : g / L.block < L.grid :=
  (Nat.div_lt_iff_lt_mul (block_pos_of_thread_lt hg)).mpr hg

/-- **Every arrival record on the barrier is a participant warp's**, with its operand. -/
theorem Sources.recorded (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    {c warp : Nat} {cnt : Option Nat} {lanes : List (Nat × EvId)} (hc : c < L.grid)
    (hr : Record.arrival id warp cnt lanes ∈ X.barriers c) : warp ∈ p ∧ cnt = count := by
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨last, hlast⟩ := (hX.ctaBar.2 c hc).2.2
  obtain ⟨s, t, _, hpf⟩ := run_at_record hlast hi
  obtain ⟨e, he⟩ := perform_ref_exists hpf
  obtain ⟨⟨g, f⟩, hm, -⟩ := List.mem_map.mp he
  obtain ⟨hg, hfg, pc, hbar⟩ := (hX.ctaBar.2 c hc).2.1 _ hr (g, f) hm
  have hwarp : g / 32 = warp := ((perform_arrival_lanes hpf).2.1 (g, f) hm).2.1
  have hfl : f.1 < L.threads := by rw [hfg]; exact cta_thread_lt hc hg
  have hmod : f.1 % L.block = g := by
    rw [hfg, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
  obtain ⟨hw, hcnt⟩ := hS f pc cnt hbar hfl
  rw [hmod, hwarp] at hw
  exact ⟨hw, hcnt⟩

/-- **A CTA's history of the barrier follows the group's protocol.** -/
theorem Sources.protocol (hX : Consistent L K A mem0 X) (hS : Sources L X count p id) {c : Nat}
    (hc : c < L.grid) : Protocol count p id (X.barriers c) := by
  intro r hr
  cases r with
  | arrival other w cnt ls =>
    intro hid
    subst hid
    exact hS.recorded hX hc hr
  | exit _ _ => trivial

/-- Every prefix of a CTA's history of the barrier follows the group's protocol. -/
theorem Sources.completed (hX : Consistent L K A mem0 X) (hS : Sources L X count p id) {c : Nat}
    (hc : c < L.grid) (idx : Nat) : Protocol count p id ((X.barriers c).take idx) :=
  fun r hr => hS.protocol hX hc r (List.mem_of_mem_take hr)

/-- The history before an arrival's record follows the group's protocol, and the record is a
participant warp's. -/
theorem Sources.prefixFor (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    {e : EvId} (hg : e.1 < L.threads) : PrefixFor L X count p id e := by
  have hc := cta_lt hg
  intro index warp cnt lanes hr _
  exact ⟨hS.completed hX hc index, hS.recorded hX hc (List.mem_of_getElem? hr)⟩

section
variable [hK : Fact K.NoBarArrive]

/-- **The generation of an arrival is its source ordinal.** -/
theorem Sources.key (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {e : EvId} {key pc : Nat} {cnt : Option Nat}
    (he : X.IsBarrier e id cnt pc) (hk : CtaBarK L X e key) :
    key = id + 16 * ((X.tr e.1).take e.2).countP (Execution.isBarId id) := by
  have hid : key % 16 = id := by
    obtain ⟨count', pc', he'⟩ := hk.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans he))).2).1
  have hg := hk.1
  have hgen := hk.2.2
  rw [hid] at hgen
  obtain ⟨index, s, warp, cnt', lanes, g, hr, hs, hm, hphase, t, ht'⟩ := hgen
  have href : e ∈ (Record.arrival id warp cnt' lanes).refs :=
    List.mem_map.mpr ⟨(g, e), hm, rfl⟩
  obtain ⟨hprot, hw, hcount⟩ := hS.prefixFor hX hg index warp cnt' lanes hr href
  subst cnt'
  have hk' := source_key hX hG.pos hG.target (cta_lt hg) hr href hprot rfl hG.bound hw
  have hu := CtaBarK.key_unique hX.ctaBar hk hk'
  omega

/-- **A passed generation is released.** -/
theorem Sources.passed_released (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} (hf : X.IsBarrier f id count pc)
    (hpassed : f.2 + 1 < (X.tr f.1).length) :
    Released L.block (X.barriers (f.1 / L.block)) id
      (((X.tr f.1).take f.2).countP (Execution.isBarId id)) := by
  obtain ⟨key, hkey, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hk := hS.key hX hG hf hkey
  subst hk
  have h1 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) % 16 = id := by
    have := hG.id_lt
    omega
  have h2 : (id + 16 * ((X.tr f.1).take f.2).countP (Execution.isBarId id)) / 16 =
      ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
    have := hG.id_lt
    omega
  unfold CtaBarDone at hdone
  rw [h1, h2] at hdone
  exact hdone

/-- **A participant lane that never exits has an arrival of every released generation**, of
that generation's key. -/
theorem Sources.member_key (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {c phase : Nat} (hc : c < L.grid)
    (hd : Released L.block (X.barriers c) id phase) {g : Nat} (hg : g < L.block) (hw : g / 32 ∈ p)
    (hno : ∀ j pc, X.get (c * L.block + g, j) ≠ some ⟨pc, .exit⟩) :
    ∃ (e : EvId) (pc : Nat), e.1 = c * L.block + g ∧ X.IsBarrier e id count pc ∧
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) = phase ∧
      CtaBarK L X e (id + 16 * phase) :=
  released_member_key hX hG.pos hG.target hc hG.id_lt hd
    (fun i _ => hS.completed hX hc (i + 1)) rfl hG.bound hg hw hno

/-- **A passed generation has every participant's arrival of its ordinal**: a participant lane
of the CTA that never exits has one by the released generation (`member_key`); for a lane that
exits the kernel supplies it (`hexited`). -/
theorem Sources.member_arrival (hX : Consistent L K A mem0 X) (hS : Sources L X count p id)
    (hG : Shape L count p id) {f : EvId} {pc : Nat} (hf : X.IsBarrier f id count pc)
    (hpassed : f.2 + 1 < (X.tr f.1).length) {g : Nat} (hcta : g / L.block = f.1 / L.block)
    (hw : (g % L.block) / 32 ∈ p)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) → ∃ i pc',
      X.IsBarrier (g, i) id count pc' ∧ ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id)) :
    ∃ i pc', X.IsBarrier (g, i) id count pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId id) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId id) := by
  by_cases hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩
  · exact hexited hex
  have hfg : f.1 < L.threads := by
    obtain ⟨key, hk, -⟩ := ctaBarDone_of_returned hX hf hpassed
    exact hk.1
  have hb0 : 0 < L.block := block_pos_of_thread_lt hfg
  have hthr : f.1 / L.block * L.block + g % L.block = g := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod g L.block
  have hno : ∀ j pcx, X.get (f.1 / L.block * L.block + g % L.block, j) ≠ some ⟨pcx, .exit⟩ := by
    rw [hthr]
    exact fun j pcx h => hex ⟨j, pcx, h⟩
  obtain ⟨e, pc', he1, he, hcount, -⟩ := hS.member_key hX hG (cta_lt hfg)
    (hS.passed_released hX hG hf hpassed) (Nat.mod_lt g hb0) hw hno
  have hge : e.1 = g := by rw [he1, hthr]
  obtain ⟨e1, e2⟩ := e
  simp only at hge
  subst hge
  exact ⟨e2, pc', he, hcount⟩

/-- **Two arrivals with the same ordinal synchronize.** A reached arrival of one thread and a
passed arrival of another thread of the same CTA, with the same ordinal: what the first thread
did before its arrival happens before what the second does after passing its own. -/
theorem Sources.same_ordinal_baseCausality (hX : Consistent L K A mem0 X)
    (hS : Sources L X count p id)
    (hG : Shape L count p id) {g h i j before after pc pc' : Nat} (hsame : SameCta L g h)
    (he : X.IsBarrier (g, i) id count pc) (hf : X.IsBarrier (h, j) id count pc')
    (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId id) =
      ((X.tr h).take j).countP (Execution.isBarId id))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  have hh : h < L.threads := hsame.2.1
  exact reached_same_ordinal_baseCausality hX hG.pos hG.target hG.id_lt hsame he hf hpassed
    (hS.sync he hsame.1).1 (hS.prefixFor hX (e := (h, j)) hh) hordinal
    (fun idx _ => hS.completed hX (cta_lt hh) (idx + 1)) rfl hG.bound hbefore hafter hlen

end

/-! ## Counting barrier arrivals along a trace -/

/-- A trace's arrivals on a barrier, with the last event one of them. -/
theorem countP_last {es : List Event} {e : Event} {id : Nat} (hl : es[es.length - 1]? = some e)
    (hb : Execution.isBarId id e = true) :
    es.countP (Execution.isBarId id) =
      (es.take (es.length - 1)).countP (Execution.isBarId id) + 1 := by
  have hlt : es.length - 1 < es.length := (List.getElem?_eq_some_iff.mp hl).1
  conv_lhs => rw [← List.take_append_drop (es.length - 1) es]
  rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega)]
  have he : es[es.length - 1] = e := (List.getElem?_eq_some_iff.mp hl).2
  rw [he]
  simp [List.countP_append, hb]

/-- An arrival event with the barrier's id. -/
theorem isBarId_form {id : Nat} {e : Event} (h : Execution.isBarId id e = true) :
    ∃ pc cnt m, e = ⟨pc, .bar id cnt m⟩ := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> simp [Execution.isBarId] at h
  rename_i id' cnt' m'
  exact ⟨pc, cnt', m', by rw [h]⟩

theorem isBar_of_isBarId {id : Nat} {e : Event} (h : Execution.isBarId id e = true) :
    Execution.isBar e = true := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isBar, Execution.isBarId]

theorem id_eq_of_isBarId {a b : Nat} {e : Event} (h : Execution.isBarId a e = true)
    (h' : Execution.isBarId b e = true) : a = b := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Execution.isBarId]

/-- The barrier arrivals of a list that are on one of two barriers are the sum of those on
each. -/
theorem countP_bar_split {a b : Nat} (hne : a ≠ b) : ∀ es : List Event,
    (∀ e ∈ es, Execution.isBar e = true →
      Execution.isBarId a e = true ∨ Execution.isBarId b e = true) →
    es.countP Execution.isBar = es.countP (Execution.isBarId a) + es.countP (Execution.isBarId b)
  | [], _ => rfl
  | e :: es, h => by
    have ih := countP_bar_split hne es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases hbar : Execution.isBar e = true
    · rcases he hbar with ha | hb
      · have hb : ¬ Execution.isBarId b e = true := fun hb => hne (id_eq_of_isBarId ha hb)
        simp [hbar, ha, hb]; omega
      · have ha : ¬ Execution.isBarId a e = true := fun ha => hne (id_eq_of_isBarId ha hb)
        simp [hbar, ha, hb]; omega
    · have ha : ¬ Execution.isBarId a e = true := fun h' => hbar (isBar_of_isBarId h')
      have hb : ¬ Execution.isBarId b e = true := fun h' => hbar (isBar_of_isBarId h')
      simp [hbar, ha, hb]

end
end PTX.NamedBar
