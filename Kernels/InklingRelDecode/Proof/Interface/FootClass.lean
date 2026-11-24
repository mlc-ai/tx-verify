-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FootAudit
public import Kernels.InklingRelDecode.Proof.Interface.FootTrack

@[expose] public section

/-!
# The shared writes of a tracked thread, by footprint

`TWrite Q L g s a bs` says what a shared write event `⟨pc, .wr a bs⟩` is, given the abstract state
`s` of thread `g` before it. There are seven kinds, one per writing site:

* `stq`: one of the eight query stores, four bytes inside the query tile
  `[sharedBase + 196608, sharedBase + 212992)`;
* `st8`: the role table `0x01000202` at `sharedBase + 213336`;
* `st9_0`, `st9_1`: the words `num_pre`, `num_iters` at `sharedBase + 212992` and `+ 212996`, with
  the value the prologue's registers hold (`ProA.numPreW`, `numItersW`);
* `store10`: the softmax region's scratch word at `sharedBase + 212992 + 4 (warp % 4)`;
* `allocWr`: the allocation's store of its address, four bytes of `b32 col` at `sharedBase`;
* `stTab`: the role table `0x03030303` at `sharedBase + 213336`.

`thread_write_class` is the statement for a thread whose machine tracked through the write
(`TT`), from the soundness of the machines and `Pre`: nothing else of the execution is used. Every
footprint is in the thread's own CTA.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- `storeValue 32` of a 32-bit word is the word. -/
theorem storeValue_b32 (x : Nat) : storeValue 32 (b32 x) = .ok (b32 x) :=
  storeValue_of_bytes (by rfl)

/-- **What a shared write is, from the state of its thread.** -/
inductive TWrite (Q : Params) (L : Launch) (g : Nat) : TSt → Acc → List Byte → Prop
  | stq {d : ProA.D} {i x : Nat} {a : Acc} {bs : List Byte} (hi : i < 32)
      (hs : d.site = ProA.stqSite i) (hl : a.loc = ⟨.shared, g / L.block, x⟩) (hz : a.size = 4)
      (h1 : L.sharedBase + 196608 ≤ x) (h2 : x + 4 ≤ L.sharedBase + 212992) :
      TWrite Q L g (.d (.pro d)) a bs
  | st8 {d : ProA.D} {a : Acc} {bs : List Byte} (hs : d.site = .st8)
      (ha : a = EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
      (hb : bs = (b32 16777730).toBytes) : TWrite Q L g (.d (.pro d)) a bs
  | st9_0 {d : ProA.D} {a : Acc} {bs : List Byte} (hs : d.site = .st9_0)
      (ha : a = EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 212992) % 2 ^ 32⟩)
      (hb : ∃ v, storeValue 32 (ProA.numPreW L g d.dt) = .ok v ∧ bs = v.toBytes) :
      TWrite Q L g (.d (.pro d)) a bs
  | st9_1 {d : ProA.D} {a : Acc} {bs : List Byte} (hs : d.site = .st9_1)
      (ha : a = EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 212992) % 2 ^ 32 + 4⟩ 1)
      (hb : ∃ v, storeValue 32 (ProA.numItersW L g d.dt) = .ok v ∧ bs = v.toBytes) :
      TWrite Q L g (.d (.pro d)) a bs
  | store10 {d : Sm.D} {a : Acc} {bs : List Byte} (hs : d.site = .store10)
      (ha : a = EvD.wordAcc ⟨.shared, g / L.block,
        L.sharedBase + 212992 + g % L.block / 32 % 4 * 4⟩) :
      TWrite Q L g (.d (.sm d)) a bs
  | allocWr {d : DStart.D} {a : Acc} {bs : List Byte} (hs : d.site = .allocWr)
      (ha : a = { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 })
      (hb : ∃ col, col < 2 ^ 16 ∧ bs = (b32 col).toBytes) : TWrite Q L g (.d (.dstart d)) a bs
  | stTab {d : Epi.D} {a : Acc} {bs : List Byte} (hs : d.site = .stTab)
      (ha : a = EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
      (hb : bs = (b32 50529027).toBytes) : TWrite Q L g (.d (.epi d)) a bs

theorem fired_dstart {g : Nat} {d : DStart.D} {e : Event} {o : Option TState}
    (h : (threadCode L g Q).toMachine.Fired (some (.d (.dstart d))) e o) :
    DStart.Fired L g Q d e o := by
  obtain ⟨t, ⟨ha, hi⟩, hf⟩ := h
  exact DStart.Fired_of_machine ⟨t, ⟨ha, hi.2.1⟩, hf⟩

/-- **A shared write of a thread tracked through it is one of the seven kinds.** -/
theorem thread_write_class (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) {s : TSt}
    (hσ : St Q L X g k = some (some s)) (hsp : a.loc.space = .shared) :
    TWrite Q L g s a bs := by
  have hk : (⟨pc, .wr a bs⟩ : Event).kind = .wr a bs := rfl
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hpw : TSt.pc s ∈ writePcs ∨ TSt.pc s ∈ sharedDirectPcs := write_pc_shared hc hf hk hsp
  have he' : (X.tr g)[k]? = some ⟨pc, .wr a bs⟩ := he
  obtain ⟨o', hF⟩ := (Frame.trace hS hX hg).fired_at he' hσ
  obtain ⟨u, rfl⟩ := fired_some hF hk
  have hr := treach_stateAt hpre hg hσ
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hSh := ProA.sharedOk_of_pre hpre
  cases s with
  | w s =>
    rcases hpw with h | h
    · exact absurd h (worker_state_notWrite s)
    · exact absurd h (worker_state_notDirect s)
  | d s =>
    cases s with
    | dstart d =>
      rcases hpw with h | h
      · exact absurd h (dstart_pc_notWrite d.site)
      · rcases dstart_pc_direct d.site h with hs | hs
        · -- the allocation's request is not a write event
          exfalso
          have := DStart.shape_alloc hb hSh (fired_dstart hF) hs
          simp only [Event.mk.injEq] at this
          cases this.2
        · obtain ⟨col, hcol, he2⟩ := DStart.shape_allocWr hb hSh (fired_dstart hF) hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, h3⟩ := he2
          exact .allocWr hs h2 ⟨col, hcol, h3⟩
    | pro d =>
      have hd := hr.1
      have hFp := fired_pro hF
      have ht : ProA.tidOf L g < 128 := hd
      have hsb : ProA.SbRoom L := by
        have := hpre.sharedRange
        unfold sharedBytes at this
        unfold ProA.SbRoom
        omega
      rcases hpw with h | h
      · rcases pro_write_site d.site h with hs | hs | hs
        · obtain ⟨v, hv, he2⟩ := ProA.shape_st8 hFp hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, h3⟩ := he2
          rw [storeValue_b32] at hv
          cases hv
          exact .st8 hs h2 h3
        · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_0 hFp hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, h3⟩ := he2
          exact .st9_0 hs h2 ⟨v, hv, h3⟩
        · obtain ⟨v, hv, he2⟩ := ProA.shape_st9_1 hFp hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, h3⟩ := he2
          exact .st9_1 hs h2 ⟨v, hv, h3⟩
      · have hmem := pro_pc_direct d.site h
        obtain ⟨i, hi, hs⟩ : ∃ i, i < 32 ∧ d.site = ProA.stqSite i := by
          simp only [ProA.stqSites, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
              h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
          all_goals first
            | exact ⟨0, by decide, h⟩ | exact ⟨1, by decide, h⟩ | exact ⟨2, by decide, h⟩
            | exact ⟨3, by decide, h⟩ | exact ⟨4, by decide, h⟩ | exact ⟨5, by decide, h⟩
            | exact ⟨6, by decide, h⟩ | exact ⟨7, by decide, h⟩ | exact ⟨8, by decide, h⟩
            | exact ⟨9, by decide, h⟩ | exact ⟨10, by decide, h⟩ | exact ⟨11, by decide, h⟩
            | exact ⟨12, by decide, h⟩ | exact ⟨13, by decide, h⟩ | exact ⟨14, by decide, h⟩
            | exact ⟨15, by decide, h⟩ | exact ⟨16, by decide, h⟩ | exact ⟨17, by decide, h⟩
            | exact ⟨18, by decide, h⟩ | exact ⟨19, by decide, h⟩ | exact ⟨20, by decide, h⟩
            | exact ⟨21, by decide, h⟩ | exact ⟨22, by decide, h⟩ | exact ⟨23, by decide, h⟩
            | exact ⟨24, by decide, h⟩ | exact ⟨25, by decide, h⟩ | exact ⟨26, by decide, h⟩
            | exact ⟨27, by decide, h⟩ | exact ⟨28, by decide, h⟩ | exact ⟨29, by decide, h⟩
            | exact ⟨30, by decide, h⟩ | exact ⟨31, by decide, h⟩
        have hm : i / 4 < 8 := by omega
        have hw : i % 4 < 4 := by omega
        have hi4 : 4 * (i / 4) + i % 4 = i := by omega
        obtain ⟨v, bs', a', hv, he2, hl, hz, h1, h2⟩ :=
          ProA.shape_stq_foot (m := i / 4) (w := i % 4) hm hw ht hsb hFp (by rw [hi4]; exact hs)
        simp only [Event.mk.injEq, Kind.wr.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact .stq hi hs hl hz (by simpa [hl] using h1) (by simpa [hl] using h2)
    | sm d =>
      rcases hpw with h | h
      · exact absurd h (sm_pc_notWrite d.site)
      · have hs := sm_pc_direct d.site h
        obtain ⟨bs', he2⟩ := Sm.shape_store10_foot hSh (fired_sm hF) hs
        simp only [Event.mk.injEq, Kind.wr.injEq] at he2
        obtain ⟨-, h2, -⟩ := he2
        exact .store10 hs h2
    | epi d =>
      rcases hpw with h | h
      · have hFe := fired_epi hF
        rcases epi_write_site d.site h with hs | hs | ⟨j, hs⟩
        · exfalso
          obtain ⟨v, hv, he2⟩ := Epi.shape_stLse_loc hpre hg hr.2 hFe hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, -⟩ := he2
          rw [h2] at hsp
          simp [EvD.wordAcc, lseLoc] at hsp
        · obtain ⟨v, hv, he2⟩ := Epi.shape_stTab hFe hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, h3⟩ := he2
          rw [storeValue_b32] at hv
          cases hv
          exact .stTab hs h2 h3
        · exfalso
          obtain ⟨v, hv, he2⟩ := Epi.shape_stO_loc hpre hg hr.2 hFe hs
          simp only [Event.mk.injEq, Kind.wr.injEq] at he2
          obtain ⟨-, h2, -⟩ := he2
          rw [h2] at hsp
          simp [EvD.wordAcc, oLoc] at hsp
      · exact absurd h (epi_pc_notDirect d.site)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
