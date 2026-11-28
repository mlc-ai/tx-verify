-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutLit

@[expose] public section

/-! # Run items with two destinations: `mov.b32 {lo, hi}, a`

A proof tool for `Tools/out_gen.py`. `XItem` has one destination (`XItem.fn`) or is a library
item (`OItem`), whose only unpack is the 64-bit `mov.b64 {lo, hi}, a`. `YItem` adds the unpack of
any width (`YItem.unpack w lo hi a`, Core's `mov.b<w> {lo, hi}, a` reading Core's rule), and runs
of `YItem`s are pieces as runs of `XItem`s are (`SegD.outs_litY`, the analogue of
`SegD.outs_lit`): the generator writes a run as `YItem`s when it has such an unpack. An `XItem` is
the `YItem` `.x it`, with the same rule (`YItem.Rule (.x it) = it.Rule`), so the rule terms of a
declaration do not change. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- A run item: an `XItem`, or the unpack of a `w`-bit register into two halves. -/
inductive YItem where
  | x (it : XItem)
  | unpack (w lo hi a : Nat)

namespace YItem

def op : YItem → Op
  | x it => it.op
  | unpack w lo hi a => .move ⟨.unpack, .int .b w, [some lo, some hi], [.reg a]⟩

def reads : YItem → List Nat
  | x it => it.reads
  | unpack _ _ _ a => [a]

def writes : YItem → List Nat
  | x it => it.writes
  | unpack _ lo hi _ => [lo, hi]

def vals (V : Nat → Value) : YItem → List (Nat × Value)
  | x it => it.vals V
  | unpack w lo hi a => [(lo, (splitValue w (V a)).1), (hi, (splitValue w (V a)).2)]

def req (V : Nat → Value) : YItem → Bool
  | x it => it.req V
  | unpack .. => true

def cond (V : Nat → Value) : YItem → Prop
  | x it => it.cond V
  | unpack w _ _ a => (V a).bytes = w / 8 ∧ (splitValue w (V a)).1.bytes = w / 16 ∧
      (splitValue w (V a)).2.bytes = w / 16

variable {A : List Assumption} {L : Launch} {g : Nat}

def Rule (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : YItem → Prop
  | x it => it.Rule A L g t
  | unpack w lo hi a => (unpack w lo hi a).op.rule = some .threadMove ∧
      ∀ a' ∈ A, a'.localRule L g t (unpack w lo hi a).op = none

def upd (V : Nat → Value) (it : YItem) : Nat → Value :=
  (it.vals V).foldl (fun (V : Nat → Value) (p : Nat × Value) => Function.update V p.1 p.2) V

def post (V : Nat → Value) (it : YItem) (t : TState) : TState :=
  PTX.next ((it.vals V).foldl (fun t p => setReg t p.1 p.2) t)

def codeB (K : Kernel) (pc : Nat) (it : YItem) : Bool := OItem.instrB K.code[pc]? it.op

def localB (it : YItem) : Bool := it.op.isLocal

theorem vals_keys (V : Nat → Value) (it : YItem) : (it.vals V).map Prod.fst = it.writes := by
  cases it with
  | x it => exact XItem.vals_keys V it
  | unpack => rfl

/-- **One item**: under its condition the instruction steps to `post`; otherwise it fails. -/
theorem exec (it : YItem) {V : Nat → Value} {t : TState}
    (hS : SegFreePc A t.pc) (hR : it.Rule A L g t)
    (hr : ∀ r ∈ it.reads, t.regs r = some (V r)) (hq : it.req V = true) :
    (it.cond V → execLocalA A L g t it.op = .ok (it.post V t)) ∧
      (¬ it.cond V → ∃ f, execLocalA A L g t it.op = .error f) := by
  cases it with
  | x it => exact it.exec hS hR hr hq
  | unpack w lo hi a =>
    have ha := hr a (by simp [reads])
    have he : execLocalA A L g t (YItem.unpack w lo hi a).op =
        (if (V a).bytes = w / 8 then
          (if (splitValue w (V a)).1.bytes = w / 16 ∧ (splitValue w (V a)).2.bytes = w / 16 then
            .ok (PTX.next (setReg (setReg t lo (splitValue w (V a)).1) hi
              (splitValue w (V a)).2))
          else .error .typeMismatch)
        else .error .typeMismatch) := by
      simp only [Rule, op] at hR
      simp only [op, hS.exec rfl, execLocalRule_of_none hR.2,
        execLocal_move (m := ⟨.unpack, .int .b w, [some lo, some hi], [.reg a]⟩) hR.1, execMove,
        DType.width, readValue, readReg, ha]
      by_cases h8 : (V a).bytes = w / 8 <;>
        by_cases h4 : (splitValue w (V a)).1.bytes = w / 16 ∧
          (splitValue w (V a)).2.bytes = w / 16 <;>
        simp [h8, h4, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨h8, h4⟩ := h
      rw [he]
      simp [h8, h4, post, vals]
    · simp only [cond] at h
      rw [he]
      by_cases h8 : (V a).bytes = w / 8
      · simp only [h8, ↓reduceIte, ite_eq_right (fun h4 => h ⟨h8, h4⟩)]
        exact ⟨_, rfl⟩
      · simp only [h8, ↓reduceIte]
        exact ⟨_, rfl⟩

/-- **The unpack reads Core's rule** where it has one and no assumption has a local rule for
it. -/
theorem unpack_rule {pc w lo hi a : Nat} (hr : (unpack w lo hi a).op.rule = some .threadMove)
    (hn : ∀ s : TState, s.pc = pc → ∀ a' ∈ A, a'.localRule L g s (unpack w lo hi a).op = none) :
    ∀ s : TState, s.pc = pc → (unpack w lo hi a).Rule A L g s :=
  fun s hs => ⟨hr, hn s hs⟩

end YItem

/-! ### Runs of `YItem`s -/

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The condition of a run of `YItem`s. -/
def yCond (V : Nat → Value) : List YItem → Prop
  | [] => True
  | it :: its => it.cond V ∧ yCond (it.upd V) its

def yReq (V : Nat → Value) : List YItem → Bool
  | [] => true
  | it :: its => it.req V && yReq (it.upd V) its

/-- The values after a run of `YItem`s. -/
def yFinal (V : Nat → Value) : List YItem → Nat → Value
  | [] => V
  | it :: its => yFinal (it.upd V) its

def yReadsB (dom : List Nat) : List YItem → Bool
  | [] => true
  | it :: its => it.reads.all (· ∈ dom) && yReadsB (it.writes ++ dom) its

def yCodeB (K : Kernel) : Nat → List YItem → Bool
  | _, [] => true
  | pc, it :: its => it.codeB K pc && yCodeB K (pc + 1) its

def yLocalB : List YItem → Bool
  | [] => true
  | it :: its => it.localB && yLocalB its

def yWrites (items : List YItem) : List Nat := items.flatMap YItem.writes

def YRules (A : List Assumption) (L : Launch) (g : Nat) : Nat → List YItem → Prop
  | _, [] => True
  | pc, it :: its => (SegFreePc A pc ∧ ∀ s : TState, s.pc = pc → it.Rule A L g s) ∧
      YRules A L g (pc + 1) its

/-- **One item**, at the state level: under its condition one local step writes its values
and keeps every register it does not write; otherwise the thread is dead. -/
theorem YItem.step (it : YItem) {V : Nat → Value} {dom : List Nat} {t : TState}
    (hc : it.codeB K t.pc = true) (hf : t.fault = none)
    (hd : ∀ r ∈ dom, t.regs r = some (V r)) (hrd : ∀ r ∈ it.reads, r ∈ dom)
    (hq : it.req V = true) (hl : it.localB = true) (hS : SegFreePc A t.pc)
    (hR : it.Rule A L g t) :
    (it.cond V → run K A L g 1 t = some (it.post V t) ∧ (it.post V t).pc = t.pc + 1 ∧
      (it.post V t).sub = t.sub ∧ (it.post V t).acc = t.acc ∧
      (it.post V t).fault = t.fault ∧
      (∀ r, r ∉ it.writes → (it.post V t).regs r = t.regs r) ∧
      ∀ r ∈ it.writes ++ dom, (it.post V t).regs r = some (it.upd V r)) ∧
    (¬ it.cond V → Machine.Dead (K := K) (A := A) (L := L) (g := g) t) := by
  have hcode := OItem.instrB_eq hc
  have hex := it.exec hS hR (fun r hr => hd r (hrd r hr)) hq
  obtain ⟨h1, h2, h3, h4⟩ := foldl_setReg_skel t (it.vals V)
  have hregs : (it.post V t).regs = (it.vals V).foldl (fun (R : Nat → Option Value)
      (p : Nat × Value) => Function.update R p.1 (some p.2)) t.regs := by
    simp only [YItem.post, PTX.next]
    exact foldl_setReg_regs t (it.vals V)
  refine ⟨fun hc' => ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩, fun hc' => ?_⟩
  · simp only [run, tauStep, tau_of_ok hcode hl hf (hex.1 hc')]
    rfl
  · simp [YItem.post, PTX.next, h1]
  · simp [YItem.post, PTX.next, h2]
  · simp [YItem.post, PTX.next, h3]
  · simp [YItem.post, PTX.next, h4]
  · rw [hregs, foldl_update_other _ (by rw [YItem.vals_keys]; exact hr)]
  · rw [hregs]
    rcases List.mem_append.mp hr with hw | hw
    · exact foldl_update_mem _ (by rw [YItem.vals_keys]; exact hw)
    · exact foldl_update_some _ (hd r hw)
  · obtain ⟨f, he⟩ := hex.2 hc'
    exact dead_of_error hcode hl hf he

/-- **A run of items**: under `yCond` local steps write each register the run writes with its
value after the run and keep every other register; otherwise the thread is dead. -/
theorem yRun : ∀ (items : List YItem) (V : Nat → Value) (dom : List Nat) (t : TState),
    yCodeB K t.pc items = true → t.fault = none → (∀ r ∈ dom, t.regs r = some (V r)) →
    yReadsB dom items = true → yReq V items = true → yLocalB items = true →
    YRules A L g t.pc items →
    (yCond V items → ∃ t', run K A L g items.length t = some t' ∧
      t'.pc = t.pc + items.length ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
      (∀ r, r ∉ yWrites items → t'.regs r = t.regs r) ∧
      ∀ r ∈ yWrites items ++ dom, t'.regs r = some (yFinal V items r)) ∧
    (¬ yCond V items → Machine.Dead (K := K) (A := A) (L := L) (g := g) t)
  | [], V, dom, t, _, _, hd, _, _, _, _ =>
    ⟨fun _ => ⟨t, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      fun r hr => hd r (by simpa [yWrites] using hr)⟩, fun h => absurd trivial h⟩
  | it :: its, V, dom, t, hc, hf, hd, hrd, hq, hl, hR => by
    simp only [yCodeB, Bool.and_eq_true] at hc
    simp only [yLocalB, Bool.and_eq_true] at hl
    simp only [yReadsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrd
    simp only [yReq, Bool.and_eq_true] at hq
    simp only [YRules] at hR
    have hst := it.step hc.1 hf hd hrd.1 hq.1 hl.1 hR.1.1 (hR.1.2 t rfl)
    by_cases hok : it.cond V
    · obtain ⟨hr1, hpc1, hsub1, hacc1, hf1, hfr1, hw1⟩ := hst.1 hok
      have ih := yRun its (it.upd V) (it.writes ++ dom) (it.post V t) (by rw [hpc1]; exact hc.2)
        (hf1.trans hf) hw1 hrd.2 hq.2 hl.2 (by rw [hpc1]; exact hR.2)
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨t', hr', hpc', hsub', hacc', hf', hfr', hw'⟩ := ih.1 h.2
        refine ⟨t', ?_, by rw [hpc', hpc1, List.length_cons]; omega, hsub'.trans hsub1,
          hacc'.trans hacc1, hf'.trans hf1, fun r hr => ?_, fun r hr => ?_⟩
        · rw [List.length_cons, Nat.add_comm]
          exact run_comp hr1 hr'
        · simp only [yWrites, List.flatMap_cons, List.mem_append, not_or] at hr
          rw [hfr' r hr.2, hfr1 r hr.1]
        · refine hw' r ?_
          simp only [yWrites, List.flatMap_cons, List.mem_append] at hr ⊢
          tauto
      · exact dead_of_run hr1 (ih.2 fun h' => h ⟨hok, h'⟩)
    · exact ⟨fun h => absurd h.1 hok, fun _ => hst.2 hok⟩

/-- **A run of items, as a piece**: from facts by `V` to facts by the values after the run,
under `yCond`; otherwise the thread is dead. -/
theorem SegD.youts {pc : Nat} {liveS liveT : List Nat} {V : Nat → Value} {items : List YItem}
    (hcode : yCodeB K pc items = true) (hreads : yReadsB liveS items = true)
    (hreq : yReq V items = true) (hloc : yLocalB items = true) (hR : YRules A L g pc items)
    (hcov : ∀ r ∈ liveT, r ∈ yWrites items ∨ r ∈ liveS) :
    SegD K A L g items.length pc (factsFrom liveS V) (pc + items.length)
      (factsFrom liveT (yFinal V items)) (yCond V items) := by
  intro t h
  have hR' := h.2.2.2.2
  have hrun := yRun items V liveS t (by rw [h.1]; exact hcode) h.2.2.2.1
    (fun r hr => holds_mem hR' (mem_factsFrom hr)) hreads hreq hloc (by rw [h.1]; exact hR)
  refine ⟨fun hc => ?_, hrun.2⟩
  obtain ⟨t', hr, hpc, hsub, hacc, hf, -, hw⟩ := hrun.1 hc
  refine ⟨t', hr, by rw [hpc, h.1], hsub.trans h.2.1, hacc.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr' => hw r ?_⟩
  rcases hcov r hr' with h1 | h1
  · exact List.mem_append_left _ h1
  · exact List.mem_append_right _ h1

/-- Item by item from `pc`: the item's instruction is at its pc, no assumption takes a segment
there, and the assumptions read it as `YItem.Rule` says. -/
def OAtY (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) : Nat → List YItem → Prop
  | _, [] => True
  | pc, it :: its => (it.codeB K pc = true ∧ SegFreePc A pc ∧
      ∀ s : TState, s.pc = pc → it.Rule A L g s) ∧ OAtY K A L g (pc + 1) its

theorem OAtY.code : ∀ {pc : Nat} {items : List YItem}, OAtY K A L g pc items →
    yCodeB K pc items = true
  | _, [], _ => rfl
  | _, _ :: _, h => by simp only [yCodeB, Bool.and_eq_true]; exact ⟨h.1.1, OAtY.code h.2⟩

theorem OAtY.rules : ∀ {pc : Nat} {items : List YItem}, OAtY K A L g pc items →
    YRules A L g pc items
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨⟨h.1.2.1, h.1.2.2⟩, OAtY.rules h.2⟩

/-- The code lemma `K.code[pc]? = some i` gives an item's instruction check when `i` is the
item's instruction (`hb`, by evaluation). -/
theorem YItem.codeB_of {pc : Nat} {i : Instr} {it : YItem} (h : K.code[pc]? = some i)
    (hb : OItem.instrB (some i) it.op = true) : it.codeB K pc = true := by
  simp only [YItem.codeB, h, hb]

/-- **A piece checked against stated values**: from the facts `F`, the items reach the facts `G`
under their condition (otherwise the thread is dead), where `G` is checked by evaluation. -/
theorem SegD.outs_litY {pc : Nat} {F G : List (Nat × Value)} {items : List YItem}
    (hat : OAtY K A L g pc items) (hloc : yLocalB items = true)
    (hreads : yReadsB (F.map Prod.fst) items = true) (hreq : yReq (lookupD F) items = true)
    (hcov : (G.map Prod.fst).all (fun r => (yWrites items).contains r ||
      (F.map Prod.fst).contains r) = true)
    (hG : factsFrom (G.map Prod.fst) (yFinal (lookupD F) items) = G) :
    SegD K A L g items.length pc F (pc + items.length) G (yCond (lookupD F) items) := by
  have h := SegD.youts (K := K) (A := A) (L := L) (g := g) (liveS := F.map Prod.fst)
    (liveT := G.map Prod.fst) hat.code hreads hreq hloc hat.rules (fun r hr => by
      have := List.all_eq_true.mp hcov r hr
      simpa [Bool.or_eq_true] using this)
  rw [hG] at h
  intro t ht
  exact h t ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    holds_lookupD ht.2.2.2.2 (List.all_eq_true.mpr fun r hr => by simpa using hr)⟩


end
end PTX.Flow
