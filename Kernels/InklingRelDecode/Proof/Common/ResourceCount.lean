-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.ResourceSites
import Lemmas.Flow.GlueStep

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Tmem.Pair
noncomputable section

def softEnd {ent L g} : (softCode ent L g).D → Nat
  | .inl _ => 0
  | .inr ⟨_,d⟩ => (decide (d.site.pc=2855)).toNat

def dataEnd {Q L g w} : (dataCode Q L g w).D → Nat
  | .inl _ => 0
  | .inr ⟨_,d⟩ => softEnd d

private theorem soft_enter {ent L g} (s : Softmax.Control.D) :
    softEnd (Code.enter (Softmax.Control.code ent L g) (fun _ : Unit =>
      Epilogue.Control.code (epiEntry ent (g%L.block)) L g) epiExit s)=0 := by
  obtain ⟨s,i,v⟩ := s
  cases s <;> rfl

private theorem data_enter {Q L g w} (s : Prologue.Control.D) :
    dataEnd (Code.enter (Prologue.Control.checkedCode Q L g w)
      (fun e => softCode e L g) (dataExit Q L g w) s)=0 := by
  obtain ⟨s,a,b,c,v⟩ := s
  cases s <;> rfl

private theorem post_next {Q L g w d dn ev} (low : g%L.block<32)
    (move : (dataCode Q L g w).next d ev=some (some dn)) :
    dataEnd dn = dataEnd d + (decide ((dataCode Q L g w).pc d=2851)).toNat := by
  rcases d with d|⟨e,d⟩
  · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some move
    rw [data_enter]
    have bound := d.site.pc_range
    change 0=0+(decide (d.site.pc=2851)).toNat
    rw [decide_eq_false (by omega)]; rfl
  · obtain ⟨sn,sub,rfl⟩ := Code.glue_inr_some move
    rcases d with d|⟨_,s⟩
    · obtain ⟨_,_,rfl⟩ := Code.glue_inl_some sub
      change softEnd _=0+(decide (d.site.pc=2851)).toNat
      rw [soft_enter]
      have off : d.site.pc≠2851 := by
        rcases d.site.pc_range with h|h
        · omega
        · rw [h]; decide
      rw [decide_eq_false off]; rfl
    · obtain ⟨_,step,rfl⟩ := Code.glue_inr_some sub
      exact Epilogue.exit_count low step

def resourcePhase {Q L g} : (thread Q L g).D → Nat
  | (.inl s,_) => Startup.resourceCount (g%L.block) s.site
  | (.inr ⟨.inl (.prologue _),s⟩,_) => 2+dataEnd s
  | _ => 2

private theorem enter_count {Q L g} (low : g%L.block<32) (s : Startup.D) (n : Cls → Nat) :
    resourcePhase (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s,n) =
      Startup.resourceCount (g%L.block) s.site := by
  obtain ⟨s,t,x,w⟩ := s
  cases s <;> try rfl
  rename_i r
  cases r <;> change 2=if 32≤g%L.block then 0 else 2 <;> simp [Nat.not_le_of_lt low]

/-- Exact paired-resource prefix count of warp zero through both data-role handoffs. -/
theorem resource_prefix {Q L m X g k s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hg : g<L.threads)
    (low : g%L.block<32) (bound : k≤(X.tr g).length) (clean : NoUbBefore X g k)
    (hs : stateAt (thread Q L) X g k=some (some s)) :
    tmemOps ((X.tr g).take k)=resourcePhase s := by
  induction k generalizing s with
  | zero =>
    rw [stateAt_zero] at hs
    cases hs
    rw [show resourcePhase (thread Q L g).init=0 from
      (enter_count low ..).trans (Startup.resource_init ..)]
    rfl
  | succ j ih =>
    have he := List.getElem?_eq_getElem (l := X.tr g) (i := j) (by omega)
    rw [stateAt_succ he] at hs
    rcases prev : stateAt (thread Q L) X g j with _|_|old <;> rw [prev] at hs <;>
      try solve | cases hs
    have hu := clean j (by omega) _ he
    have nu := noUbBefore_of_get hX he
    have oldCount := ih (by omega) nu prev
    have hi := (reached_table hf hg nu prev).1
    rw [List.take_succ_eq_append_getElem (by omega)]
    simp only [tmemOps,List.countP_append,List.countP_singleton]
    change tmemOps ((X.tr g).take j)+_=_
    rw [oldCount]
    obtain ⟨old,n⟩ := old
    obtain ⟨sn,nn⟩ := s
    obtain ⟨move,_⟩ := Code.counted_next_some hs
    rcases old with d|⟨r,d⟩
    · obtain ⟨dn,go,rfl⟩ := Code.glue_inl_some move
      rw [enter_count low]
      have step := Startup.resource_next hi.1 (start_ev hp hX he prev hu) go
      rw [step]; cases isTmemOp (X.tr g)[j] <;> rfl
    · obtain ⟨dn,step,rfl⟩ := Code.glue_inr_some move
      rcases r with (r|r)
      · cases r with
        | dispatch =>
          have high := (worker_warp hp hX (by omega) prev).1
          omega
        | prologue =>
          have kind := data_resource hp hX he hu prev
          change 2+dataEnd d+(if isTmemOp (X.tr g)[j] then 1 else 0)=2+dataEnd dn
          rw [post_next low step,kind]
          cases decide ((dataCode Q L g _).pc d=2851) <;> simp [Nat.add_assoc]
      · cases step

end
end PTX.Kernels.InklingRelDecode.Proof
