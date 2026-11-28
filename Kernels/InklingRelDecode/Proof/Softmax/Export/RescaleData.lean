-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Lib.RescaleWord
public import Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.EpiPrev
import Kernels.InklingRelDecode.Proof.Softmax.Operand
import Kernels.InklingRelDecode.Proof.Common.SoftSite
import Kernels.InklingRelDecode.Proof.Common.Where
import Lemmas.Kernel.Frame
import Kernels.InklingRelDecode.Proof.Common.FollowControl
import Kernels.InklingRelDecode.Proof.Lib.ShuffleOperand
import Kernels.InklingRelDecode.Proof.Softmax.Export.ExitShuffles
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Lib.ShuffleEvent
import Kernels.InklingRelDecode.Proof.Common.Export.PshRecv
import Kernels.InklingRelDecode.Flow.Code.Part035

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow Control

private theorem site_2253 (s : Site) (h : s.pc=2253) : s=.shfl11 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_2255 (s : Site) (h : s.pc=2255) : s=.shfl12 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_2252 (s : Site) (h : s.pc=2252) : s=.ldL := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

set_option maxRecDepth 10000 in
private theorem pred_shfl12 {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.shfl12) :
    d.site=.shfl11 ∧ ∃ m a b c ok, ev.kind=.shfl m a b c dn.held.peer ok ∧
      dn.held.word=d.held.word := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | exact ⟨rfl,_,_,_,_,_,by assumption,rfl⟩

set_option maxRecDepth 10000 in
private theorem pred_shfl11 {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.shfl11) :
    d.site=.ldL ∧ ∃ x bs, ev.kind=.rd x bs ∧ dn.held.word=Lib.loadWord bs := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | exact ⟨rfl,_,_,by assumption,rfl⟩

private theorem word_of (ent : Entry) (L : Launch) (g : Nat) (d : D) :
    valueOf ent L g d 1544=Lib.minWord d.held.word d.held.peer := by simp [valueOf]

private theorem word_1542 (ent : Entry) (L : Launch) (g : Nat) (d : D) :
    valueOf ent L g d 1542=d.held.word := by simp [valueOf]

/-- The second decision shuffle is a butterfly with offset one. -/
public theorem shuffle_2255_shape {Q L m X g k mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨2255,.shfl mode a b c recv ok⟩) : mode=.bfly ∧ b=1 ∧ c=31 := by
  have clean : ∀ f, (Event.mk 2255 (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2255; decide)
    (by show 2255<2331; decide)
  have site : d.site=.shfl12 := site_2255 _ pc.symm
  obtain ⟨_,mode',bval,cval⟩ := operand hX hp get (ev := ⟨2255,.shfl mode a b c recv ok⟩) rfl
    (show d.site.pc=2255 from pc.symm) hs Flow.code_2255
    (fun _ => ⟨_,rfl,rfl⟩)
  exact ⟨mode',bval,cval⟩

/-- The decision's two shuffles: the word read at pc 2252 is the first one's operand, and the
second one sends the minimum of that word and what the first received. -/
public theorem rescale_data {Q L m X g k a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨2255,.shfl .bfly a b c recv ok⟩) :
    ∃ j ac bs p ok₁, k=j+2 ∧ X.get (g,j)=some ⟨2252,.rd ac bs⟩ ∧
      X.get (g,j+1)=some ⟨2253,.shfl .bfly (Lib.loadWord bs) 2 31 p ok₁⟩ ∧
      a=Lib.minWord (Lib.loadWord bs) p ∧ b=1 ∧ c=31 := by
  have clean : ∀ f, (Event.mk 2255 (.shfl .bfly a b c recv ok)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2255; decide)
    (by show 2255<2331; decide)
  have site : d.site=.shfl12 := site_2255 _ pc.symm
  have later : d≠{} := by rintro rfl; exact absurd site (by decide)
  obtain ⟨val,-,bval,cval⟩ := operand hX hp get (ev := ⟨2255,.shfl .bfly a b c recv ok⟩) rfl
    (show d.site.pc=2255 from pc.symm) hs Flow.code_2255 (fun _ => ⟨_,rfl,rfl⟩)
  replace val := val (by decide +kernel)
  rw [word_of] at val
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  obtain ⟨u,old,cnt,ev1,eq1,st1,get1,step1⟩ := soft_prev len later hs
  obtain ⟨osite,m1,a1,b1,c1,ok1,kind1,word1⟩ := pred_shfl12 step1 site
  have clean1 := Frame.noUbBefore_of_get hX get u (by omega) ev1 get1
  have pc1 := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get1 st1 clean1
  have ev1_pc : ev1.pc=2253 := by
    change ev1.pc=old.site.pc at pc1
    rw [osite] at pc1
    exact pc1
  obtain ⟨val1,mode1,b1v,c1v⟩ := operand hX hp get1 kind1
    (show old.site.pc=2253 by rw [osite]; rfl) st1 Flow.code_2253 (fun _ => ⟨_,rfl,rfl⟩)
  replace val1 := val1 (by decide +kernel)
  rw [word_1542] at val1
  have later1 : old≠{} := by rintro rfl; exact absurd osite (by decide)
  obtain ⟨u2,old2,cnt2,ev2,eq2,st2,get2,step2⟩ := soft_prev (by omega) later1 st1
  obtain ⟨osite2,x,bs,kind2,word2⟩ := pred_shfl11 step2 osite
  have clean2 := Frame.noUbBefore_of_get hX get u2 (by omega) ev2 get2
  have pc2 := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get2 st2 clean2
  have ev2_pc : ev2.pc=2252 := by
    change ev2.pc=old2.site.pc at pc2
    rw [osite2] at pc2
    exact pc2
  have e1 : ev1=⟨2253,.shfl .bfly a1 2 31 d.held.peer ok1⟩ := by
    obtain ⟨p1,k1⟩ := ev1
    cases ev1_pc
    cases kind1
    cases mode1
    cases b1v
    cases c1v
    rfl
  have e2 : ev2=⟨2252,.rd x bs⟩ := by
    obtain ⟨p2,k2⟩ := ev2
    cases ev2_pc
    cases kind2
    rfl
  have wd : a1=Lib.loadWord bs := val1.trans word2
  refine ⟨u2,x,bs,d.held.peer,ok1,by omega,e2 ▸ get2,?_,?_,bval,cval⟩
  · rw [wd] at e1
    have : u2+1=u := by omega
    rw [this]
    exact e1 ▸ get1
  · rw [val,word1,word2]

private theorem late_site (s : Site)
    (h : s.pc=1261 ∨ s.pc=1838 ∨ s.pc=2242 ∨ s.pc=2244 ∨ s.pc=2246 ∨ s.pc=2248 ∨ s.pc=2253 ∨
      s.pc=2255 ∨ s.pc=2234) :
    s=.shfl4 ∨ s=.shfl5 ∨ s=.shfl7 ∨ s=.shfl8 ∨ s=.shfl9 ∨ s=.shfl10 ∨ s=.shfl11 ∨
      s=.shfl12 ∨ s=.shfl6 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- No data lane of the warp has exited before the rescale decision's shuffles of a lane that
has not: the decision runs in a loop round below the launch's trip count, and a lane exits only
after the last round. -/
public theorem decision_not_exited {Q L m X g k h n mode a b c recv ok pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩)
    (late : pc=1838 ∨ pc=2242 ∨ pc=2244 ∨ pc=2246 ∨ pc=2248 ∨ pc=2253 ∨ pc=2255 ∨ pc=2234)
    (count : ((X.tr g).take k).countP Execution.isShfl=n)
    (lh : h%L.block<128) (cta : h/L.block=g/L.block) : ¬ ShflExited X h n := by
  rintro ⟨v,pc',exit,low⟩
  obtain ⟨total,-⟩ := exit_shuffles hp hX exit lh
  rw [cta] at total
  have clean : ∀ f, (Event.mk pc (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX get
  obtain ⟨w,ent,d,cnt,hs,at_pc⟩ := at_site hp hX get clean (by show 574<pc; omega)
    (by show pc<2331; omega)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have ord := shfl_ordinal hp hX len hs nu
  have limit := reached_limit hp hX hg len hs
  have inv := reached_table hf hg nu hs
  have site := late_site d.site (by rw [←at_pc]; exact Or.inr late)
  have q : Control.Inv ent (g%L.block) d := inv.1.1
  have below : d.i<ent.limit := by
    rcases site with h|h|h|h|h|h|h|h|h <;> exact q.loop (by rw [h]; nofun) (by rw [h]; nofun)
      (by rw [h]; nofun) (fun _ => by rw [h]; nofun)
  have cnt_eq : cnt .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
  have prev := shfl_previous hp hX len hs nu
  simp only [shflCount] at ord
  rw [limit] at below
  have small : (1≤shflInRound d.site d.i ∧ shflInRound d.site d.i≤2) ∨
      (shflInRound d.site d.i≤8 ∧ 0<d.i) ∨ shflInRound d.site d.i=0 := by
    rcases site with h|h|h|h|h|h|h|h|h <;>
      first
      | (simp [h, shflInRound]; done)
      | exact .inr (.inl ⟨by simp [h, shflInRound], prev (by rw [h]; rfl)⟩)
  have step : Lib.shflBase d.i+shflInRound d.site d.i<Lib.shflBase (d.i+1) := by
    unfold Lib.shflBase
    split <;> split <;> omega
  have mono : Lib.shflBase (d.i+1)≤Lib.shflBase (Lib.blocksOf Q L (g/L.block)) := by
    unfold Lib.shflBase
    split <;> split <;> omega
  omega

private theorem shuffle_site (s : Site) (h : s.pc ∈ Lib.shflPcs) : s.isShuffle=true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem prologue_shuffle (s : Prologue.Site) (h : s.pc ∈ Lib.shflPcs) :
    s.isShuffle=true := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem prologue_psh (s : Prologue.Site) (h : s.isShuffle=true) :
    s.pc ∈ [202,244,286] := by
  cases s <;> simp [Prologue.Site.isShuffle] at h
  rename_i b
  fin_cases b <;> decide +kernel

private theorem prologue_position (p : Nat) (s : Prologue.Site) (h : s.isShuffle=true) :
    Prologue.shflPosition p s≤2 := by
  cases s <;> simp [Prologue.Site.isShuffle] at h
  rename_i b
  have := b.isLt
  simp only [Prologue.shflPosition]
  omega

private theorem shuffle_unique {sx sq : Site} {i i' : Nat}
    (dec : sx=.shfl4 ∨ sx=.shfl5 ∨ sx=.shfl7 ∨ sx=.shfl8 ∨ sx=.shfl9 ∨ sx=.shfl10 ∨
      sx=.shfl11 ∨ sx=.shfl12 ∨ sx=.shfl6)
    (pos : needsPrevious sx=true → 0 < i) (pos' : needsPrevious sq=true → 0 < i')
    (shuffle : sq.isShuffle=true)
    (same : Lib.shflBase i' + shflInRound sq i' = Lib.shflBase i + shflInRound sx i) :
    sq = sx := by
  rcases dec with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> cases sq <;>
    simp [Site.isShuffle] at shuffle <;>
    simp only [shflInRound,Lib.shflBase] at same <;> split at same <;> split at same <;>
    first | rfl | (exfalso; omega) | (exfalso; have := pos' rfl; omega) |
      (exfalso; have := pos rfl; omega)

set_option maxRecDepth 10000 in
/-- The partner of a broadcast, butterfly or decision shuffle, with the same shuffle count, is a
shuffle of the same site or a prologue broadcast: a data lane's `n`-th shuffle is at a site fixed
by `n`. -/
public theorem partner_site {Q L m X g k q j pc pc' mode a b c recv ok mode' a' b' c' recv' ok'}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩)
    (late : pc=1261 ∨ pc=1838 ∨ pc=2242 ∨ pc=2244 ∨ pc=2246 ∨ pc=2248 ∨ pc=2253 ∨ pc=2255 ∨
      pc=2234)
    (low : q%L.block<128) (cta : q/L.block=g/L.block)
    (get' : X.get (q,j)=some ⟨pc',.shfl mode' a' b' c' recv' ok'⟩)
    (count : ((X.tr q).take j).countP Execution.isShfl=
      ((X.tr g).take k).countP Execution.isShfl) : pc'=pc ∨ pc'∈[202,244,286] := by
  have clean : ∀ f, (Event.mk pc (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  have hg := Frame.lt_of_get hX get
  obtain ⟨w,ent,d,cnt,hs,at_pc⟩ := at_site hp hX get clean (by show 574<pc; omega)
    (by show pc<2331; omega)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  have nu := Frame.noUbBefore_of_get hX get
  have ord := shfl_ordinal hp hX len hs nu
  have limit := reached_limit hp hX hg len hs
  have inv := reached_table hf hg nu hs
  have site := late_site d.site (by rw [←at_pc]; exact late)
  have prev := shfl_previous hp hX len hs nu
  have inv0 : Control.Inv ent (g%L.block) d := inv.1.1
  have below : d.i<ent.limit := by
    rcases site with h|h|h|h|h|h|h|h|h <;> exact inv0.loop (by rw [h]; nofun) (by rw [h]; nofun)
      (by rw [h]; nofun) (fun _ => by rw [h]; nofun)
  have cnt_eq : cnt .shfl=((X.tr g).take k).countP Execution.isShfl := fcount hs _
  simp only [shflCount] at ord
  rw [limit] at below
  have dsite := site
  have big : 1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase d.i≤
      ((X.tr g).take k).countP Execution.isShfl := by
    rw [←cnt_eq,ord]
    simp only [shflInRound]
    omega
  have up : ((X.tr g).take k).countP Execution.isShfl≤
      1+Iface.preloadCount Q L (g/L.block)+Lib.shflBase d.i+shflInRound d.site d.i := by
    rw [←cnt_eq,ord]
    omega
  have small : (1≤shflInRound d.site d.i ∧ shflInRound d.site d.i≤2) ∨
      (shflInRound d.site d.i≤8 ∧ 0<d.i) ∨ shflInRound d.site d.i=0 := by
    rcases site with h|h|h|h|h|h|h|h|h <;>
      first
      | (simp [h, shflInRound]; done)
      | exact .inr (.inl ⟨by simp [h, shflInRound], prev (by rw [h]; rfl)⟩)
  have step : Lib.shflBase d.i+shflInRound d.site d.i<Lib.shflBase (d.i+1) := by
    unfold Lib.shflBase
    split <;> split <;> omega
  have base : 0<d.i → 3≤Lib.shflBase d.i := by
    unfold Lib.shflBase
    split <;> omega
  have mono : Lib.shflBase (d.i+1)≤Lib.shflBase (Lib.blocksOf Q L (g/L.block)) := by
    unfold Lib.shflBase
    split <;> split <;> omega
  have hq := Frame.lt_of_get hX get'
  have clean' : ∀ f, (Event.mk pc' (.shfl mode' a' b' c' recv' ok')).kind≠.ub f := fun _ => nofun
  have nu2 : ∀ pc f, (Event.mk pc' (.shfl mode' a' b' c' recv' ok'))≠⟨pc,.ub f⟩ :=
    fun _ f eq => clean' f (congrArg Event.kind eq)
  obtain ⟨s,hs',_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX get' nu2 ⟨control_tracked hp hX q j hq,fun _ _ => trivial⟩
  have loc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX get' hs' clean'
  have len' := (List.getElem?_eq_some_iff.mp get').1.le
  have nuq := Frame.noUbBefore_of_get hX get'
  have listed : pc'∈Lib.shflPcs := by
    have := Lib.shfl_event hX get' (fun _ => nofun)
    simpa [Execution.isShfl] using this
  have pre : Iface.preloadCount Q L (q/L.block)=Iface.preloadCount Q L (g/L.block) := by
    rw [cta]
  obtain ⟨s,n⟩ := s
  rcases s with s|⟨r,d'⟩
  · have one := shfl_startup_exact hp hX len' hs' nuq
    have two : n .shfl=((X.tr g).take k).countP Execution.isShfl :=
      (fcount hs' Cls.shfl).trans count
    obtain ⟨st,tt,xx,ww⟩ := s
    cases st with
    | enter r =>
      exfalso
      change pc'=Startup.Entry.pc r at loc
      subst loc
      cases r <;> revert listed <;> decide
    | _ => (dsimp only at one; omega)
  rcases r with r|r
  swap
  · exfalso
    change pc'=Startup.Entry.pc r at loc
    subst loc
    cases r <;> revert listed <;> decide
  cases r with
  | dispatch =>
    obtain ⟨wide,_⟩ := worker_warp hp hX len' hs'
    change 128≤q%L.block at wide
    omega
  | prologue w' =>
    rcases d' with d'|⟨ent',d'|⟨⟨⟩,d'⟩⟩
    · have shuf : d'.site.isShuffle=true := prologue_shuffle _ (by
        change pc'=_ at loc; rw [loc] at listed; exact listed)
      have hpc' : pc'∈[202,244,286] := by
        change pc'=d'.site.pc at loc
        rw [loc]
        exact prologue_psh _ shuf
      exact Or.inr hpc'
    · have ordq : n .shfl=1+Iface.preloadCount Q L (q/L.block)+Softmax.shflCount d' :=
        shfl_ordinal hp hX len' hs' nuq
      have lim := reached_limit hp hX hq len' hs'
      have shuf : d'.site.isShuffle=true := shuffle_site _ (by
        change pc'=_ at loc; rw [loc] at listed; exact listed)
      have two : n .shfl=((X.tr g).take k).countP Execution.isShfl :=
        (fcount hs' Cls.shfl).trans count
      simp only [shflCount] at ordq
      rw [pre] at ordq
      change pc'=d'.site.pc at loc
      have same : Lib.shflBase d'.i+shflInRound d'.site d'.i=
          Lib.shflBase d.i+shflInRound d.site d.i := by omega
      have eq := shuffle_unique dsite prev (shfl_previous hp hX len' hs' nuq) shuf same
      exact Or.inl (by rw [loc,eq,←at_pc])
    · have bound : 1+Iface.preloadCount Q L (q/L.block)+Lib.shflBase ent'.limit≤n .shfl :=
        shfl_epilogue hp hX len' hs' nuq
      have lim := reached_limit hp hX hq len' hs'
      have two : n .shfl=((X.tr g).take k).countP Execution.isShfl :=
        (fcount hs' Cls.shfl).trans count
      rw [lim,cta] at bound
      omega

/-- The partner of a butterfly or decision shuffle is a shuffle of the same site. -/
public theorem partner_pc_late {Q L m X g k q j pc pc' mode a b c recv ok mode' a' b' c' recv' ok'}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩)
    (late : pc=1838 ∨ pc=2242 ∨ pc=2244 ∨ pc=2246 ∨ pc=2248 ∨ pc=2253 ∨ pc=2255 ∨ pc=2234)
    (low : q%L.block<128) (cta : q/L.block=g/L.block)
    (get' : X.get (q,j)=some ⟨pc',.shfl mode' a' b' c' recv' ok'⟩) (bf : mode'=.bfly)
    (count : ((X.tr q).take j).countP Execution.isShfl=
      ((X.tr g).take k).countP Execution.isShfl) : pc'=pc := by
  rcases partner_site hp hX hf get (Or.inr late) low cta get' count with h|h
  · exact h
  · obtain ⟨_,_,e⟩ := Export.psh_event hp hX get' (fun _ => nofun) h
    have := congrArg Event.kind e
    simp only at this
    cases this
    cases bf

/-- The partner of a rescale-decision shuffle is a shuffle of the same site. -/
public theorem partner_pc {Q L m X g k q j pc pc' mode a b c recv ok mode' a' b' c' recv' ok'}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (get : X.get (g,k)=some ⟨pc,.shfl mode a b c recv ok⟩) (decision : pc=2253 ∨ pc=2255)
    (low : q%L.block<128) (cta : q/L.block=g/L.block)
    (get' : X.get (q,j)=some ⟨pc',.shfl mode' a' b' c' recv' ok'⟩) (bf : mode'=.bfly)
    (count : ((X.tr q).take j).countP Execution.isShfl=
      ((X.tr g).take k).countP Execution.isShfl) : pc'=pc :=
  partner_pc_late hp hX hf get (by omega) low cta get' bf count

/-- The first decision shuffle sends the word loaded just before it. -/
public theorem word_data {Q L m X g k mode a b c recv ok} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (get : X.get (g,k)=some ⟨2253,.shfl mode a b c recv ok⟩) :
    ∃ j ac bs, k=j+1 ∧ X.get (g,j)=some ⟨2252,.rd ac bs⟩ ∧ a=Lib.loadWord bs ∧
      mode=.bfly ∧ b=2 ∧ c=31 := by
  have clean : ∀ f, (Event.mk 2253 (.shfl mode a b c recv ok)).kind≠.ub f := fun _ => nofun
  obtain ⟨w,ent,d,n,hs,pc⟩ := at_site hp hX get clean (by show 574<2253; decide)
    (by show 2253<2331; decide)
  have site : d.site=.shfl11 := site_2253 _ pc.symm
  obtain ⟨val,mval,bval,cval⟩ := operand hX hp get (ev := ⟨2253,.shfl mode a b c recv ok⟩) rfl
    (show d.site.pc=2253 from pc.symm) hs Flow.code_2253 (fun _ => ⟨_,rfl,rfl⟩)
  replace val := val (by decide +kernel)
  rw [word_1542] at val
  have later : d≠{} := by rintro rfl; exact absurd site (by decide)
  have len := (List.getElem?_eq_some_iff.mp get).1.le
  obtain ⟨u,old,cnt,ev,eq,st,got,step⟩ := soft_prev len later hs
  obtain ⟨osite,x,bs,kind,word⟩ := pred_shfl11 step site
  have clean2 := Frame.noUbBefore_of_get hX get u (by omega) ev got
  have pc2 := Frame.event_pcU (fun g hg => thread_sound hp hg) hX got st clean2
  have ev_pc : ev.pc=2252 := by
    change ev.pc=old.site.pc at pc2
    rw [osite] at pc2
    exact pc2
  have e : ev=⟨2252,.rd x bs⟩ := by
    obtain ⟨p2,k2⟩ := ev
    cases ev_pc
    cases kind
    rfl
  exact ⟨u,x,bs,by omega,e ▸ got,val.trans word,mval,bval,cval⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
