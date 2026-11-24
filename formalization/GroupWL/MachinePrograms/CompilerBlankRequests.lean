import GroupWL.MachinePrograms.CompilerRequests
import GroupWL.MachinePrograms.StackIndexing

/-! Product-domain emission for the indexed blank suffix of a tableau. -/
namespace GroupWL.MachinePrograms.Structured

open AddressedCircuit BinaryAddress BinaryIntervals CircuitDescription

variable {K : Type*} [DecidableEq K]

theorem domainWord_above {d : ℕ} (a : Address d) (h : Fin d) :
    domainWord (aboveDomain a h) = repeatWord [true,true] h.val++[false,true]++
      mapWord (fun b => [!b,b]) ((List.ofFn a).drop (h.val+1)) := by
  induction d with
  | zero => exact Fin.elim0 h
  | succ d ih =>
    refine Fin.cases ?_ (fun h => ?_) h
    · simp only [Fin.val_zero,repeatWord_zero,List.nil_append,List.ofFn_succ,List.drop_succ_cons,List.drop_zero]
      rw [← domainWord_singleton]
      unfold domainWord
      simp only [List.ofFn_succ,List.flatten_cons]
      congr 1
    · have hi := ih (fun i => a i.succ) h
      simp only [domainWord,List.ofFn_succ,List.flatten_cons] at hi ⊢
      simp only [Fin.val_succ,repeatWord_succ,List.drop_succ_cons]
      have h0 : [decide (false ∈ (aboveDomain a h.succ).coordinate 0),
          decide (true ∈ (aboveDomain a h.succ).coordinate 0)] = [true,true] := by
        have hz : (0 : Fin (d+1)) ≠ h.succ := by
          intro he; have := congrArg Fin.val he; simp at this
        simp [aboveDomain,hz]
      rw [h0]
      have htail : (fun i : Fin d => [decide (false ∈ (aboveDomain a h.succ).coordinate i.succ),
          decide (true ∈ (aboveDomain a h.succ).coordinate i.succ)]) =
          (fun i : Fin d => [decide (false ∈ (aboveDomain (fun j => a j.succ) h).coordinate i),
            decide (true ∈ (aboveDomain (fun j => a j.succ) h).coordinate i)]) := by
        funext i
        simp [aboveDomain]
      rw [htail,hi]
      simp [List.append_assoc]

def aboveRepeatRegisters : Fin 4 ↪ Fin 6 := ⟨![1,2,3,5],by decide⟩
def aboveMapRegisters : Fin 4 ↪ Fin 6 := ⟨![0,2,3,5],by decide⟩

/-- Bits, unary index, output, counter, saved prefix, scratch. -/
def emitAboveDomain (reg : Fin 6 ↪ K) : Program K :=
  .seq (repeatEmit (aboveRepeatRegisters.trans reg) [true,true])
    (.seq (emitFixed (reg 2) [false,true])
      (.seq (copy (reg 1) (reg 3) (reg 5))
        (.seq (.push (reg 3) true)
          (.seq (scanPrefix (reg 3) (reg 0) (reg 4))
            (.seq (emitSingletonDomain (aboveMapRegisters.trans reg)) (transfer (reg 4) (reg 0)))))))

theorem emitAboveDomain_runs (S : Store K) (reg : Fin 6 ↪ K) {d : ℕ}
    (a : Address d) (h : Fin d) (ha : S (reg 0) = List.ofFn a)
    (hh : S (reg 1) = unary h.val)
    (hc : S (reg 3) = []) (hp : S (reg 4) = []) (ht : S (reg 5) = []) :
    Writes (reg 2) (emitAboveDomain reg) S (domainWord (aboveDomain a h))
      (40*(d+h.val+1)) := by
  have eqreg (i j : Fin 6) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let A := Function.update S (reg 2) ((repeatWord [true,true] h.val).reverse++S (reg 2))
  have h1 : Runs (repeatEmit (aboveRepeatRegisters.trans reg) [true,true]) S (11*h.val+3) A := by
    simpa [A,aboveRepeatRegisters,Nat.mul_comm] using
      repeatEmit_runs S (aboveRepeatRegisters.trans reg) [true,true] h.val hh hc ht
  let B := Function.update A (reg 2) ([false,true].reverse++A (reg 2))
  have h2 : Runs (emitFixed (reg 2) [false,true]) A 2 B := emitFixed_runs A _ _
  let C := Function.update B (reg 3) (unary h.val)
  have h3 : Runs (copy (reg 1) (reg 3) (reg 5)) B (7*h.val+2) C := by
    simpa [C,B,A,eqreg,hh,hc,unary] using copy_runs B (reg 1) (reg 3) (reg 5)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (by simp [B,A,eqreg,ht])
  let D := Function.update C (reg 3) (unary (h.val+1))
  have h4 : Runs (.push (reg 3) true) C 1 D := by
    simpa [D,C,unary,List.replicate_succ] using Runs.push C (reg 3) true
  let E := Function.update (Function.update (Function.update D (reg 3) [])
    (reg 0) ((List.ofFn a).drop (h.val+1))) (reg 4) ((List.ofFn a).take (h.val+1)).reverse
  have h5 : Runs (scanPrefix (reg 3) (reg 0) (reg 4)) D (4*(h.val+1)+1) E := by
    have hr := scanPrefix_runs D (reg 3) (reg 0) (reg 4)
      (reg.injective.ne (by decide)) (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
      (h.val+1) (by simp [D,unary])
    have hm : min (h.val+1) d = h.val+1 := min_eq_left (by omega)
    convert hr using 1 <;> simp [E,D,C,B,A,eqreg,ha,hp,hm] <;> omega
  let F := Function.update E (reg 2)
    ((mapWord (fun b => [!b,b]) ((List.ofFn a).drop (h.val+1))).reverse++E (reg 2))
  have h6 : Runs (emitSingletonDomain (aboveMapRegisters.trans reg)) E (11*(d-h.val-1)+3) F := by
    have hr := emitMap_runs E (aboveMapRegisters.trans reg) (fun b => [!b,b])
      (by simp [aboveMapRegisters,E,eqreg]) (by simp [aboveMapRegisters,E,D,C,B,A,eqreg,ht])
    rw [singletonMask_length] at hr
    convert hr using 1 <;> simp [emitSingletonDomain,F,aboveMapRegisters,E,eqreg,List.length_drop,Nat.sub_sub] <;> omega
  have h7 := transfer_runs F (reg 4) (reg 0) (reg.injective.ne (by decide))
  have hf4 : F (reg 4) = ((List.ofFn a).take (h.val+1)).reverse := by simp [F,E,eqreg]
  have hf0 : F (reg 0) = (List.ofFn a).drop (h.val+1) := by simp [F,E,eqreg]
  have hfinal : Function.update (Function.update F (reg 4) []) (reg 0)
      ((F (reg 4)).reverse++F (reg 0)) =
      Function.update S (reg 2) ((domainWord (aboveDomain a h)).reverse++S (reg 2)) := by
    rw [hf4,hf0,List.reverse_reverse,List.take_append_drop]
    funext k
    by_cases hk : k = reg 0
    · subst k; simp [eqreg,ha]
    · by_cases hk' : k = reg 2
      · subst k
        simp [F,E,D,C,B,A,eqreg,domainWord_above,List.reverse_append,List.append_assoc]
      · by_cases hk'' : k = reg 4
        · subst k; simp [eqreg,hp]
        · by_cases hk''' : k = reg 3
          · subst k; simp [F,E,eqreg,hc]
          · simp [F,E,D,C,B,A,Function.update_of_ne hk,Function.update_of_ne hk',
              Function.update_of_ne hk'',Function.update_of_ne hk''']
  rw [hfinal,hf4,List.length_reverse,List.length_take,List.length_ofFn,
    min_eq_left (by omega : h.val+1 ≤ d)] at h7
  refine ⟨(11*h.val+3)+(2+((7*h.val+2)+(1+((4*(h.val+1)+1)+
    ((11*(d-h.val-1)+3)+(3*(h.val+1)+1)))))),?_,
    Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 (Runs.seq h5 (Runs.seq h6 h7)))))⟩
  omega

def indexedLookupRegisters : Fin 6 ↪ Fin 7 := ⟨![0,1,3,4,5,6],by decide⟩
def indexedAboveRegisters : Fin 6 ↪ Fin 7 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 7 => x.val) h)⟩
def indexedSingletonRegisters : Fin 4 ↪ Fin 7 := ⟨![0,2,3,5],by decide⟩

def emitIndexedDomain (reg : Fin 7 ↪ K) : Program K :=
  .seq (indexLookup (indexedLookupRegisters.trans reg))
    (.seq (.peek (reg 6) .skip (emitAboveDomain (indexedAboveRegisters.trans reg))
      (emitSingletonDomain (indexedSingletonRegisters.trans reg))) (clear (reg 6)))

theorem emitIndexedDomain_runs (S : Store K) (reg : Fin 7 ↪ K) {d : ℕ}
    (a : Address d) (h : Fin d) (ha : S (reg 0) = List.ofFn a)
    (hh : S (reg 1) = unary h.val)
    (he : ∀ i : Fin 7, 3 ≤ i.val → S (reg i) = []) :
    Writes (reg 2) (emitIndexedDomain reg) S (domainWord (indexedDomain a (some h)))
      (60*(d+h.val+1)) := by
  have eqreg (i j : Fin 7) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  obtain ⟨t,ht,hi⟩ := indexLookup_runs_bound S (indexedLookupRegisters.trans reg) h.val hh
    (he 3 (by decide)) (he 4 (by decide)) (he 5 (by decide))
  let A := Function.update S (reg 6) [a h]
  have hi' : Runs (indexLookup (indexedLookupRegisters.trans reg)) S t A := by
    simpa [A,indexedLookupRegisters,ha,List.getElem?_ofFn,h.isLt] using hi
  have ht' : t ≤ 14*h.val+7 := by
    simpa [indexedLookupRegisters,he 6 (by decide)] using ht
  have hbranch : Writes (reg 2)
      (.peek (reg 6) .skip (emitAboveDomain (indexedAboveRegisters.trans reg))
        (emitSingletonDomain (indexedSingletonRegisters.trans reg))) A
      (domainWord (indexedDomain a (some h))) (40*(d+h.val+1)+1) := by
    cases hb : a h with
    | false =>
      obtain ⟨u,hu,hr⟩ := emitAboveDomain_runs A (indexedAboveRegisters.trans reg) a h
        (by simpa [A,indexedAboveRegisters,eqreg] using ha)
        (by simpa [A,indexedAboveRegisters,eqreg] using hh)
        (by simp [A,indexedAboveRegisters,eqreg,he 3 (by decide)])
        (by simp [A,indexedAboveRegisters,eqreg,he 4 (by decide)])
        (by simp [A,indexedAboveRegisters,eqreg,he 5 (by decide)])
      refine ⟨u+1,by omega,Runs.peek ?_⟩
      simpa [select,A,hb,indexedDomain,indexedAboveRegisters] using hr
    | true =>
      have hr := emitSingletonDomain_runs A (indexedSingletonRegisters.trans reg) a
        (by simpa [A,indexedSingletonRegisters,eqreg] using ha)
        (by simp [A,indexedSingletonRegisters,eqreg,he 3 (by decide)])
        (by simp [A,indexedSingletonRegisters,eqreg,he 5 (by decide)])
      refine ⟨(11*d+3)+1,by omega,Runs.peek ?_⟩
      simpa [select,A,hb,indexedDomain,indexedSingletonRegisters] using hr
  obtain ⟨u,hu,hr⟩ := hbranch
  let B := Function.update A (reg 2) ((domainWord (indexedDomain a (some h))).reverse++A (reg 2))
  have hc := clear_runs B (reg 6)
  have hb6 : B (reg 6) = [a h] := by simp [B,A,eqreg]
  rw [hb6] at hc
  have hfinal : Function.update B (reg 6) [] =
      Function.update S (reg 2) ((domainWord (indexedDomain a (some h))).reverse++S (reg 2)) := by
    funext k
    by_cases hk : k = reg 6
    · subst k; simp [eqreg,he 6 (by decide)]
    · by_cases hk' : k = reg 2
      · subst k; simp [B,A,eqreg]
      · simp [B,A,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at hc
  exact ⟨t+(u+3),by omega,Runs.seq hi' (Runs.seq hr hc)⟩

def blankPositionWord (M : Complexity.Machine) {d : ℕ} (a : Address d)
    (h : Option (Fin d)) : List Bool :=
  codeWord (CellularTableau.Gate.scalar (MachineCircuit.blank M))++
    domainWord (ProductAddress.domain (ProductDomain.singleton (fun _ : Fin d => false))
      (indexedDomain a h))

def blankIndexRegisters : Fin 7 ↪ Fin 8 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)⟩
def blankTimeRegisters : Fin 4 ↪ Fin 8 := ⟨![7,2,3,5],by decide⟩
def blankSingletonRegisters : Fin 4 ↪ Fin 8 := ⟨![0,2,3,5],by decide⟩

def emitBlankRequest (reg : Fin 8 ↪ K) (M : Complexity.Machine) (indexed : Bool) : Program K :=
  .seq (emitFixed (reg 2) (codeWord (CellularTableau.Gate.scalar (MachineCircuit.blank M))))
    (.seq (repeatEmit (blankTimeRegisters.trans reg) [true,false])
      (if indexed then emitIndexedDomain (blankIndexRegisters.trans reg)
       else emitSingletonDomain (blankSingletonRegisters.trans reg)))

theorem emitBlankRequest_some_runs (S : Store K) (reg : Fin 8 ↪ K) (M : Complexity.Machine)
    {d : ℕ} (a : Address d) (h : Fin d) (ha : S (reg 0) = List.ofFn a)
    (hh : S (reg 1) = unary h.val) (hd : S (reg 7) = unary d)
    (he : ∀ i : Fin 8, 3 ≤ i.val → i.val ≤ 6 → S (reg i) = []) :
    Writes (reg 2) (emitBlankRequest reg M true) S (blankPositionWord M a (some h))
      (FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+80*(d+h.val+1)) := by
  have eqreg (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let code := codeWord (CellularTableau.Gate.scalar (MachineCircuit.blank M))
  let A := Function.update S (reg 2) (code.reverse++S (reg 2))
  have htime : Writes (reg 2) (repeatEmit (blankTimeRegisters.trans reg) [true,false]) A
      (repeatWord [true,false] d) (11*d+3) := by
    refine ⟨_,le_rfl,?_⟩
    simpa [blankTimeRegisters,Nat.mul_comm] using repeatEmit_runs A
      (blankTimeRegisters.trans reg) [true,false] d
      (by simpa [blankTimeRegisters,A,eqreg] using hd)
      (by simp [blankTimeRegisters,A,eqreg,he 3 (by decide) (by decide)])
      (by simp [blankTimeRegisters,A,eqreg,he 5 (by decide) (by decide)])
  let B := Function.update A (reg 2) ((repeatWord [true,false] d).reverse++A (reg 2))
  have hbits : Writes (reg 2) (emitIndexedDomain (blankIndexRegisters.trans reg)) B
      (domainWord (indexedDomain a (some h))) (60*(d+h.val+1)) := by
    exact emitIndexedDomain_runs B (blankIndexRegisters.trans reg) a h
      (by simpa [blankIndexRegisters,B,A,eqreg] using ha)
      (by simpa [blankIndexRegisters,B,A,eqreg] using hh)
      (by intro i hi; simp [blankIndexRegisters,B,A,eqreg,
            show (⟨i.val,by omega⟩ : Fin 8) ≠ 2 by intro h; have := congrArg Fin.val h; simp at this; omega,
            he ⟨i.val,by omega⟩ hi (by change i.val ≤ 6; omega)])
  have run := (emitFixed_writes S (reg 2) code).seq (htime.seq hbits)
  have hc : code.length ≤ FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M)) :=
    length_codeWord _
  have run' := run.mono (by omega : code.length+((11*d+3)+60*(d+h.val+1)) ≤
    FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+80*(d+h.val+1))
  simpa [emitBlankRequest,blankPositionWord,domainWord_product,domainWord_constant,code,
    List.append_assoc] using run'

theorem emitBlankRequest_none_runs (S : Store K) (reg : Fin 8 ↪ K) (M : Complexity.Machine)
    {d : ℕ} (a : Address d) (ha : S (reg 0) = List.ofFn a) (hd : S (reg 7) = unary d)
    (hc : S (reg 3) = []) (ht : S (reg 5) = []) :
    Writes (reg 2) (emitBlankRequest reg M false) S (blankPositionWord M a none)
      (FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+22*d+6) := by
  have eqreg (i j : Fin 8) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let code := codeWord (CellularTableau.Gate.scalar (MachineCircuit.blank M))
  let A := Function.update S (reg 2) (code.reverse++S (reg 2))
  have htime : Writes (reg 2) (repeatEmit (blankTimeRegisters.trans reg) [true,false]) A
      (repeatWord [true,false] d) (11*d+3) := by
    refine ⟨_,le_rfl,?_⟩
    simpa [blankTimeRegisters,Nat.mul_comm] using repeatEmit_runs A
      (blankTimeRegisters.trans reg) [true,false] d
      (by simpa [blankTimeRegisters,A,eqreg] using hd)
      (by simp [blankTimeRegisters,A,eqreg,hc]) (by simp [blankTimeRegisters,A,eqreg,ht])
  let B := Function.update A (reg 2) ((repeatWord [true,false] d).reverse++A (reg 2))
  have hbits : Writes (reg 2) (emitSingletonDomain (blankSingletonRegisters.trans reg)) B
      (domainWord (ProductDomain.singleton a)) (11*d+3) := by
    refine ⟨_,le_rfl,?_⟩
    exact emitSingletonDomain_runs B (blankSingletonRegisters.trans reg) a
      (by simpa [blankSingletonRegisters,B,A,eqreg] using ha)
      (by simp [blankSingletonRegisters,B,A,eqreg,hc]) (by simp [blankSingletonRegisters,B,A,eqreg,ht])
  have run := (emitFixed_writes S (reg 2) code).seq (htime.seq hbits)
  have hc : code.length ≤ FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M)) :=
    length_codeWord _
  have run' := run.mono (by omega : code.length+((11*d+3)+(11*d+3)) ≤
    FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+22*d+6)
  simpa [emitBlankRequest,blankPositionWord,indexedDomain,domainWord_product,domainWord_constant,code,
    List.append_assoc] using run'

def blankAt (M : Complexity.Machine) {d : ℕ} (a : Address d) (i : ℕ) : List Bool :=
  blankPositionWord M a (if hi : i < d then some ⟨i,hi⟩ else none)

def blankSequence (M : Complexity.Machine) {d : ℕ} (a : Address d) : ℕ → ℕ → List Bool
  | _,0 => []
  | i,m+1 => blankAt M a i++blankSequence M a (i+1) m

def blankLoopRegisters : Fin 8 ↪ Fin 9 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 9 => x.val) h)⟩

def emitBlankLoop (reg : Fin 9 ↪ K) (M : Complexity.Machine) : Program K :=
  .while (reg 8) Option.isSome
    (.seq (emitBlankRequest (blankLoopRegisters.trans reg) M true)
      (.seq (.push (reg 1) true) (discard (reg 8))))

theorem emitBlankLoop_runs (reg : Fin 9 ↪ K) (M : Complexity.Machine) {d : ℕ}
    (a : Address d) (m : ℕ) : ∀ (S : Store K) (j : ℕ), j+m ≤ d →
    S (reg 0) = List.ofFn a → S (reg 1) = unary j → S (reg 7) = unary d →
    S (reg 8) = unary m →
    (∀ i : Fin 9, 3 ≤ i.val → i.val ≤ 6 → S (reg i) = []) →
    ∃ t ≤ m*(FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+160*(d+1)+3)+1,
      Runs (emitBlankLoop reg M) S t
        (Function.update (Function.update (Function.update S (reg 1) (unary (j+m)))
          (reg 8) []) (reg 2) ((blankSequence M a j m).reverse++S (reg 2))) := by
  have eqreg (i j : Fin 9) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  induction m with
  | zero =>
    intro S j hj ha hh hd hm he
    have hfinal : Function.update (Function.update (Function.update S (reg 1) (unary (j+0)))
        (reg 8) []) (reg 2) ((blankSequence M a j 0).reverse++S (reg 2)) = S := by
      simp only [Nat.add_zero,blankSequence,List.reverse_nil,List.nil_append]
      rw [← hh,Function.update_eq_self,show [] = S (reg 8) from hm.symm,Function.update_eq_self,
        Function.update_eq_self]
    rw [hfinal]
    exact ⟨1,by simp,Runs.while_false (by simp [hm,unary])⟩
  | succ m ih =>
    intro S j hj ha hh hd hm he
    have hjd : j < d := by omega
    obtain ⟨t,ht,hr⟩ := emitBlankRequest_some_runs S (blankLoopRegisters.trans reg) M a ⟨j,hjd⟩
      (by simpa [blankLoopRegisters] using ha) (by simpa [blankLoopRegisters] using hh)
      (by simpa [blankLoopRegisters] using hd)
      (by intro i hi hi'; exact he ⟨i.val,by omega⟩ hi hi')
    let A := Function.update S (reg 2) ((blankAt M a j).reverse++S (reg 2))
    have hr' : Runs (emitBlankRequest (blankLoopRegisters.trans reg) M true) S t A := by
      simpa [A,blankAt,hjd,blankLoopRegisters] using hr
    let B := Function.update A (reg 1) (unary (j+1))
    have hp : Runs (.push (reg 1) true) A 1 B := by
      simpa [B,A,eqreg,hh,unary,List.replicate_succ] using Runs.push A (reg 1) true
    let C := Function.update B (reg 8) (unary m)
    have hc : Runs (discard (reg 8)) B 1 C := by
      simpa [C,B,A,eqreg,hm,unary,List.replicate_succ] using discard_runs B (reg 8)
    obtain ⟨u,hu,hrest⟩ := ih C (j+1) (by omega) (by simp [C,B,A,eqreg,ha])
      (by simp [C,B,eqreg]) (by simp [C,B,A,eqreg,hd]) (by simp [C])
      (by intro i hi hi'; simp [C,B,A,eqreg,show i ≠ 8 by omega,show i ≠ 1 by omega,
            show i ≠ 2 by omega,he i hi hi'])
    have hfinal : Function.update (Function.update (Function.update C (reg 1) (unary (j+1+m)))
        (reg 8) []) (reg 2) ((blankSequence M a (j+1) m).reverse++C (reg 2)) =
        Function.update (Function.update (Function.update S (reg 1) (unary (j+(m+1))))
          (reg 8) []) (reg 2) ((blankSequence M a j (m+1)).reverse++S (reg 2)) := by
      funext k
      by_cases hk : k = reg 2
      · subst k; simp [C,B,A,eqreg,blankSequence,List.reverse_append,List.append_assoc]
      · by_cases hk' : k = reg 8
        · subst k; simp [eqreg]
        · by_cases hk'' : k = reg 1
          · subst k; simp [eqreg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          · simp [C,B,A,Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
    rw [hfinal] at hrest
    refine ⟨t+(1+1)+u+1,?_,Runs.while_true (by simp [hm,unary,List.replicate_succ])
      (Runs.seq hr' (Runs.seq hp hc)) hrest⟩
    simp only [Nat.add_mul,Nat.one_mul]
    omega

def blankWords (M : Complexity.Machine) {d : ℕ} (a : Address d) : List Bool :=
  blankPositionWord M a none++blankSequence M a 0 d

/-- Register 0 holds preserved threshold bits, 7 holds unary width, 2 is
output, and all other registers start and finish empty. -/
def emitBlankWords (reg : Fin 9 ↪ K) (M : Complexity.Machine) : Program K :=
  .seq (emitBlankRequest (blankLoopRegisters.trans reg) M false)
    (.seq (copy (reg 7) (reg 8) (reg 5))
      (.seq (emitBlankLoop reg M) (clear (reg 1))))

theorem emitBlankWords_runs (S : Store K) (reg : Fin 9 ↪ K) (M : Complexity.Machine)
    {d : ℕ} (a : Address d) (ha : S (reg 0) = List.ofFn a) (hd : S (reg 7) = unary d)
    (he : ∀ i : Fin 9, i ≠ 0 → i ≠ 2 → i ≠ 7 → S (reg i) = []) :
    Writes (reg 2) (emitBlankWords reg M) S (blankWords M a)
      ((d+1)*(FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+180*(d+1))) := by
  have eqreg (i j : Fin 9) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  obtain ⟨t,ht,hr⟩ := emitBlankRequest_none_runs S (blankLoopRegisters.trans reg) M a
    (by simpa [blankLoopRegisters] using ha) (by simpa [blankLoopRegisters] using hd)
    (he 3 (by decide) (by decide) (by decide)) (he 5 (by decide) (by decide) (by decide))
  let A := Function.update S (reg 2) ((blankPositionWord M a none).reverse++S (reg 2))
  have hr' : Runs (emitBlankRequest (blankLoopRegisters.trans reg) M false) S t A := by
    simpa [A,blankLoopRegisters] using hr
  let B := Function.update A (reg 8) (unary d)
  have hc : Runs (copy (reg 7) (reg 8) (reg 5)) A (7*d+2) B := by
    simpa [B,A,eqreg,hd,unary,he 8 (by decide) (by decide) (by decide)] using
      copy_runs A (reg 7) (reg 8) (reg 5) (reg.injective.ne (by decide))
        (reg.injective.ne (by decide)) (reg.injective.ne (by decide))
        (by simp [A,eqreg,he 5 (by decide) (by decide) (by decide)])
  obtain ⟨u,hu,hloop⟩ := emitBlankLoop_runs reg M a d B 0 (by omega)
    (by simp [B,A,eqreg,ha]) (by simp [B,A,eqreg,unary,he 1 (by decide) (by decide) (by decide)])
    (by simp [B,A,eqreg,hd]) (by simp [B])
    (by intro i hi hi'; simp [B,A,eqreg,show i ≠ 8 by omega,show i ≠ 2 by omega,
          he i (by omega) (by omega) (by omega)])
  let C := Function.update (Function.update S (reg 1) (unary d)) (reg 2)
    ((blankWords M a).reverse++S (reg 2))
  have hloop' : Runs (emitBlankLoop reg M) B u C := by
    convert hloop using 1
    funext k
    by_cases hk : k = reg 2
    · subst k; simp [C,B,A,eqreg,blankWords,List.reverse_append,List.append_assoc]
    · by_cases hk' : k = reg 1
      · subst k; simp [C,B,A,eqreg]
      · by_cases hk'' : k = reg 8
        · subst k; simp [C,eqreg,he 8 (by decide) (by decide) (by decide)]
        · simp [C,B,A,Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
  have hclear := clear_runs C (reg 1)
  have hc1 : C (reg 1) = unary d := by simp [C,eqreg]
  rw [hc1,unary_length] at hclear
  have hfinal : Function.update C (reg 1) [] =
      Function.update S (reg 2) ((blankWords M a).reverse++S (reg 2)) := by
    funext k
    by_cases hk : k = reg 1
    · subst k; simp [eqreg,he 1 (by decide) (by decide) (by decide)]
    · by_cases hk' : k = reg 2
      · subst k; simp [C,eqreg]
      · simp [C,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at hclear
  refine ⟨t+((7*d+2)+(u+(2*d+1))),?_,Runs.seq hr' (Runs.seq hc (Runs.seq hloop' hclear))⟩
  nlinarith

def blankBinaryRegisters : Fin 12 ↪ Fin 19 := ⟨![9,7,10,11,12,13,14,15,16,17,18,0],by decide⟩
def blankStreamRegisters : Fin 9 ↪ Fin 19 :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)⟩

/-- Unary threshold is in register 9, unary width in 7, and output in 2.
All other registers are scratch and are restored empty. -/
def emitBlankRequests (reg : Fin 19 ↪ K) (M : Complexity.Machine) : Program K :=
  .seq (binaryNatural (blankBinaryRegisters.trans reg))
    (.seq (emitBlankWords (blankStreamRegisters.trans reg) M) (clear (reg 0)))

theorem emitBlankRequests_runs (S : Store K) (reg : Fin 19 ↪ K) (M : Complexity.Machine)
    (n d : ℕ) (hn : S (reg 9) = unary n) (hd : S (reg 7) = unary d)
    (he : ∀ i : Fin 19, i ≠ 9 → i ≠ 7 → i ≠ 2 → S (reg i) = []) :
    Writes (reg 2) (emitBlankRequests reg M) S (blankWords M (ofNat d n))
      ((FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))+400)*(n+d+1)^2) := by
  have eqreg (i j : Fin 19) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  obtain ⟨t,ht,hr⟩ := binaryNatural_runs S (blankBinaryRegisters.trans reg) n d hn hd
    (he 10 (by decide) (by decide) (by decide))
    (by intro i hi; fin_cases i <;> simp_all [blankBinaryRegisters])
  let A := Function.update S (reg 0) (binaryWord d n)
  have hr' : Runs (binaryNatural (blankBinaryRegisters.trans reg)) S t A := by
    simpa [A,blankBinaryRegisters] using hr
  obtain ⟨u,hu,hs⟩ := emitBlankWords_runs A (blankStreamRegisters.trans reg) M (ofNat d n)
    (by simp [A,blankStreamRegisters,binaryWord])
    (by simpa [A,blankStreamRegisters,eqreg] using hd)
    (by intro i hi0 hi2 hi7
        have hi9 : (⟨i.val,by omega⟩ : Fin 19) ≠ 9 := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        have hi0' : (⟨i.val,by omega⟩ : Fin 19) ≠ 0 := by
          intro h; apply hi0; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)
        have hi2' : (⟨i.val,by omega⟩ : Fin 19) ≠ 2 := by
          intro h; apply hi2; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)
        have hi7' : (⟨i.val,by omega⟩ : Fin 19) ≠ 7 := by
          intro h; apply hi7; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)
        simp [A,blankStreamRegisters,eqreg,hi0',he ⟨i.val,by omega⟩ hi9 hi7' hi2'])
  let B := Function.update A (reg 2) ((blankWords M (ofNat d n)).reverse++A (reg 2))
  have hs' : Runs (emitBlankWords (blankStreamRegisters.trans reg) M) A u B := by
    simpa [B,blankStreamRegisters] using hs
  have hc := clear_runs B (reg 0)
  have hb0 : B (reg 0) = binaryWord d n := by simp [B,A,eqreg]
  rw [hb0,binaryWord_length] at hc
  have hfinal : Function.update B (reg 0) [] =
      Function.update S (reg 2) ((blankWords M (ofNat d n)).reverse++S (reg 2)) := by
    funext k
    by_cases hk : k = reg 0
    · subst k; simp [eqreg,he 0 (by decide) (by decide) (by decide)]
    · by_cases hk' : k = reg 2
      · subst k; simp [B,A,eqreg]
      · simp [B,A,Function.update_of_ne hk,Function.update_of_ne hk']
  rw [hfinal] at hc
  refine ⟨t+(u+(2*d+1)),?_,Runs.seq hr' (Runs.seq hs' hc)⟩
  have hle : d+1 ≤ n+d+1 := by omega
  have hsq := Nat.pow_le_pow_left hle 2
  have hsmall : d+1 ≤ (n+d+1)^2 := hle.trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)
  have hg := Nat.mul_le_mul_left (FiniteCode.size (CellularTableau.Gate (MachineCellular.Cell M))) hsmall
  nlinarith

end GroupWL.MachinePrograms.Structured
