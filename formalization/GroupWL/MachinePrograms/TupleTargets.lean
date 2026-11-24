import GroupWL.MachinePrograms.TupleReplacement
import GroupWL.MachinePrograms.NatArrayCountedLoops

/-! Concrete array materialization of tuple replacement targets. -/
namespace GroupWL.MachinePrograms.TupleTargets
open NatArrayLanguage IndexedTuples
abbrev Reg := Fin 22
abbrev Arr := Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def replacementRegisters : Fin 11 ↪ Reg :=
  ⟨fun i => ⟨i.val,by omega⟩,
    by intro i j h; exact Fin.ext (congrArg (fun x : Reg => x.val) h)⟩

def decodeAtoms : List (Atom Reg Arr) := [
  .divmod 19 1 16 11,.divmod 9 10 19 12,.binary .lt 21 10 0]

def addOffset : Code := .atom (.binary .add 8 8 14)

def compute : Code := .seq (atoms decodeAtoms)
  (.branch 21 (.seq (replaceTuple replacementRegisters) addOffset)
    (.seq (.atom (.copy 8 9)) addOffset))

def address (k b row slot coordinate : ℕ) : ℕ := coordinate+k*(slot+b*row)

def value (n k b offset flat : ℕ) : ℕ :=
  offset+if flat/k%b<n then replaceCode n (flat/k/b) (flat%k) (flat/k%b) else flat/k/b

theorem compute_runs (n k b offset : ℕ) (hn : 0<n) (row : Fin (n^k))
    (slot : Fin b) (i : Fin k) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hbase : S.scalar 0=n) (hk : S.scalar 11=k) (hb : S.scalar 12=b)
    (hoff : S.scalar 14=offset) (hflat : S.scalar 16=address k b row.val slot.val i.val)
    (hroom : offset+n^k≤B) :
    ∃ t≤3*k+15,∃ T,Runs (storageBound Reg Arr B) compute S t T ∧ T.Bounded B ∧
      T.scalar 8=value n k b offset (address k b row.val slot.val i.val) := by
  have hkpos : 0<k := by have := i.isLt; omega
  have hbpos : 0<b := by have := slot.isLt; omega
  have hdiv : address k b row.val slot.val i.val/k=slot.val+b*row.val := by
    simp [address,Nat.add_mul_div_left _ _ hkpos,Nat.div_eq_of_lt i.isLt]
  have hmod : address k b row.val slot.val i.val%k=i.val := by
    simp [address,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt i.isLt]
  have hdiv' : (slot.val+b*row.val)/b=row.val := by
    simp [Nat.add_mul_div_left _ _ hbpos,Nat.div_eq_of_lt slot.isLt]
  have hmod' : (slot.val+b*row.val)%b=slot.val := by
    simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt slot.isLt]
  have h1 : 1≤B := by have hp : 0<n^k := pow_pos hn _; omega
  have hvalid : ValidAtoms B decodeAtoms S := by
    simp +decide only [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Function.update_apply,hbase,hk,hb,hflat,hdiv,hmod,hdiv',hmod']
    refine ⟨⟨by decide,hkpos⟩,trivial,⟨by decide,hbpos⟩,trivial,trivial,?_,trivial⟩
    split_ifs <;> omega
  obtain ⟨decode,hU⟩ := atoms_runs hS decodeAtoms hvalid
  let U := applyAtoms decodeAtoms S
  have ubase : U.scalar 0=n := by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hbase]
  have uindex : U.scalar 1=i.val := by
    simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hflat,hk,hmod]
  have ucode : U.scalar 9=row.val := by
    simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hflat,hk,hb,hdiv,hdiv']
  have uslot : U.scalar 10=slot.val := by
    simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hflat,hk,hb,hdiv,hmod']
  have uoffset : U.scalar 14=offset := by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hoff]
  have uflag : U.scalar 21=if slot.val<n then 1 else 0 := by
    simp [U,applyAtoms,decodeAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hbase,hflat,hk,hb,hdiv,hmod']
  by_cases hslot : slot.val<n
  · let a := finFunctionFinEquiv.symm row
    let x : Fin n := ⟨slot.val,hslot⟩
    have hcount : n^k≤B := by omega
    obtain ⟨V,repl,hV,hresult⟩ := replaceTuple_runs replacementRegisters hn a i x U B hU
      (by simpa [replacementRegisters] using ubase) (by simpa [replacementRegisters] using uindex)
      (by simpa [replacementRegisters,a] using ucode) (by simpa [replacementRegisters,x] using uslot) hcount
    have voffset : V.scalar 14=offset := by
      rw [repl.scalar_eq_of_not_mem 14 (by
        simp [replaceTuple,power,powerLoop,powerBody,atoms,NatArrayLanguage.sequence,replacementAtoms,
          replacementRegisters,replacementPowerRegisters,Program.scalarWrites,Atom.scalarWrites])]
      exact uoffset
    have hvresult : V.scalar 8=(finFunctionFinEquiv (Function.update a i x)).val := by
      simpa [replacementRegisters] using hresult
    have hout : (finFunctionFinEquiv (Function.update a i x)).val+offset≤B := by
      have := (finFunctionFinEquiv (Function.update a i x)).isLt
      omega
    have add := atom_runs hV (.binary .add 8 8 14) trivial
      (by simpa [Atom.SmallResult,BinaryOp.eval,hvresult,voffset] using hout)
    have hW := (Atom.binary .add 8 8 14).apply_bounded hV
      (by simpa [Atom.SmallResult,BinaryOp.eval,hvresult,voffset] using hout)
    refine ⟨3+((3*i.val+10)+1+1),by omega,_,Runs.seq decode
      (Runs.branch_nonzero (by change U.scalar 21≠0; simp [uflag,hslot]) (Runs.seq repl add)),hW,?_⟩
    simp only [Atom.apply,Store.setScalar_same,BinaryOp.eval,hvresult,voffset,value,hdiv,hmod,hdiv',hmod',if_pos hslot]
    have he : replaceCode n row.val i.val slot.val=(finFunctionFinEquiv (Function.update a i x)).val := by
      simpa [a,x] using replaceCode_correct a i x
    rw [he,Nat.add_comm]
  · have copy := atom_runs hU (.copy 8 9) trivial trivial
    let V := U.setScalar 8 row.val
    have copy' : Runs (storageBound Reg Arr B) (.atom (.copy 8 9)) U 1 V := by
      change Runs (storageBound Reg Arr B) (.atom (.copy 8 9)) U 1 (U.setScalar 8 (U.scalar 9)) at copy
      rw [ucode] at copy
      exact copy
    have hrow : row.val≤B := by have := row.isLt; omega
    have hV : V.Bounded B := hU.setScalar _ hrow
    have hsmall : (Atom.binary .add 8 8 14).SmallResult B V := by
      simp [Atom.SmallResult,BinaryOp.eval,V,uoffset]
      have := row.isLt
      omega
    have add := atom_runs hV (.binary .add 8 8 14) trivial hsmall
    refine ⟨3+(1+1+1),by omega,_,Runs.seq decode
      (Runs.branch_zero (by change U.scalar 21=0; simp [uflag,hslot]) (Runs.seq copy' add)),
      (Atom.binary .add 8 8 14).apply_bounded hV hsmall,?_⟩
    simp [Atom.apply,BinaryOp.eval,V,uoffset,value,hdiv,hmod,hdiv',hmod',hslot,Nat.add_comm]

def word (n k b offset : ℕ) : List ℕ :=
  List.ofFn (fun z : Fin ((n^k*b)*k) => value n k b offset z.val)

def body : Code := .seq compute (.atom (.write () 16 8))

theorem body_runs (n k b offset : ℕ) (hn : 0<n) (z : Fin ((n^k*b)*k))
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hbase : S.scalar 0=n) (hk : S.scalar 11=k) (hb : S.scalar 12=b)
    (hoff : S.scalar 14=offset) (hz : S.scalar 16=z.val)
    (hlen : (S.array ()).length=(n^k*b)*k) (hroom : offset+n^k≤B) :
    ∃ t≤3*k+16,∃ T,Runs (storageBound Reg Arr B) body S t T ∧ T.Bounded B ∧
      T.array ()=(S.array ()).set z.val (value n k b offset z.val) := by
  let ri := finProdFinEquiv.symm z
  let rs := finProdFinEquiv.symm ri.1
  have hzaddr : address k b rs.1.val rs.2.val ri.2.val=z.val := by
    change (finProdFinEquiv (finProdFinEquiv (rs.1,rs.2),ri.2)).val=z.val
    have hs : finProdFinEquiv rs=ri.1 := Equiv.apply_symm_apply _ _
    change (finProdFinEquiv (finProdFinEquiv rs,ri.2)).val=z.val
    rw [hs]
    change (finProdFinEquiv ri).val=z.val
    exact congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv z)
  obtain ⟨t,ht,U,run,hU,hval⟩ := compute_runs n k b offset hn rs.1 rs.2 ri.2 S B hS
    hbase hk hb hoff (by simpa [hzaddr] using hz) hroom
  have harray : U.array ()=S.array () := run.array_eq_of_not_mem () (by
    simp [compute,addOffset,atoms,decodeAtoms,replaceTuple,power,powerLoop,powerBody,
      replacementAtoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  have hindex : U.scalar 16=z.val := by
    rw [run.scalar_eq_of_not_mem 16 (by
      simp [compute,addOffset,atoms,decodeAtoms,replaceTuple,power,powerLoop,powerBody,
        replacementAtoms,replacementRegisters,replacementPowerRegisters,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites])]
    exact hz
  have valid : (Atom.write () 16 8).Valid U := by simp [Atom.Valid,hindex,harray,hlen,z.isLt]
  have write := atom_runs hU (.write () 16 8) valid trivial
  refine ⟨t+1,by omega,_,Runs.seq run write,(Atom.write () 16 8).apply_bounded hU trivial,?_⟩
  simp [Atom.apply,harray,hindex,hval,hzaddr]

private structure FillInvariant (n k b offset B j : ℕ) (S : Store Reg Arr) : Prop where
  bounded : S.Bounded B
  base_eq : S.scalar 0=n
  arity_eq : S.scalar 11=k
  width_eq : S.scalar 12=b
  offset_eq : S.scalar 14=offset
  index_eq : S.scalar 16=j
  todo_eq : S.scalar 17=(n^k*b)*k-j
  one_eq : S.scalar 20=1
  length_eq : (S.array ()).length=(n^k*b)*k
  values_eq : ∀ i < j,IndexedRefinement.read (S.array ()) i=value n k b offset i

def fill : Code := countedLoop 16 17 15 20 body

theorem fill_runs (n k b offset : ℕ) (hn : 0<n) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hbase : S.scalar 0=n) (hk : S.scalar 11=k) (hb : S.scalar 12=b)
    (hoff : S.scalar 14=offset) (hsize : S.scalar 15=(n^k*b)*k) (hone : S.scalar 20=1)
    (hlen : (S.array ()).length=(n^k*b)*k) (hroom : offset+n^k≤B) :
    ∃ t≤((n^k*b)*k)*(3*k+19)+3,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧
      T.Bounded B ∧ T.array ()=word n k b offset := by
  have htotal : (n^k*b)*k≤B := by simpa [hsize] using hS.1 15
  let I := FillInvariant n k b offset B
  have hcopy : (S.setScalar 17 (S.scalar 15)).Bounded B := hS.setScalar _ (hS.1 _)
  have hstart : I 0 ((S.setScalar 17 (S.scalar 15)).setScalar 16 0) := by
    refine ⟨hcopy.setScalar _ (Nat.zero_le _),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp [hbase]
    · simp [hk]
    · simp [hb]
    · simp [hoff]
    · simp
    · simp [hsize]
    · simp [hone]
    · simpa using hlen
    · intro i hi; omega
  have control : ∀ j≤(n^k*b)*k,∀ U,I j U → U.scalar 16=j ∧ U.scalar 17=(n^k*b)*k-j ∧
      U.scalar 20=1 ∧ U.size≤storageBound Reg Arr B := by
    intro j hj U hU
    exact ⟨hU.index_eq,hU.todo_eq,hU.one_eq,Store.size_le_of_bounded hU.bounded⟩
  have step : ∀ j<(n^k*b)*k,∀ U,I j U → ∃ t≤3*k+16,∃ V,
      Runs (storageBound Reg Arr B) body U t V ∧
      V.scalar 16=j ∧ V.scalar 17=(n^k*b)*k-j ∧ V.scalar 20=1 ∧
      (V.setScalar 16 (j+1)).size≤storageBound Reg Arr B ∧ I (j+1) (advance 16 17 V) := by
    intro j hj U hU
    obtain ⟨t,ht,V,run,hV,harray⟩ := body_runs n k b offset hn ⟨j,hj⟩ U B hU.bounded
      hU.base_eq hU.arity_eq hU.width_eq hU.offset_eq hU.index_eq hU.length_eq hroom
    have frames (r : Reg) (hr : r∈({0,11,12,14,16,17,20} : Finset Reg)) : V.scalar r=U.scalar r := by
      apply run.scalar_eq_of_not_mem
      fin_cases r <;> simp_all [body,compute,addOffset,atoms,decodeAtoms,replaceTuple,power,powerLoop,powerBody,
        replacementAtoms,replacementRegisters,replacementPowerRegisters,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites]
    have hvi : V.scalar 16=j := (frames _ (by simp)).trans hU.index_eq
    have hvr : V.scalar 17=(n^k*b)*k-j := (frames _ (by simp)).trans hU.todo_eq
    have hvone : V.scalar 20=1 := (frames _ (by simp)).trans hU.one_eq
    have hmid := hV.setScalar 16 (show j+1≤B by omega)
    refine ⟨t,ht,V,run,hvi,hvr,hvone,Store.size_le_of_bounded hmid,?_⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [advance,hvi] using hmid.setScalar 17 (show V.scalar 17-1≤B by rw [hvr]; omega)
    · simpa [advance] using (frames _ (by simp)).trans hU.base_eq
    · simpa [advance] using (frames _ (by simp)).trans hU.arity_eq
    · simpa [advance] using (frames _ (by simp)).trans hU.width_eq
    · simpa [advance] using (frames _ (by simp)).trans hU.offset_eq
    · simp [advance,hvi]
    · simp [advance,hvr]; omega
    · simpa [advance] using hvone
    · simpa [advance,harray] using hU.length_eq
    · intro i hi
      change IndexedRefinement.read (V.array ()) i=value n k b offset i
      rw [harray]
      by_cases hij : i=j
      · subst i; simp [IndexedRefinement.read,hU.length_eq,hj]
      · have hil : i<j := by omega
        simpa [IndexedRefinement.read,List.getElem?_set,hij,Ne.symm hij] using hU.values_eq i hil
  obtain ⟨t,ht,T,run,hT⟩ := countedLoop_runs (storageBound Reg Arr B) 16 17 15 20 body
    ((n^k*b)*k) (3*k+16) I S (Store.size_le_of_bounded hS) (Store.size_le_of_bounded hcopy)
    hstart control (by decide) (by decide) step
  refine ⟨t,by omega,T,run,hT.bounded,?_⟩
  apply List.ext_getElem
  · simpa [word] using hT.length_eq
  · intro i hi hi'
    have hr := hT.values_eq i (by simpa [hT.length_eq] using hi)
    simpa [word,IndexedRefinement.read,List.getElem?_eq_getElem,hi] using hr

def countRegisters : Fin 5 ↪ Reg := ⟨![0,11,13,3,4],by decide⟩

def prelude : List (Atom Reg Arr) := [
  .binary .mul 15 13 12,.binary .mul 15 15 11,.const 18 0,
  .allocate () 15 18,.const 20 1]

/-- Build one group's complete target-array block. Inputs are base order 0,
arity 11, padded width 12, and disjoint-universe offset 14. -/
def generate : Code := .seq (power countRegisters) (.seq (atoms prelude) fill)

theorem generate_runs_with_count (n k b offset : ℕ) (hn : 0<n) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hbase : S.scalar 0=n) (hk : S.scalar 11=k) (hb : S.scalar 12=b) (hoff : S.scalar 14=offset)
    (hroom : offset+n^k≤B) (hslots : n^k*b≤B) (hsize : (n^k*b)*k≤B) :
    ∃ t≤((n^k*b)*k)*(3*k+19)+3*k+12,∃ T,
      Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧ T.array ()=word n k b offset ∧
        T.scalar 13=n^k := by
  have hcount : n^k≤B := by omega
  obtain ⟨U,powrun,hU,hpow⟩ := power_runs countRegisters S n k B hS hn hbase hk hcount
  have upow : U.scalar 13=n^k := by simpa [countRegisters] using hpow
  have frames (r : Reg) (hr : r∈({0,11,12,14} : Finset Reg)) : U.scalar r=S.scalar r := by
    apply powrun.scalar_eq_of_not_mem
    fin_cases r <;> simp_all [power,powerLoop,powerBody,atoms,countRegisters,NatArrayLanguage.sequence,
      Program.scalarWrites,Atom.scalarWrites]
  have ubase : U.scalar 0=n := (frames _ (by simp)).trans hbase
  have uk : U.scalar 11=k := (frames _ (by simp)).trans hk
  have ub : U.scalar 12=b := (frames _ (by simp)).trans hb
  have uoff : U.scalar 14=offset := (frames _ (by simp)).trans hoff
  have h1 : 1≤B := (one_le_pow₀ hn).trans hcount
  have hvalid : ValidAtoms B prelude U := by
    simp +decide only [prelude,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,Store.setArray,Function.update_apply,upow,uk,ub]
    exact ⟨trivial,hslots,trivial,hsize,trivial,Nat.zero_le _,trivial,trivial,trivial,h1,trivial⟩
  obtain ⟨init,hV⟩ := atoms_runs hU prelude hvalid
  let V := applyAtoms prelude U
  have vbase : V.scalar 0=n := by simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,ubase]
  have vk : V.scalar 11=k := by simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,uk]
  have vb : V.scalar 12=b := by simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,ub]
  have voff : V.scalar 14=offset := by simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,uoff]
  have vsize : V.scalar 15=(n^k*b)*k := by
    simp [V,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,upow,ub,uk]
  have vone : V.scalar 20=1 := by simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray]
  have vlen : (V.array ()).length=(n^k*b)*k := by
    simp [V,applyAtoms,prelude,Atom.apply,BinaryOp.eval,Store.setScalar,Store.setArray,upow,ub,uk]
  obtain ⟨t,ht,T,run,hT,heq⟩ := fill_runs n k b offset hn V B hV vbase vk vb voff vsize vone vlen hroom
  have vcount : V.scalar 13=n^k := by
    simp [V,applyAtoms,prelude,Atom.apply,Store.setScalar,Store.setArray,upow]
  have tcount : T.scalar 13=n^k := by
    rw [run.scalar_eq_of_not_mem 13 (by
      simp [fill,countedLoop,body,compute,addOffset,atoms,decodeAtoms,replaceTuple,power,powerLoop,powerBody,
        replacementAtoms,replacementRegisters,replacementPowerRegisters,NatArrayLanguage.sequence,
        Program.scalarWrites,Atom.scalarWrites])]
    exact vcount
  exact ⟨(3*k+4)+(5+t),by omega,T,Runs.seq powrun (Runs.seq init run),hT,heq,tcount⟩

theorem generate_runs (n k b offset : ℕ) (hn : 0<n) (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B)
    (hbase : S.scalar 0=n) (hk : S.scalar 11=k) (hb : S.scalar 12=b) (hoff : S.scalar 14=offset)
    (hroom : offset+n^k≤B) (hslots : n^k*b≤B) (hsize : (n^k*b)*k≤B) :
    ∃ t≤((n^k*b)*k)*(3*k+19)+3*k+12,∃ T,
      Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧ T.array ()=word n k b offset := by
  obtain ⟨t,ht,T,run,hT,heq,_⟩ := generate_runs_with_count n k b offset hn S B hS
    hbase hk hb hoff hroom hslots hsize
  exact ⟨t,ht,T,run,hT,heq⟩

end GroupWL.MachinePrograms.TupleTargets
