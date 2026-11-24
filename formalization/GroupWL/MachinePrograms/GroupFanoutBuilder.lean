import GroupWL.MachinePrograms.GroupTargetBuilder

/-! Operational construction of the tuple replacement multiplicities. -/
namespace GroupWL.MachinePrograms.GroupFanoutBuilder
open NatArrayLanguage
abbrev Reg := Fin 5 ⊕ NatArrayConcat.Reg
abbrev Arr := Unit ⊕ NatArrayConcat.Arr
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def generate : Code := .seq ((power (Function.Embedding.refl (Fin 5))).map Sum.inl Sum.inl)
  (.seq (.atom (.allocate (.inr 0) (.inl 2) (.inl 0)))
    (.seq (.atom (.copy (.inl 0) (.inr 0)))
      (.seq ((power (Function.Embedding.refl (Fin 5))).map Sum.inl Sum.inl)
        (.seq (.atom (.allocate (.inr 1) (.inl 2) (.inl 0)))
          (NatArrayConcat.concat.map Sum.inr Sum.inr)))))

theorem fanoutWord (n m k : ℕ) (hn : 0<n) :
    (IndexedTuples.data n m k hn).fanoutWord=List.replicate (n^k) n++List.replicate (m^k) m := by
  unfold IndexedRefinement.Data.fanoutWord
  rw [List.ofFn_add]
  congr 1
  · simp [IndexedTuples.data,IndexedTuples.fanout,List.ofFn_const]
  · simp [IndexedTuples.data,IndexedTuples.fanout,List.ofFn_const]

theorem generate_runs (n m k : ℕ) (hn : 0<n) (hm : 0<m) (S : Store Reg Arr) (B : ℕ)
    (hS : S.Bounded B) (hleft : S.scalar (.inl 0)=n) (hright : S.scalar (.inr 0)=m)
    (hk : S.scalar (.inl 1)=k) (hroom : n^k+m^k≤B) :
    ∃ t≤8*(n^k+m^k)+6*k+20,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      T.array (.inr 2)=(IndexedTuples.data n m k hn).fanoutWord := by
  obtain ⟨U,first,hU,hcountU⟩ := power_runs (Function.Embedding.refl (Fin 5)) S.left n k B hS.left
    hn hleft hk (by omega)
  change U.scalar 2=n^k at hcountU
  let A := U.join S.right
  have first' : Runs (storageBound Reg Arr B) ((power (Function.Embedding.refl (Fin 5))).map Sum.inl Sum.inl)
      S (3*k+4) A := first.left_bounded hS
  have hA : A.Bounded B := hU.join hS.right
  have ubase : U.scalar 0=n := by
    rw [first.scalar_eq_of_not_mem 0 (by
      simp [power,powerLoop,powerBody,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])]
    exact hleft
  have uexp : U.scalar 1=k := by
    rw [first.scalar_eq_of_not_mem 1 (by
      simp [power,powerLoop,powerBody,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])]
    exact hk
  let C := (Atom.allocate (.inr 0) (.inl 2) (.inl 0)).apply A
  have alloc := atom_runs hA (.allocate (.inr 0) (.inl 2) (.inl 0)) trivial trivial
  have hC : C.Bounded B := (Atom.allocate (.inr 0) (.inl 2) (.inl 0)).apply_bounded hA trivial
  let D := (Atom.copy (.inl 0) (.inr 0)).apply C
  have copy := atom_runs hC (.copy (.inl 0) (.inr 0)) trivial trivial
  have hD : D.Bounded B := (Atom.copy (.inl 0) (.inr 0)).apply_bounded hC trivial
  have dl : D.left.scalar 0=m := by simp [D,C,A,Atom.apply,Store.left,Store.right,Store.setScalar,hright]
  have dk : D.left.scalar 1=k := by simp [D,C,A,Atom.apply,Store.left,Store.setScalar,uexp]
  have dsaved : D.right.array 0=List.replicate (n^k) n := by
    simp [D,C,A,Atom.apply,Store.right,Store.setArray,ubase,hcountU]
  obtain ⟨V,second,hV,hcountV⟩ := power_runs (Function.Embedding.refl (Fin 5)) D.left m k B hD.left
    hm dl dk (by omega)
  change V.scalar 2=m^k at hcountV
  have vbase : V.scalar 0=m := by
    rw [second.scalar_eq_of_not_mem 0 (by
      simp [power,powerLoop,powerBody,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])]
    exact dl
  let F := V.join D.right
  have second' := second.left_bounded hD
  have hF : F.Bounded B := hV.join hD.right
  let G := (Atom.allocate (.inr 1) (.inl 2) (.inl 0)).apply F
  have alloc' := atom_runs hF (.allocate (.inr 1) (.inl 2) (.inl 0)) trivial trivial
  have hG : G.Bounded B := (Atom.allocate (.inr 1) (.inl 2) (.inl 0)).apply_bounded hF trivial
  have gl : G.right.array 0=List.replicate (n^k) n := by
    simpa [G,F,Atom.apply,Store.right,Store.setArray] using dsaved
  have gr : G.right.array 1=List.replicate (m^k) m := by
    simp [G,F,Atom.apply,Store.right,Store.setArray,vbase,hcountV]
  have h1 : 1≤B := (one_le_pow₀ hn).trans (by omega : n^k≤B)
  obtain ⟨t,ht,W,last,hW,hout,_,_⟩ := NatArrayConcat.concat_runs G.right B hG.right
    (by simpa [gl,gr] using hroom) h1
  have last' := last.right_bounded hG
  refine ⟨(3*k+4)+(1+(1+((3*k+4)+(1+t)))),?_,G.left.join W,
    Runs.seq first' (Runs.seq alloc (Runs.seq copy (Runs.seq second' (Runs.seq alloc' last')))),
    hG.left.join hW,?_⟩
  · simp only [gl,gr,List.length_replicate] at ht
    omega
  · change W.array 2=_
    rw [hout,gl,gr,fanoutWord]

end GroupWL.MachinePrograms.GroupFanoutBuilder
