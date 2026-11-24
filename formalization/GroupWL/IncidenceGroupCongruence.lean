import GroupWL.FrameResponses

/-! Proof-level changes of finite enumerations and equal source systems. -/
namespace GroupWL.IncidenceGroupCongruence

open IncidenceTensor FrameResponses

variable {F I J : Type} [Field F]
  {V : J → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module F (V j)]

noncomputable def zero (fI fI' : Fintype I) (fJ fJ' : Fintype J)
    (dJ dJ' : DecidableEq J) (A B : AffineSystem F I J V) (h : A = B)
    (q : ℕ) (hq : 2 ≤ q) :
    @ZeroGroup F I J _ fI fJ dJ V _ _ A q hq ≃*
      @ZeroGroup F I J _ fI' fJ' dJ' V _ _ B q hq := by
  subst B
  cases Subsingleton.elim fI fI'
  cases Subsingleton.elim fJ fJ'
  cases Subsingleton.elim dJ dJ'
  exact MulEquiv.refl _

noncomputable def charged (fI fI' : Fintype I) (fJ fJ' : Fintype J)
    (dI dI' : DecidableEq I) (dJ dJ' : DecidableEq J) (A B : AffineSystem F I J V) (h : A = B)
    (q : ℕ) (hq : 2 ≤ q) (β : I → F) :
    @ChargedGroup F I J _ fI fJ dI dJ V _ _ A q hq β ≃*
      @ChargedGroup F I J _ fI' fJ' dI' dJ' V _ _ B q hq β := by
  subst B
  cases Subsingleton.elim fI fI'
  cases Subsingleton.elim fJ fJ'
  cases Subsingleton.elim dI dI'
  cases Subsingleton.elim dJ dJ'
  exact MulEquiv.refl _

end GroupWL.IncidenceGroupCongruence
