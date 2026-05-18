class Typed (term ty : Type) where
  hasType : term → ty → Bool

class TypedWithQuote (term ty : Type) extends Typed term ty where
  quote : ty → ty
  unquote : term → term
  hquoteUnquote :
    ∀ t : ty, ∀ x : term, hasType x (quote t) → hasType (unquote x) t
