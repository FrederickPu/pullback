class UnquoteTy (Ty : Type) where
  -- `syntax T` returns Type describing the syntax of quoted type `T : Ty`
  «syntax» : Ty → Type
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : Ty → Type
  unquote  (T : Ty) (t : «syntax» T) : interpret T
  imp (α β : Ty) : Ty
  interpret_imp (α β : Ty) : interpret (imp α β) = interpret α → interpret β
  unit : Ty
  hUnit : interpret unit = Unit


infixr:80 "→" => UnquoteTy.imp
open UnquoteTy

class MonadTy {Ty : Type} [UnquoteTy Ty] (m : Ty → Ty) where
  map {α β : Ty} : «syntax» (((α → β) → (m α)) → (m β))
  mapConst {α β : Ty} : «syntax» (α → m β → m α)
  pure {α : Ty} : «syntax» (α → (m α))
  seq {α β : Ty} : «syntax» ((m (imp α β)) → (unit → (m α)) → (m β))
  seqLeft {α β : Ty} : «syntax» ((m α) → (unit → (m β)) → (m α))
  seqRight {α β : Ty} : «syntax» ((m α) → (unit → (m β)) → (m β))
  bind {α β : Ty} : «syntax» ((m α) → (α → (m β)) → (m β))
