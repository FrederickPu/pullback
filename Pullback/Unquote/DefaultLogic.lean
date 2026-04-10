import Pullback.UnquoteDefault.Basic

inductive Default where
  | TrueProp       : Nat → DefaultLogic       -- proposition is true
  | ConsistentProp : Nat → DefaultLogic       -- proposition is consistent

-- (Prereqs + Justifications, Conclusion)
def rules : List (List Default × Default) :=
  [
    -- Rule 0: if TrueProp 0 is provable and ConsistentProp 1 holds, conclude TrueProp 2
    ([Default.TrueProp 0, Default.ConsistentProp 1], Default.TrueProp 2),

    -- Rule 1: if TrueProp 2 is provable, conclude TrueProp 3
    ([Default.TrueProp 2], Default.TrueProp 3),

    -- Rule 2: if TrueProp 1 is provable, conclude TrueProp 4
    ([Default.TrueProp 1], Default.TrueProp 4),

    -- Rule 3: if TrueProp 3, TrueProp 4, and ConsistentProp 0 holds, conclude TrueProp 5
    ([Default.TrueProp 3, Default.TrueProp 4, Default.ConsistentProp 0], Default.TrueProp 5)
  ]

-- if you have a solver that works on `solve : Default → WompWompLam ...`
-- then for correctly written syntax `<s>` can write `((solve <s>).unquote : <s>)` note thate the `<s>` inside the quote is parsed to a different type than the `<s>` outside the type but because the `Default` embeds nicely inside of lean type theory the same syntax can be overloaded to both describe the quoted and non quoted form. Since all judgements are implcit through unification we in principle dont need any metaproggrammign for this automation at all (we still might want to run at least an opaque because running in kernel mode might be too slow)!


-- note that we can also make non first order embeddings into lean, for example we can embed into lean structures even tho the underlying theory is guaranteed to have a first order model
