import Init
import Lean

namespace Python

/- Declare an abstract syntax tree for Python -/

inductive Expr
  | constInt  (n : Int)
  | constBool (b : Bool)
  | constStr  (s : String)
  | var       (n : String)
  | plus      (e₁ e₂ : Expr)
  | len       (e : Expr)
  | concat    (e₁ e₂ : Expr)
  | equal     (e₁ e₂ : Expr)
  -- Dictionary stuff
  | emptyDict
  | lookup (d k : Expr)
deriving Inhabited, Repr

inductive Stmt
  | skip
  | seq (s₁ s₂ : Stmt)
  | assign (s : String) (e : Expr)
  | ifThenElse (e : Expr) (s₁ s₂ : Stmt)
  | dictAssign (s : String) (k : Expr) (v : Expr) -- for d[k] = v


/- Extend Lean's parser to parse Python snippets -/

declare_syntax_cat expr
declare_syntax_cat stmt

syntax num : expr
syntax ident : expr
syntax str : expr


-- Dictionary Syntax
syntax "{}" : expr
syntax:90 expr:90 "[" expr "]" : expr -- High precedence for lookup


syntax:65 expr:65 "+" expr:66 : expr
syntax "len(" expr ")" : expr
syntax expr "+" expr : expr
syntax:45 expr:45 "==" expr:46 : expr

syntax "skip" "; " : stmt
syntax stmt stmt : stmt
syntax ident " = " expr: stmt
syntax "if" expr ": " stmt "else" ": " stmt : stmt

syntax ident "[" expr "]" "= " expr : stmt

syntax "python" "{" stmt "}" : term
syntax "expr" "{" expr "}" : term


open Lean Elab Term in

-- General rules
macro_rules
  | `(expr { $n:num }) => `(Expr.constInt $(quote n.getNat))
  | `(expr { true }) => `(Expr.constBool true)
  | `(expr { false }) => `(Expr.constBool false)
  | `(expr { $s:str }) => do
    let raw := s.getString
    `(Expr.constStr $(quote raw))
  | `(expr { $s:ident }) =>
    let raw := s.getId.toString
    `(Expr.var $(quote raw))
  | `(expr {$e₁ + $e₂}) => `(Expr.plus (expr {$e₁}) (expr {$e₂}))
  | `(expr {$e₁ == $e₂}) => `(Expr.equal (expr {$e₁}) (expr {$e₂}))
  | `(expr { len($e) }) => `(Expr.len (expr { $e }))
  | `(expr { {} }) => `(Expr.emptyDict)
  | `(expr { $d:expr [ $k:expr ] }) => `(Expr.lookup (expr {$d}) (expr {$k}))



-- General Statment Rules
macro_rules
  | `(python { skip; } ) => `(Stmt.skip)
  | `(python {$s₁:stmt $s₂:stmt}) => `(Stmt.seq (python {$s₁}) (python {$s₂}))
  | `(python {$s:ident = $e:expr}) =>
    let raw := s.getId.toString
    `(Stmt.assign $(Lean.Quote.quote raw) (expr {$e}))
  | `(python{if $e : $s₁ else : $s₂}) => `(Stmt.ifThenElse (expr {$e}) (python {$s₁}) (python {$s₂}))
  | `(python { $s:ident [ $k:expr ] = $v:expr }) =>
    let raw := s.getId.toString
    `(Stmt.dictAssign $(Lean.Quote.quote raw) (expr {$k}) (expr {$v}))

-- Small testing

#check expr { x + y }
#check expr { "x" + "y" }

#check python {
  if x == y:
    z = x
  else :
    z = y
}


#check python {
  d = {}
  d["name"] = "gemini"
  x = d["name"]
}
