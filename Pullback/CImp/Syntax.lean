import Init
import Lean

/-! CImp: imp extended with C memory semantics -/
namespace CImp

/- Abtract Syntax Tree -/
abbrev Value : Type := BitVec 32

#eval (1 : Value) < (2 : Value)

inductive Expr where
  | const (v : Value)
  | var (n : Lean.Name)
  | lt (e₁ e₂ : Expr)
  | add (e₁ e₂ : Expr)
  | deref (ptr : Expr)
deriving Repr

inductive Stmt where
  | assign (n : Lean.Name) (e : Expr)
  /-
    *ptr := e
  -/
  | assignPtr (ptr : Expr) (e : Expr)
  | seq (s₁ : Stmt) (s₂ : Stmt)
  | IfThenElse (c : Expr) (t : Stmt) (e : Stmt)
  | while (c : Expr) (b : Stmt)
deriving Repr

/- Syntax declaration -/
declare_syntax_cat expr
declare_syntax_cat stmt

syntax num : expr
syntax ident : expr
syntax expr "<" expr : expr
syntax expr "+" expr : expr
syntax "*" expr : expr

syntax ident ":=" expr ";" : stmt
syntax "*" expr ":= "expr ";" : stmt

syntax stmt stmt : stmt
syntax "if" "(" expr ")" "{" stmt "}" "else" "{" stmt "}" : stmt
syntax "while" "(" expr ")" "{" stmt "}" : stmt

syntax "expr" "{" expr "}" : term
syntax "stmt" "{" stmt "}" : term

/- Syntax Elaboration -/
macro_rules
  | `(expr{$i:ident}) => `(Expr.var $(Lean.Quote.quote i.getId))
  | `(expr{$x < $y}) => `(Expr.lt expr{$x} expr{$y})
  | `(expr{$x + $y}) => `(Expr.add expr{$x} expr{$y})
  | `(expr{$n:num}) => `(Expr.const $(Lean.Quote.quote (n.getNat)))
  | `(expr{*$ptr:expr}) => `(Expr.deref expr{$ptr})
  | `(stmt{$x:ident := $e:expr ;}) => `(Stmt.assign $(Lean.Quote.quote x.getId) expr{$e})
  | `(stmt{*$ptr:expr := $e:expr ;}) => `(Stmt.assignPtr expr{$ptr} expr{$e})
  | `(stmt{$s₁ $s₂}) => `(Stmt.seq stmt{$s₁} stmt{$s₂})
  | `(stmt{if ($e) { $s₁ } else { $s₂ }}) => `(Stmt.IfThenElse expr{$e} stmt{$s₁} stmt{$s₂})
  | `(stmt{while ( $e ) { $s }}) => `(Stmt.while expr{$e} stmt{$s})

/- Pretty printing -/

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Expr.var]
def unexpandVar : Unexpander
  | `($_Exprvar $n) =>
    match n.raw.isNameLit? with
    | some name => `(expr{$(mkIdent name):ident})
    | none => throw ()
  | _ => throw ()

@[app_unexpander Expr.const]
def unexpandConst : Unexpander
  | `($_exprConst $n:term) =>
    match n.raw.isNatLit? with
    | some val => `(expr{$(Syntax.mkNatLit val):num})
    | none => throw ()
  | _ => throw ()

@[app_unexpander Expr.add]
def unexpandAdd : Unexpander
  | `($_add expr{$x} expr{$y}) => `(expr{$x + $y})
  | _ => throw ()

@[app_unexpander Expr.lt]
def unexpandLt : Unexpander
  | `($_lt expr{$x} expr{$y}) => `(expr{$x < $y})
  | _ => throw ()

@[app_unexpander Expr.deref]
def unexpandDeref : Unexpander
  | `($_Exprderef expr{$e}) =>
    `(expr{* $e})
  | _ => throw ()

@[app_unexpander Stmt.assign]
def unexpandAssign : Unexpander
  | `($_ $x:str expr{$e}) =>
    `(stmt{$(mkIdent (Name.mkSimple x.getString)):ident := $e;})
  | _ => throw ()

@[app_unexpander Stmt.assignPtr]
def unexpandAssignPtr : Unexpander
  | `($_ expr{$ptr} expr{$e}) =>
    `(stmt{*$ptr := $e;})
  | _ => throw ()

@[app_unexpander Stmt.seq]
def unexpandSeq : Unexpander
  | `($_seq stmt{$s1} stmt{$s2}) => `(stmt{$s1 $s2})
  | _ => throw ()

@[app_unexpander Stmt.IfThenElse]
def unexpandIf : Unexpander
  | `($_ expr{$e} stmt{$s1} stmt{$s2}) => `(stmt{if ($e) { $s1 } else { $s2 }})
  | _ => throw ()

@[app_unexpander Stmt.while]
def unexpandWhile : Unexpander
  | `($_while expr{$e} stmt{$s}) => `(stmt{while ($e) { $s }})
  | _ => throw ()


#check stmt{while (x < 10) { x := x + 1; }}
