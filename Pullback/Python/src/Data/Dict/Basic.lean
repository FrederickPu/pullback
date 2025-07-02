namespace Python

abbrev Dict (α : Type) := List (String × α)

namespace Dict

/-- Find the most recent binding for a key. -/
def find (d : Dict α) (s : String) : Option α :=
  match d with
  | []          => none
  | (k',v)::rest =>
    if s == k' then some v
    else find rest s

/-- Insert or overwrite a binding `k ↦ v`. -/
def insert (d : Dict α) (k : String) (v : α) : Dict α :=
  (k, v) :: d

/-- Delete *all* bindings for `k`. -/
def erase (d : Dict α) (k : String) : Dict α :=
  d.filter (fun (k',_) => k' ≠ k)

end Dict
