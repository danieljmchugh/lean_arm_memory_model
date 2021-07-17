-- Armv8 memory model: Ordering constraints
import mm_dependencies

/- ######################## Internal requirements ######################## -/
-- note, acyclic takes tc of the union
def internal_visibility_requirement (co : event → event → Prop) (p : program) : Prop := 
  acyclic (λ e₁ e₂, e₁ ∈ p ∧ e₂ ∈ p ∧ coherence_after co e₁ e₂ ∨ reads_from e₁ e₂ ∨ po_loc e₁ e₂) 

/- ######################## External requirements ######################## -/

def external_visibility_requirement (co dtr : event → event → Prop) (p : program) : Prop := 
  acyclic (λ e₁ e₂, e₁ ∈ p ∧ e₂ ∈ p ∧ ordered_before co dtr e₁ e₂) 
  


def valid_program (co dtr : event → event → Prop) (p : program)  : Prop := 
  (internal_visibility_requirement co p) ∧ (external_visibility_requirement co dtr p)