-- Armv8 memory model: Dependency defintions
import mm_basic_defs

/- ######################## Dependency definitions ######################## -/

def address_dependency (dtr : event → event → Prop) : event → event → Prop := 
  λ r₁ e₂, is_read r₁ ∧ in_program_order r₁ e₂ ∧ dtr r₁ e₂

def data_dependency (dtr : event → event → Prop) : event → event → Prop := 
  λ r₁ w₂, is_read r₁ ∧ is_write w₂ ∧ in_program_order r₁ w₂ ∧ dtr r₁ w₂

def control_dependency (dtr : event → event → Prop) : event → event → Prop := 
  λ r₁ e₂, is_read r₁ ∧ in_program_order r₁ e₂ ∧ dtr r₁ e₂

def dependency_ordered_before (dtr : event → event → Prop) : event → event → Prop := 
  λ r₁ e₂, is_read r₁ ∧ same_ob r₁ e₂ ∧ in_program_order r₁ e₂ ∧ 
    (address_dependency dtr r₁ e₂ ∨ data_dependency dtr r₁ e₂) ∨ 
    (is_write e₂ ∧ control_dependency dtr r₁ e₂) ∨ 
    (is_write e₂ ∧ ∃ e₃, in_program_order e₂ e₃ ∧ address_dependency dtr r₁ e₃ ) ∨ 
    (∃ w₃, is_write w₃ ∧ local_read_succ w₃ e₂ ∧ (address_dependency dtr r₁ w₃ ∨ data_dependency dtr r₁ w₃ ))

def locally_ordered_before (dtr : event → event → Prop) : event → event → Prop :=
  tc (λ e₁ e₂, (same_ob e₁ e₂) ∧ 
      (local_write_succ e₁ e₂) ∨ 
      (dependency_ordered_before dtr e₁ e₂))
      -- ∨ aob
      -- ∨ bob

def ordered_before (co dtr : event → event → Prop ) : event → event → Prop :=
  tc (λ e₁ e₂, observed_by co e₁ e₂ ∨ locally_ordered_before dtr e₁ e₂)
