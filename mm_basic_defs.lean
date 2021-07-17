-- Armv8 memory model: Basic defintions

/- ######################## Elements ######################## -/

def observer := Type

@[reducible]
def location := ℕ

@[reducible]
def program_order_instruction_index := ℕ

@[derive decidable_eq] 
inductive instruction
| write 
| read 

structure event :=
  (id : ℕ)
  (ob : observer) 
  (poii : program_order_instruction_index)
  (instruction : instruction)
  (loc : location)

@[reducible]
def program := list event

/- Util functions -/
def is_write (e : event) : Prop := 
  e.instruction = instruction.write

def is_read (e : event) : Prop := 
  e.instruction = instruction.read

def same_ob (e₁ e₂ : event) : Prop := 
  e₁.ob = e₁.ob

def same_loc (e₁ e₂ : event) : Prop := 
  e₁.loc = e₁.loc

def acyclic (r : event → event → Prop) : Prop := irreflexive (tc r)
  


/- ######################## Relations ######################## -/  

def in_program_order : event → event → Prop :=
  λ e₁ e₂, (same_ob e₁ e₂) ∧  (e₁.poii < e₂.poii)

def po_loc : event → event → Prop :=
  λ e₁ e₂, (in_program_order e₁ e₂) ∧  (e₁.loc = e₂.loc)

def wf_coherence_order (co : event → event → Prop) : Prop :=
  (∀ e₁ e₂, co e₁ e₂ → (same_loc e₁ e₂) ∧ (is_write e₁) ∧ (is_write e₂)) ∧
  (∀ e₁ e₂, (is_write e₁) → (is_write e₂) → (co e₁ e₂ ∨ co e₂ e₁)) 

def reads_from : event → event → Prop :=
  λ w₁ r₂, is_write w₁ ∧ is_read r₂ ∧ same_loc w₁ r₂ 

def local_read_succ : event → event → Prop :=
  λ w₁ r₂,
    ((is_write w₁ ∧ is_read r₂) ∧ (same_ob w₁ r₂) ∧ (same_loc w₁ r₂)) ∧ (in_program_order w₁ r₂) → 
    (¬ ∃ w', ((is_write w') ∧ (same_ob w₁ w') ∧ (same_loc w₁ w')) → 
      ((in_program_order w₁ w') ∧ (in_program_order w' r₂)))

def local_write_succ : event → event → Prop := 
  λ w₁ w₂, (is_write w₁ ∧ is_write w₁) ∧ (same_ob w₁ w₂) ∧ (same_loc w₁ w₂) ∧ (in_program_order w₁ w₂)

def coherence_after (co : event → event → Prop) : event → event → Prop := 
  λ e₁ w₂, 
    ((is_write e₁ ∧ is_write w₂ ∧ same_loc e₁ w₂) → co e₁ w₂) ∨                          
    ((is_read e₁ ∧ is_write w₂ ∧ same_loc e₁ w₂) → ∃ w', is_write w' ∧ reads_from w' e₁ ∧ co w' w₂) -- equivalent to the fr relation

def observed_by (co : event → event → Prop) : event → event →  Prop :=
  λ e₁ e₂,
    ((is_write e₂ ∧ ¬ same_ob e₁ e₂) → coherence_after co e₁ e₂) ∨ 
    ((is_write e₁ ∧ is_read e₂ ∧ ¬ same_ob e₁ e₂) → reads_from e₁ e₂)
