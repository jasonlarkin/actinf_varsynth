# Lean 4 Troubleshooting Guide: Common Errors and Solutions

## 🎯 **Overview**

This guide documents common errors encountered during Lean 4 development and their solutions, based on our experience implementing the variational synthesis framework.

## 🚀 **Environment Setup Issues**

### **1. Lean Installation Problems**

#### **Error**: `error: failed to parse latest release tag`
**Cause**: Network connectivity issues or Lean release server problems
**Solution**: 
```bash
# Install specific version instead of 'stable'
elan toolchain install 4.6.0
elan default 4.6.0
```

#### **Error**: `Could not resolve host: releases.lean-lang.org`
**Cause**: WSL networking issues or DNS problems
**Solution**:
```bash
# Check network connectivity
ping google.com
nslookup releases.lean-lang.org

# If DNS works but download fails, try specific version
elan toolchain install 4.6.0
```

#### **Error**: `no installed toolchains`
**Cause**: Elan installed but no Lean versions downloaded
**Solution**:
```bash
# Install specific version
elan toolchain install 4.6.0
elan default 4.6.0
```

### **2. Project Configuration Issues**

#### **Error**: `unknown package 'data'` or `unknown package 'Mathlib'`
**Cause**: Missing mathlib dependency or incorrect import paths
**Solution**:
```bash
# 1. Ensure mathlib is in lakefile.lean
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.0"

# 2. Install dependencies
lake update

# 3. Build project
lake build

# 4. Use correct import paths
import Mathlib.Data.Real.Basic  # Not: import data.real.basic
```

#### **Error**: `manifest out of date: git revision of dependency 'mathlib' changed`
**Cause**: mathlib version mismatch
**Solution**:
```bash
# Update mathlib to match Lean version
lake update mathlib
```

## 🔧 **Code Syntax Issues**

### **1. Import Path Problems**

#### **Error**: `unknown package 'Mathlib'`
**Solution**: Use correct import syntax for Lean 4.6.0
```lean
-- Correct imports
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Ring.Basic

-- NOT: import data.real.basic (old Lean 3 syntax)
```

### **2. Lambda Function Syntax**

#### **Error**: `unexpected token ','; expected '↦', '=>'`
**Cause**: Wrong lambda syntax for Lean 4.6.0
**Solution**:
```lean
-- Correct syntax for Lean 4.6.0
def function := λ x => -x

-- NOT: λ x, -x (old syntax)
-- NOT: λ x ↦ -x (alternative syntax)
```

### **3. Theorem Proof Syntax**

#### **Error**: `unknown identifier 'begin'`
**Cause**: Wrong proof syntax for Lean 4.6.0
**Solution**:
```lean
-- Correct syntax for simple proofs
theorem example : true :=
  rfl

-- For complex proofs, use proper tactic syntax
theorem complex_example (x : ℝ) : x + 0 = x :=
  by { rw add_zero }
```

#### **Error**: `invalid 'end', insufficient scopes`
**Cause**: Mismatched begin/end blocks
**Solution**: Use consistent proof syntax
```lean
-- Option 1: Simple proofs (recommended for basic cases)
theorem simple : true :=
  rfl

-- Option 2: Full tactic proofs
theorem complex : true :=
begin
  trivial
end
```

### **4. Type Instance Issues**

#### **Error**: `failed to synthesize instance HAdd state state ?m.1234`
**Cause**: Missing type class instances for operations
**Solution**: Ensure types have proper instances
```lean
-- Define types that inherit from proper classes
def time := ℝ  -- ℝ has all necessary instances
def state := ℝ

-- NOT: def time := Nat  -- Nat might lack some instances
```

#### **Error**: `failed to synthesize instance Neg state`
**Cause**: Missing negation instance
**Solution**: Use types with built-in instances
```lean
-- Use ℝ which has all arithmetic instances
def state := ℝ

-- Or define custom instances if needed
instance : Neg MyType := ⟨λ x => ...⟩
```

## 📦 **Package and Dependency Issues**

### **1. Mathlib Version Compatibility**

#### **Error**: `package configuration has errors` in mathlib
**Cause**: Version incompatibility between Lean and mathlib
**Solution**:
```lean
-- In lakefile.lean, use compatible version
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.0"

-- NOT: require mathlib from git "..." @ "stable"
```

### **2. Build System Issues**

#### **Error**: `unknown command 'list'` for lake
**Cause**: Different Lake version syntax
**Solution**: Check available commands
```bash
# Check Lake version
lake --version

# Check available commands
lake --help

# Use correct commands for your version
lake build
lake update
```

## 🎯 **Common Mathematical Issues**

### **1. Real Number Operations**

#### **Error**: `unsolved goals ⊢ 0 < 0.2`
**Cause**: Complex tactic issues with norm_num
**Solution**: Use simpler proofs
```lean
-- Simple approach
def example : simple_langevin_equation :=
{ variance := 0.2,
  variance_positive := by { exact (by { norm_num } : 0.2 > 0) } }

-- Or use known theorems
variance_positive := by { exact zero_lt_two }
```

### **2. Vector Operations**

#### **Error**: `failed to synthesize instance` for vector operations
**Cause**: Missing vector type class instances
**Solution**: Use proper vector definitions
```lean
-- Correct vector definition
def vector_state := Fin dimension → ℝ

-- Vector operations
def vector_add (v1 v2 : vector_state) : vector_state :=
  λ i => v1 i + v2 i
```

## 🚀 **Best Practices for Lean 4.6.0**

### **1. Import Strategy**
```lean
-- Always use Mathlib prefix
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Ring.Basic
```

### **2. Proof Strategy**
```lean
-- Start with simple proofs
theorem simple : true :=
  rfl

-- Use tactics only when necessary
theorem complex : true :=
begin
  -- tactics here
end
```

### **3. Type Definitions**
```lean
-- Use ℝ for real numbers (has all instances)
def time := ℝ
def state := ℝ

-- Use Fin n → ℝ for vectors (inherits ℝ instances)
def vector_state := Fin dimension → ℝ
```

### **4. Project Structure**
```bash
# Always use Lake for project management
lake init
lake update
lake build

# Run proofs through Lake environment
lake env lean --run src/file.lean
```

## 🔍 **Debugging Steps**

### **1. When Code Won't Compile**
1. **Check imports** - Use Mathlib prefix
2. **Verify syntax** - Use correct lambda syntax (=>)
3. **Check types** - Ensure types have proper instances
4. **Use Lake** - Run through `lake env lean --run`

### **2. When Dependencies Won't Install**
1. **Check network** - Test basic connectivity
2. **Use specific versions** - Avoid 'stable' tags
3. **Clean and rebuild** - Remove .lake directory and retry
4. **Check compatibility** - Ensure Lean and mathlib versions match

### **3. When Proofs Won't Work**
1. **Start simple** - Use `rfl` for basic proofs
2. **Check types** - Ensure all types are properly defined
3. **Use Lake environment** - Run through project build system
4. **Simplify complexity** - Break complex proofs into simple parts

## 📚 **Resources**

### **Official Documentation**
- [Lean 4 Documentation](https://leanprover-community.github.io/)
- [Mathlib Overview](https://leanprover-community.github.io/mathlib-overview.html)
- [Lake Package Manager](https://github.com/leanprover/lake)

### **Community Resources**
- [Lean Community](https://github.com/leanprover-community)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [Mathlib GitHub](https://github.com/leanprover-community/mathlib4)

---

**Remember**: Lean 4.6.0 is stable and well-supported. Most issues are related to syntax changes from Lean 3 or dependency configuration. When in doubt, use the Lake environment and start with simple proofs! 