-- Simple test case for Lean compilation
-- This file tests basic functionality and compilation

-- Basic mathematical functions
def add_numbers (a b : Nat) : Nat := a + b

def multiply_numbers (a b : Nat) : Nat := a * b

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- Test some properties
def test_add : Prop := add_numbers 2 3 = 5
def test_multiply : Prop := multiply_numbers 4 5 = 20
def test_factorial : Prop := factorial 5 = 120

-- Main function for executable
def main : IO Unit := do
  IO.println "=== Lean Compilation Test ==="
  IO.println s!"2 + 3 = {add_numbers 2 3}"
  IO.println s!"4 * 5 = {multiply_numbers 4 5}"
  IO.println s!"5! = {factorial 5}"
  IO.println "Compilation successful! 🎉" 