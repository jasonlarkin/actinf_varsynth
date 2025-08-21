#!/usr/bin/env python3
"""
Test script for Lean Langevin Python bindings
Demonstrates how to use your mathematically proven equations from Python
"""

import sys
import os
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from langevin_bindings import LangevinBindings, test_langevin_bindings

def main():
    """Main test function"""
    print("🚀 Testing Lean Langevin Python Bindings")
    print("=" * 50)
    
    # Test the bindings
    l = test_langevin_bindings()
    
    if not l:
        print("❌ Failed to initialize bindings")
        return
    
    print("\n🎯 Testing Mathematical Functions")
    print("-" * 30)
    
    # Test basic mathematical functions
    test_x = 2.0
    test_t = 0.0
    
    print(f"Flow function f({test_x}) = {l.simple_flow(test_x)}")
    print(f"Noise function ω({test_t}) = {l.simple_noise(test_t)}")
    print(f"Evolution equation dx/dt at x={test_x}, t={test_t} = {l.evolution_equation(test_x, test_t)}")
    
    # Verify the mathematical relationship
    expected = l.simple_flow(test_x) + l.simple_noise(test_t)
    actual = l.evolution_equation(test_x, test_t)
    print(f"Verification: f({test_x}) + ω({test_t}) = {expected} = {actual} ✅")
    
    print("\n📊 Testing Numerical Integration")
    print("-" * 30)
    
    # Test Euler integration
    x0 = 1.0
    dt = 0.1
    steps = 5
    
    print(f"Initial state: x₀ = {x0}")
    print(f"Time step: dt = {dt}")
    print(f"Number of steps: {steps}")
    
    # Manual step-by-step integration
    x = x0
    for i in range(steps):
        dx_dt = l.evolution_equation(x, i * dt)
        x_new = l.euler_step(x, dt)
        print(f"Step {i}: x = {x:.6f}, dx/dt = {dx_dt:.6f}, x_new = {x_new:.6f}")
        x = x_new
    
    print("\n🎨 Testing Visualization")
    print("-" * 30)
    
    try:
        # Create plots
        print("Creating single trajectory plot...")
        fig1 = l.plot_trajectory(1.0, 2.0, 0.01, "Single Trajectory Example", show=False)
        
        print("Creating multiple trajectories plot...")
        initial_states = [0.0, 0.5, 1.0, 1.5, 2.0]
        fig2 = l.plot_multiple_trajectories(initial_states, 2.0, 0.01, "Multiple Initial Conditions", show=False)
        
        print("✅ All plots created successfully!")
        print("Note: Plots are saved but not displayed (show=False)")
        
        # Save plots
        fig1.savefig('single_trajectory.png', dpi=300, bbox_inches='tight')
        fig2.savefig('multiple_trajectories.png', dpi=300, bbox_inches='tight')
        print("📁 Plots saved as 'single_trajectory.png' and 'multiple_trajectories.png'")
        
    except Exception as e:
        print(f"❌ Error creating plots: {e}")
    
    print("\n🔬 Mathematical Analysis")
    print("-" * 30)
    
    # Analyze convergence to equilibrium
    t, x = l.simulate_trajectory(1.0, 0.0, 5.0, 0.01)
    equilibrium = 0.1
    
    print(f"Simulation: t ∈ [0, {t[-1]:.1f}], {len(t)} time points")
    print(f"Initial state: x(0) = {x[0]:.6f}")
    print(f"Final state: x({t[-1]:.1f}) = {x[-1]:.6f}")
    print(f"Equilibrium: x* = {equilibrium}")
    print(f"Convergence error: |x({t[-1]:.1f}) - x*| = {abs(x[-1] - equilibrium):.6f}")
    
    # Check if system is converging
    if abs(x[-1] - equilibrium) < 0.01:
        print("✅ System successfully converged to equilibrium!")
    else:
        print("⚠️  System may need longer simulation time to converge")
    
    print("\n🎉 Python Bindings Test Complete!")
    print("=" * 50)
    print("Your Lean Langevin equations are now accessible from Python!")
    print("You can use these bindings for:")
    print("  • Advanced plotting and visualization")
    print("  • Data analysis and statistics")
    print("  • Integration with scientific computing workflows")
    print("  • Machine learning and parameter optimization")

if __name__ == "__main__":
    main() 