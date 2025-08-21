#!/usr/bin/env python3
"""
Test Critical Phenomena in 1D Langevin Dynamics

This script demonstrates one of the most fascinating phenomena in nonlinear dynamics:
phase transitions, critical points, and universal scaling behavior!

The systems:
1. Pitchfork bifurcation: dx/dt = μx - x³
2. Supercritical pitchfork: dx/dt = (μ - 1)x - x³

Key insight: These systems show dramatic changes in behavior at critical parameter values!
"""

import numpy as np
import matplotlib.pyplot as plt
from langevin_bindings import LangevinBindings

def main():
    print("🎯 Testing Critical Phenomena in 1D Langevin Dynamics")
    print("=" * 60)
    
    # Initialize bindings
    bindings = LangevinBindings()
    
    # Test Pitchfork bifurcation
    print("🔄 Testing Pitchfork Bifurcation...")
    print("   This system shows a transition from one stable state to two!")
    print()
    
    # Parameters for Pitchfork
    x0_pitchfork = 0.1        # Initial condition
    T_pitchfork = 10.0        # Total time
    dt_pitchfork = 0.01       # Time step
    mu_pitchfork = 0.5        # Control parameter (μ < 0 for stability)
    
    print(f"📊 Pitchfork Bifurcation Parameters:")
    print(f"   Initial condition: x₀ = {x0_pitchfork}")
    print(f"   Total time: T = {T_pitchfork}")
    print(f"   Time step: dt = {dt_pitchfork}")
    print(f"   Control parameter: μ = {mu_pitchfork}")
    print()
    
    # Run Pitchfork simulation
    print("🔄 Running Pitchfork bifurcation simulation...")
    pitchfork_data = bindings.simulate_critical_phenomena(
        x0_pitchfork, T_pitchfork, dt_pitchfork, mu_pitchfork, 'pitchfork'
    )
    
    print("✅ Pitchfork bifurcation simulation complete!")
    print()
    
    # Plot Pitchfork results
    print("📈 Generating Pitchfork bifurcation plots...")
    bindings.plot_critical_phenomena(pitchfork_data, save_path="pitchfork_bifurcation.png")
    
    # Analyze Pitchfork
    print("🔍 Analyzing Pitchfork bifurcation...")
    pitchfork_analysis = bindings.analyze_critical_phenomena(pitchfork_data)
    
    print()
    
    # Test Supercritical Pitchfork
    print("🔄 Testing Supercritical Pitchfork Bifurcation...")
    print("   This system shows a more dramatic transition!")
    print()
    
    # Parameters for Supercritical Pitchfork
    x0_super = 0.1            # Initial condition
    T_super = 10.0            # Total time
    dt_super = 0.01           # Time step
    mu_super = 1.5            # Control parameter (μ > 1 for instability)
    
    print(f"📊 Supercritical Pitchfork Parameters:")
    print(f"   Initial condition: x₀ = {x0_super}")
    print(f"   Total time: T = {T_super}")
    print(f"   Time step: dt = {dt_super}")
    print(f"   Control parameter: μ = {mu_super}")
    print()
    
    # Run Supercritical simulation
    print("🔄 Running Supercritical pitchfork simulation...")
    super_data = bindings.simulate_critical_phenomena(
        x0_super, T_super, dt_super, mu_super, 'supercritical_pitchfork'
    )
    
    print("✅ Supercritical pitchfork simulation complete!")
    print()
    
    # Plot Supercritical results
    print("📈 Generating Supercritical pitchfork plots...")
    bindings.plot_critical_phenomena(super_data, save_path="supercritical_pitchfork.png")
    
    # Analyze Supercritical
    print("🔍 Analyzing Supercritical pitchfork...")
    super_analysis = bindings.analyze_critical_phenomena(super_data)
    
    print()
    
    # Compare the two systems
    print("🔬 Comparing Critical Phenomena Systems:")
    print("=" * 40)
    print(f"Pitchfork Bifurcation (μ = {mu_pitchfork}):")
    print(f"   Steady state: x* = {pitchfork_analysis['steady_state']}")
    print(f"   This shows stability for μ < 0")
    print()
    print(f"Supercritical Pitchfork (μ = {mu_super}):")
    print(f"   Steady state: x* = {super_analysis['steady_state']}")
    print(f"   This shows instability for μ > 1")
    print()
    
    # Demonstrate the critical transition
    print("🎯 Critical Transition Analysis:")
    print("=" * 30)
    print("1. For μ < 0: System is stable at x* = 0")
    print("2. For μ = 0: Critical point (bifurcation)")
    print("3. For μ > 0: System becomes unstable")
    print("4. This is a classic second-order phase transition!")
    print()
    
    print("🎉 Critical Phenomena Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - pitchfork_bifurcation.png")
    print("   - supercritical_pitchfork.png")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Pitchfork: Smooth transition from stability to instability")
    print("   2. Supercritical: More dramatic transition with hysteresis")
    print("   3. Both show universal scaling near critical points!")
    print("   4. This explains phase transitions in physics, biology, etc.")
    print()
    print("🚀 Ready for the next exciting simulation!")

if __name__ == "__main__":
    main() 