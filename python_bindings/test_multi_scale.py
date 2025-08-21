#!/usr/bin/env python3
"""
Test Multi-Scale Dynamics in 1D Langevin Dynamics

This script demonstrates one of the most fascinating phenomena in nonlinear dynamics:
fast and slow variables that interact to create emergent behavior!

The system:
- Fast variable: dx_fast/dt = -x_fast/τ_fast + coupling * x_slow
- Slow variable: dx_slow/dt = -x_slow/τ_slow

Key insight: Fast variables can be "adiabatically eliminated" to reveal emergent dynamics on slow manifolds!
"""

import numpy as np
import matplotlib.pyplot as plt
from langevin_bindings import LangevinBindings

def main():
    print("🎯 Testing Multi-Scale Dynamics in 1D Langevin Dynamics")
    print("=" * 60)
    
    # Initialize bindings
    bindings = LangevinBindings()
    
    # Test Multi-Scale Dynamics
    print("🔄 Testing Multi-Scale Dynamics...")
    print("   This system has fast and slow variables that interact!")
    print()
    
    # Parameters for Multi-Scale
    x_fast0 = 1.0             # Initial fast variable
    x_slow0 = 0.5             # Initial slow variable
    T_multi = 15.0            # Total time (longer to see slow dynamics)
    dt_multi = 0.01           # Time step
    mu_multi = 1.0            # Control parameter
    tau_fast = 0.1            # Fast time constant (τ_fast << 1)
    tau_slow = 2.0            # Slow time constant (τ_slow >> 1)
    coupling = 0.3            # Coupling strength between variables
    
    print(f"📊 Multi-Scale Dynamics Parameters:")
    print(f"   Initial fast variable: x_fast₀ = {x_fast0}")
    print(f"   Initial slow variable: x_slow₀ = {x_slow0}")
    print(f"   Total time: T = {T_multi}")
    print(f"   Time step: dt = {dt_multi}")
    print(f"   Control parameter: μ = {mu_multi}")
    print(f"   Fast time constant: τ_fast = {tau_fast}")
    print(f"   Slow time constant: τ_slow = {tau_slow}")
    print(f"   Coupling strength: {coupling}")
    print()
    
    # Run Multi-Scale simulation
    print("🔄 Running Multi-Scale dynamics simulation...")
    multi_data = bindings.simulate_multi_scale(
        x_fast0, x_slow0, T_multi, dt_multi, mu_multi, tau_fast, tau_slow, coupling
    )
    
    print("✅ Multi-Scale dynamics simulation complete!")
    print()
    
    # Plot Multi-Scale results
    print("📈 Generating Multi-Scale dynamics plots...")
    bindings.plot_multi_scale(multi_data, save_path="multi_scale_dynamics.png")
    
    # Analyze Multi-Scale
    print("🔍 Analyzing Multi-Scale dynamics...")
    multi_analysis = bindings.analyze_multi_scale(multi_data)
    
    print()
    
    # Demonstrate adiabatic elimination
    print("🔬 Adiabatic Elimination Analysis:")
    print("=" * 30)
    print("1. Fast variable (τ_fast = 0.1): Relaxes quickly to quasi-equilibrium")
    print("2. Slow variable (τ_slow = 2.0): Evolves on slow manifold")
    print("3. Coupling (0.3): Creates emergent behavior")
    print("4. This is the foundation of multi-scale modeling!")
    print()
    
    # Show time scale separation
    print("⏱️ Time Scale Separation:")
    print("=" * 25)
    print(f"   τ_fast/τ_slow = {tau_fast/tau_slow:.3f} << 1")
    print(f"   This justifies adiabatic elimination!")
    print(f"   Fast variables can be treated as 'slaved' to slow ones")
    print()
    
    print("🎉 Multi-Scale Dynamics Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - multi_scale_dynamics.png")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Fast variables relax quickly to quasi-equilibrium")
    print("   2. Slow variables evolve on emergent slow manifolds")
    print("   3. Coupling creates complex emergent behavior!")
    print("   4. This explains neural dynamics, chemical reactions, etc.")
    print()
    print("🚀 Ready for the next exciting simulation!")

if __name__ == "__main__":
    main() 