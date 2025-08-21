#!/usr/bin/env python3
"""
Test Limit Cycles in 1D Langevin Dynamics

This script demonstrates one of the most fascinating phenomena in nonlinear dynamics:
self-sustaining oscillations that emerge from the system's own dynamics!

The systems:
1. Van der Pol oscillator: d²x/dt² + μ(1-x²)dx/dt + x = 0
2. Hopf bifurcation: dx/dt = μx - x³ - y, dy/dt = x + μy - y³

Key insight: These systems can oscillate indefinitely without external forcing!
"""

import numpy as np
import matplotlib.pyplot as plt
from langevin_bindings import LangevinBindings

def main():
    print("🎯 Testing Limit Cycles in 1D Langevin Dynamics")
    print("=" * 60)
    
    # Initialize bindings
    bindings = LangevinBindings()
    
    # Test Van der Pol oscillator
    print("🔄 Testing Van der Pol Oscillator...")
    print("   This system has self-sustaining oscillations!")
    print()
    
    # Parameters for Van der Pol
    x0_vdp = 1.0          # Initial position
    dx0_vdp = 0.0         # Initial velocity
    T_vdp = 20.0          # Total time (longer to see limit cycle)
    dt_vdp = 0.01         # Time step
    mu_vdp = 2.0          # Control parameter (μ > 0 for oscillations)
    
    print(f"📊 Van der Pol Parameters:")
    print(f"   Initial position: x₀ = {x0_vdp}")
    print(f"   Initial velocity: dx₀/dt = {dx0_vdp}")
    print(f"   Total time: T = {T_vdp}")
    print(f"   Time step: dt = {dt_vdp}")
    print(f"   Control parameter: μ = {mu_vdp}")
    print()
    
    # Run Van der Pol simulation
    print("🔄 Running Van der Pol simulation...")
    vdp_data = bindings.simulate_limit_cycle(
        x0_vdp, dx0_vdp, T_vdp, dt_vdp, mu_vdp, 'van_der_pol'
    )
    
    print("✅ Van der Pol simulation complete!")
    print()
    
    # Plot Van der Pol results
    print("📈 Generating Van der Pol plots...")
    bindings.plot_limit_cycle(vdp_data, save_path="van_der_pol_limit_cycle.png")
    
    # Analyze Van der Pol
    print("🔍 Analyzing Van der Pol limit cycle...")
    vdp_analysis = bindings.analyze_limit_cycle(vdp_data)
    
    print()
    
    # Test Hopf bifurcation system
    print("🔄 Testing Hopf Bifurcation System...")
    print("   This system shows a transition to oscillations!")
    print()
    
    # Parameters for Hopf
    x0_hopf = 0.1         # Initial position
    dx0_hopf = 0.0        # Initial velocity
    T_hopf = 15.0         # Total time
    dt_hopf = 0.01        # Time step
    mu_hopf = 0.5         # Control parameter (μ > 0 for oscillations)
    
    print(f"📊 Hopf Bifurcation Parameters:")
    print(f"   Initial position: x₀ = {x0_hopf}")
    print(f"   Initial velocity: dx₀/dt = {dx0_hopf}")
    print(f"   Total time: T = {T_hopf}")
    print(f"   Time step: dt = {dt_hopf}")
    print(f"   Control parameter: μ = {mu_hopf}")
    print()
    
    # Run Hopf simulation
    print("🔄 Running Hopf bifurcation simulation...")
    hopf_data = bindings.simulate_limit_cycle(
        x0_hopf, dx0_hopf, T_hopf, dt_hopf, mu_hopf, 'hopf'
    )
    
    print("✅ Hopf bifurcation simulation complete!")
    print()
    
    # Plot Hopf results
    print("📈 Generating Hopf bifurcation plots...")
    bindings.plot_limit_cycle(hopf_data, save_path="hopf_bifurcation_limit_cycle.png")
    
    # Analyze Hopf
    print("🔍 Analyzing Hopf bifurcation limit cycle...")
    hopf_analysis = bindings.analyze_limit_cycle(hopf_data)
    
    print()
    
    # Compare the two systems
    print("🔬 Comparing Limit Cycle Systems:")
    print("=" * 40)
    print(f"Van der Pol (μ = {mu_vdp}):")
    print(f"   Period: {vdp_analysis['period']:.3f}")
    print(f"   Frequency: {vdp_analysis['frequency']:.3f}")
    print(f"   Amplitude: {vdp_analysis['amplitude']:.3f}")
    print(f"   Energy: {vdp_analysis['energy']:.3f}")
    print()
    print(f"Hopf Bifurcation (μ = {mu_hopf}):")
    print(f"   Period: {hopf_analysis['period']:.3f}")
    print(f"   Frequency: {hopf_analysis['frequency']:.3f}")
    print(f"   Amplitude: {hopf_analysis['amplitude']:.3f}")
    print(f"   Energy: {hopf_analysis['energy']:.3f}")
    print()
    
    print("🎉 Limit Cycle Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - van_der_pol_limit_cycle.png")
    print("   - hopf_bifurcation_limit_cycle.png")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Van der Pol: Self-sustaining oscillations with energy pumping")
    print("   2. Hopf: Smooth transition from fixed point to limit cycle")
    print("   3. Both systems oscillate indefinitely without external forcing!")
    print("   4. This explains biological rhythms, chemical oscillations, etc.")
    print()
    print("🚀 Ready for the next exciting simulation!")

if __name__ == "__main__":
    main() 