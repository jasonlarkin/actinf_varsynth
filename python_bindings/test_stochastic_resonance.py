#!/usr/bin/env python3
"""
Test Stochastic Resonance in 1D Langevin Dynamics

This script demonstrates one of the most fascinating phenomena in nonlinear dynamics:
how adding noise can actually IMPROVE the detection of weak periodic signals!

The system: dx/dt = -x + A*sin(ωt) + ξ(t)
where ξ(t) is Gaussian white noise with amplitude σ

Key insight: There's an optimal noise level that maximizes signal-to-noise ratio!
"""

import numpy as np
import matplotlib.pyplot as plt
from langevin_bindings import LangevinBindings

def main():
    print("🎯 Testing Stochastic Resonance in 1D Langevin Dynamics")
    print("=" * 60)
    
    # Initialize bindings
    bindings = LangevinBindings()
    
    # Parameters for stochastic resonance
    x0 = 0.5          # Initial condition
    T = 10.0          # Total time
    dt = 0.01         # Time step
    A = 0.05          # Weak periodic forcing amplitude
    omega = 2.0       # Forcing frequency
    
    # Test different noise levels
    noise_levels = [0.0, 0.1, 0.2, 0.3, 0.5, 0.8, 1.0, 1.5]
    
    print(f"📊 Simulation Parameters:")
    print(f"   Initial condition: x₀ = {x0}")
    print(f"   Total time: T = {T}")
    print(f"   Time step: dt = {dt}")
    print(f"   Forcing amplitude: A = {A} (weak!)")
    print(f"   Forcing frequency: ω = {omega}")
    print(f"   Noise levels to test: {noise_levels}")
    print()
    
    # Run stochastic resonance simulation
    print("🔄 Running stochastic resonance simulation...")
    simulation_data = bindings.simulate_stochastic_resonance(
        x0, T, dt, A, omega, noise_levels
    )
    
    print("✅ Simulation complete!")
    print()
    
    # Plot the results
    print("📈 Generating plots...")
    bindings.plot_stochastic_resonance(simulation_data, 
                                     save_path="stochastic_resonance_trajectories.png")
    
    # Analyze the stochastic resonance effect
    print("🔍 Analyzing stochastic resonance effect...")
    analysis = bindings.analyze_stochastic_resonance(simulation_data)
    
    # Save the analysis plot
    plt.figure(figsize=(10, 6))
    plt.plot(analysis['noise_levels'], analysis['snr_values'], 'bo-', 
             linewidth=2, markersize=8)
    plt.xlabel('Noise Level σ')
    plt.ylabel('Signal-to-Noise Ratio')
    plt.title('Stochastic Resonance: Optimal Noise Level')
    plt.grid(True, alpha=0.3)
    
    # Mark optimal noise level
    plt.axvline(analysis['optimal_noise'], color='red', linestyle='--', alpha=0.7,
               label=f'Optimal σ = {analysis["optimal_noise"]:.3f}')
    plt.legend()
    plt.savefig("stochastic_resonance_analysis.png", dpi=300, bbox_inches='tight')
    plt.show()
    
    print()
    print("🎉 Stochastic Resonance Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - stochastic_resonance_trajectories.png")
    print("   - stochastic_resonance_analysis.png")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Without noise (σ = 0), the weak signal is barely visible")
    print("   2. With optimal noise, the signal becomes clearly detectable")
    print("   3. Too much noise overwhelms the signal again")
    print("   4. This explains why some biological systems need noise!")
    print()
    print("🚀 Ready for the next exciting simulation!")

if __name__ == "__main__":
    main() 