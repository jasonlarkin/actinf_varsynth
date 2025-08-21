#!/usr/bin/env python3
"""
Test Chaotic Dynamics in 1D Langevin Dynamics

This script demonstrates one of the most fascinating phenomena in nonlinear dynamics:
sensitive dependence on initial conditions, strange attractors, and chaos!

The systems:
1. Logistic map: x_{n+1} = r * x_n * (1 - x_n)
2. Lorenz system: dx/dt = σ(y-x), dy/dt = x(ρ-z)-y, dz/dt = xy-βz

Key insight: Deterministic systems can exhibit unpredictable, chaotic behavior!
"""

import numpy as np
import matplotlib.pyplot as plt
from langevin_bindings import LangevinBindings

def main():
    print("🎯 Testing Chaotic Dynamics in 1D Langevin Dynamics")
    print("=" * 60)
    
    # Initialize bindings
    bindings = LangevinBindings()
    
    # Test Logistic Map (classic chaotic system)
    print("🔄 Testing Logistic Map...")
    print("   This system shows the route to chaos!")
    print()
    
    # Parameters for Logistic Map
    x0_logistic = 0.5           # Initial condition
    T_logistic = 100.0          # Total time (longer to see chaos)
    dt_logistic = 1.0           # Time step (discrete map)
    r_logistic = 3.8            # Control parameter (chaotic regime)
    
    print(f"📊 Logistic Map Parameters:")
    print(f"   Initial condition: x₀ = {x0_logistic}")
    print(f"   Total time: T = {T_logistic}")
    print(f"   Time step: dt = {dt_logistic}")
    print(f"   Control parameter: r = {r_logistic}")
    print(f"   Note: r > 3.57 leads to chaos!")
    print()
    
    # Run Logistic Map simulation
    print("🔄 Running Logistic map simulation...")
    logistic_data = bindings.simulate_chaotic_dynamics(
        x0_logistic, T_logistic, dt_logistic, r_logistic, 'logistic_map'
    )
    
    print("✅ Logistic map simulation complete!")
    print()
    
    # Plot Logistic Map results
    print("📈 Generating Logistic map plots...")
    bindings.plot_chaotic_dynamics(logistic_data, save_path="logistic_map_chaos.png")
    
    # Analyze Logistic Map
    print("🔍 Analyzing Logistic map chaos...")
    logistic_analysis = bindings.analyze_chaotic_dynamics(logistic_data)
    
    print()
    
    # Test Lorenz System (continuous chaotic system)
    print("🔄 Testing Lorenz System...")
    print("   This system shows the famous butterfly effect!")
    print()
    
    # Parameters for Lorenz
    x0_lorenz = 1.0             # Initial condition
    T_lorenz = 20.0             # Total time
    dt_lorenz = 0.01            # Time step
    r_lorenz = 28.0             # Control parameter (chaotic regime)
    
    print(f"📊 Lorenz System Parameters:")
    print(f"   Initial condition: x₀ = {x0_lorenz}")
    print(f"   Total time: T = {T_lorenz}")
    print(f"   Time step: dt = {dt_lorenz}")
    print(f"   Control parameter: ρ = {r_lorenz}")
    print(f"   Note: ρ > 24.74 leads to chaos!")
    print()
    
    # Run Lorenz simulation
    print("🔄 Running Lorenz system simulation...")
    lorenz_data = bindings.simulate_chaotic_dynamics(
        x0_lorenz, T_lorenz, dt_lorenz, r_lorenz, 'lorenz'
    )
    
    print("✅ Lorenz system simulation complete!")
    print()
    
    # Plot Lorenz results
    print("📈 Generating Lorenz system plots...")
    bindings.plot_chaotic_dynamics(lorenz_data, save_path="lorenz_system_chaos.png")
    
    # Analyze Lorenz
    print("🔍 Analyzing Lorenz system chaos...")
    lorenz_analysis = bindings.analyze_chaotic_dynamics(lorenz_data)
    
    print()
    
    # Demonstrate sensitive dependence on initial conditions
    print("🦋 Sensitive Dependence on Initial Conditions:")
    print("=" * 50)
    print("1. Logistic Map: Tiny changes in x₀ lead to completely different trajectories")
    print("2. Lorenz System: The famous 'butterfly effect'")
    print("3. Both systems are deterministic but unpredictable!")
    print("4. This is the essence of chaos theory!")
    print()
    
    # Compare the two systems
    print("🔬 Comparing Chaotic Systems:")
    print("=" * 40)
    print(f"Logistic Map (r = {r_logistic}):")
    print(f"   Lyapunov exponent: λ = {logistic_analysis['lyapunov_exponent']:.3f}")
    print(f"   Correlation dimension: D = {logistic_analysis['correlation_dimension']:.3f}")
    print(f"   Is chaotic: {logistic_analysis['is_chaotic']}")
    print()
    print(f"Lorenz System (ρ = {r_lorenz}):")
    print(f"   Lyapunov exponent: λ = {lorenz_analysis['lyapunov_exponent']:.3f}")
    print(f"   Correlation dimension: D = {lorenz_analysis['correlation_dimension']:.3f}")
    print(f"   Is chaotic: {lorenz_analysis['is_chaotic']}")
    print()
    
    print("🎉 Chaotic Dynamics Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - logistic_map_chaos.png")
    print("   - lorenz_system_chaos.png")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Deterministic systems can be unpredictable!")
    print("   2. Small changes in initial conditions lead to chaos")
    print("   3. Lyapunov exponents measure chaos quantitatively")
    print("   4. This explains weather, neural dynamics, etc.")
    print()
    print("🚀 Ready for N-dimensional dynamics in the next thread!")

if __name__ == "__main__":
    main() 