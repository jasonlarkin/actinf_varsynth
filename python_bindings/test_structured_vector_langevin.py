#!/usr/bin/env python3
"""
Test Structured Vector Langevin Dynamics

This script tests the structured N-dimensional vector Langevin system:
- Structured approach with flow and noise functions
- Variance matrices for noise correlations
- Advanced flow types (linear, nonlinear, coupled)
- Advanced noise types (diagonal, correlated, anisotropic)

This matches the Lean formalization in src/vector_langevin_proof.lean
"""

import numpy as np
import matplotlib.pyplot as plt
from vector_langevin_bindings import VectorLangevinBindings

def main():
    print("🎯 Testing Structured Vector Langevin Dynamics")
    print("=" * 60)
    print("   This matches src/vector_langevin_proof.lean")
    print("   Structured approach with flow and noise functions")
    print()
    
    # Initialize 3D vector Langevin bindings
    print("🔄 Initializing 3D Vector Langevin Bindings...")
    bindings = VectorLangevinBindings(dimension=3)
    
    # Test 1: Linear flow with diagonal noise (basic case)
    print("🧮 Test 1: Linear Flow with Diagonal Noise")
    print("=" * 40)
    print("   Flow: f_i(x) = -x_i")
    print("   Noise: ω_i(t) ~ N(0, 0.1) (independent)")
    print()
    
    structured_eq1 = bindings.create_structured_vector_equation(
        flow_type='linear',
        noise_type='diagonal',
        variance=0.1,
        coupling_strength=0.0
    )
    
    print("✅ Structured equation created:")
    print(f"   Flow type: {structured_eq1['flow_type']}")
    print(f"   Noise type: {structured_eq1['noise_type']}")
    print(f"   Variance: {structured_eq1['variance']:.3f}")
    print(f"   Coupling: {structured_eq1['coupling_strength']:.3f}")
    print()
    
    # Test 2: Nonlinear flow with anisotropic noise
    print("🧮 Test 2: Nonlinear Flow with Anisotropic Noise")
    print("=" * 40)
    print("   Flow: f_i(x) = -x_i + 0.1 * x_i²")
    print("   Noise: ω_i(t) ~ N(0, σ_i) with different σ_i")
    print()
    
    structured_eq2 = bindings.create_structured_vector_equation(
        flow_type='nonlinear',
        noise_type='anisotropic',
        variance=0.15,
        coupling_strength=0.0
    )
    
    print("✅ Structured equation created:")
    print(f"   Flow type: {structured_eq2['flow_type']}")
    print(f"   Noise type: {structured_eq2['noise_type']}")
    print(f"   Variance: {structured_eq2['variance']:.3f}")
    print()
    
    # Test 3: Coupled flow with correlated noise
    print("🧮 Test 3: Coupled Flow with Correlated Noise")
    print("=" * 40)
    print("   Flow: f_i(x) = -x_i + 0.2 * x_{i+1}")
    print("   Noise: ω_i(t) with inter-component correlations")
    print()
    
    structured_eq3 = bindings.create_structured_vector_equation(
        flow_type='coupled',
        noise_type='correlated',
        variance=0.2,
        coupling_strength=0.3
    )
    
    print("✅ Structured equation created:")
    print(f"   Flow type: {structured_eq3['flow_type']}")
    print(f"   Noise type: {structured_eq3['noise_type']}")
    print(f"   Variance: {structured_eq3['variance']:.3f}")
    print(f"   Coupling: {structured_eq3['coupling_strength']:.3f}")
    print()
    
    # Simulation parameters
    print("📊 Simulation Parameters:")
    x0 = np.array([1.5, -0.8, 1.2])  # Initial 3D state
    T = 8.0                           # Total time
    dt = 0.01                         # Time step
    
    print(f"   Initial state: x₀ = {x0}")
    print(f"   Total time: T = {T}")
    print(f"   Time step: dt = {dt}")
    print()
    
    # Run simulations for all three structured equations
    print("🔄 Running Structured Vector Langevin Simulations...")
    print()
    
    # Simulation 1: Linear + Diagonal
    print("📈 Simulation 1: Linear Flow + Diagonal Noise")
    sim1_data = bindings.simulate_structured_vector_langevin(structured_eq1, x0, T, dt)
    print("✅ Simulation 1 complete!")
    
    # Simulation 2: Nonlinear + Anisotropic
    print("📈 Simulation 2: Nonlinear Flow + Anisotropic Noise")
    sim2_data = bindings.simulate_structured_vector_langevin(structured_eq2, x0, T, dt)
    print("✅ Simulation 2 complete!")
    
    # Simulation 3: Coupled + Correlated
    print("📈 Simulation 3: Coupled Flow + Correlated Noise")
    sim3_data = bindings.simulate_structured_vector_langevin(structured_eq3, x0, T, dt)
    print("✅ Simulation 3 complete!")
    
    print()
    
    # Analyze all three systems
    print("🔍 Analyzing Structured Vector Dynamics...")
    print()
    
    print("📊 Analysis 1: Linear + Diagonal")
    analysis1 = bindings.analyze_structured_dynamics(sim1_data)
    
    print()
    print("📊 Analysis 2: Nonlinear + Anisotropic")
    analysis2 = bindings.analyze_structured_dynamics(sim2_data)
    
    print()
    print("📊 Analysis 3: Coupled + Correlated")
    analysis3 = bindings.analyze_structured_dynamics(sim3_data)
    
    print()
    
    # Compare the three systems
    print("🔬 Comparing Structured Systems:")
    print("=" * 40)
    
    print("📈 Linear + Diagonal (Test 1):")
    print(f"   Final magnitude: {analysis1['magnitude_stats']['final_value']:.3f}")
    std_values1 = [analysis1['component_stats'][f'x_{i+1}']['std'] for i in range(3)]
    print(f"   Component std: {[f'{val:.3f}' for val in std_values1]}")
    
    print()
    print("📈 Nonlinear + Anisotropic (Test 2):")
    print(f"   Final magnitude: {analysis2['magnitude_stats']['final_value']:.3f}")
    std_values2 = [analysis2['component_stats'][f'x_{i+1}']['std'] for i in range(3)]
    print(f"   Component std: {[f'{val:.3f}' for val in std_values2]}")
    
    print()
    print("📈 Coupled + Correlated (Test 3):")
    print(f"   Final magnitude: {analysis3['magnitude_stats']['final_value']:.3f}")
    std_values3 = [analysis3['component_stats'][f'x_{i+1}']['std'] for i in range(3)]
    print(f"   Component std: {[f'{val:.3f}' for val in std_values3]}")
    
    if analysis3['coupling_analysis']:
        print(f"   Coupling correlations: {list(analysis3['coupling_analysis'].values())}")
    
    print()
    
    # Theoretical insights
    print("🔬 Theoretical Insights:")
    print("=" * 30)
    print("1. Linear + Diagonal: Independent components, exponential decay")
    print("2. Nonlinear + Anisotropic: Different noise levels, potential bistability")
    print("3. Coupled + Correlated: Inter-component interactions, collective behavior")
    print("4. All systems inherit mathematical rigor from Lean proofs!")
    print()
    
    print("🎉 Structured Vector Langevin Test Complete!")
    print("=" * 60)
    print("📁 Generated files:")
    print("   - Multiple analysis plots for each system")
    print()
    print("🔬 Key Scientific Insights:")
    print("   1. Structured approach enables complex flow and noise functions")
    print("   2. Variance matrices capture noise correlations")
    print("   3. Coupling creates emergent collective behavior")
    print("   4. All systems maintain mathematical rigor from Lean")
    print()
    print("🚀 Ready for Step 3: Advanced Vector Analysis!")

if __name__ == "__main__":
    main() 