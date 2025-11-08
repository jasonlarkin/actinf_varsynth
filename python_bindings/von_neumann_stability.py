#!/usr/bin/env python3
"""
Von Neumann Stability Analysis for Langevin Equations
====================================================

This module implements von Neumann stability analysis to address the
"no proof of stability" limitation identified in our project.

Addresses:
- Numerical stability of integration schemes
- Stability bounds for different time steps
- Rigorous stability analysis for our dx/dt = -x + 0.1 system
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict, Any

class VonNeumannStability:
    """
    Von Neumann stability analysis for differential equations.
    
    Tests numerical stability under different integration schemes:
    - Explicit Euler
    - Implicit Euler  
    - Trapezoidal
    - RK4
    """
    
    def __init__(self):
        """Initialize von Neumann stability analyzer."""
        self.schemes = ['explicit_euler', 'implicit_euler', 'trapezoidal', 'rk4']
        
    def amplification_factor(self, scheme: str, lambda_val: complex, dt: float) -> complex:
        """
        Calculate amplification factor G(λ, dt) for given scheme.
        
        Args:
            scheme: Integration scheme name
            lambda_val: Eigenvalue of the system
            dt: Time step size
            
        Returns:
            Amplification factor G(λ, dt)
        """
        if scheme == 'explicit_euler':
            return 1 + lambda_val * dt
        elif scheme == 'implicit_euler':
            return 1 / (1 - lambda_val * dt)
        elif scheme == 'trapezoidal':
            return (1 + lambda_val * dt / 2) / (1 - lambda_val * dt / 2)
        elif scheme == 'rk4':
            return (1 + lambda_val * dt + 
                   (lambda_val * dt)**2 / 2 + 
                   (lambda_val * dt)**3 / 6 + 
                   (lambda_val * dt)**4 / 24)
        else:
            raise ValueError(f"Unknown scheme: {scheme}")
    
    def is_stable(self, scheme: str, lambda_val: complex, dt: float) -> bool:
        """
        Check if scheme is stable for given eigenvalue and time step.
        
        Args:
            scheme: Integration scheme name
            lambda_val: Eigenvalue of the system
            dt: Time step size
            
        Returns:
            True if stable (|G| ≤ 1), False otherwise
        """
        G = self.amplification_factor(scheme, lambda_val, dt)
        return abs(G) <= 1
    
    def stability_region(self, scheme: str) -> float:
        """
        Get maximum stable time step for given scheme.
        
        Args:
            scheme: Integration scheme name
            
        Returns:
            Maximum stable time step
        """
        if scheme == 'explicit_euler':
            return 2.0  # Stable for dt ≤ 2
        elif scheme == 'implicit_euler':
            return np.inf  # Unconditionally stable
        elif scheme == 'trapezoidal':
            return np.inf  # Unconditionally stable
        elif scheme == 'rk4':
            return 2.78  # Approximate stability limit
        else:
            return 0.0
    
    def analyze_langevin_stability(self, dt: float) -> Dict[str, Any]:
        """
        Analyze stability of our Langevin equation dx/dt = -x + 0.1.
        
        Args:
            dt: Time step size
            
        Returns:
            Stability analysis results
        """
        # Our system has eigenvalue λ = -1 (stable continuous system)
        lambda_val = -1.0
        
        results = {}
        for scheme in self.schemes:
            G = self.amplification_factor(scheme, lambda_val, dt)
            stable = self.is_stable(scheme, lambda_val, dt)
            max_dt = self.stability_region(scheme)
            
            results[scheme] = {
                'amplification_factor': G,
                'magnitude': abs(G),
                'is_stable': stable,
                'max_stable_dt': max_dt,
                'stability_margin': max_dt - dt if max_dt != np.inf else np.inf
            }
        
        return results
    
    def plot_stability_regions(self, lambda_vals: List[complex], dt_max: float = 3.0):
        """
        Plot stability regions for different schemes.
        
        Args:
            lambda_vals: List of eigenvalues to test
            dt_max: Maximum time step to plot
        """
        dt_vals = np.linspace(0.01, dt_max, 100)
        
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        fig.suptitle('Von Neumann Stability Regions for Different Integration Schemes', fontsize=16)
        
        for i, scheme in enumerate(self.schemes):
            row, col = i // 2, i % 2
            ax = axes[row, col]
            
            # Calculate stability for each eigenvalue and time step
            stability_matrix = np.zeros((len(lambda_vals), len(dt_vals)))
            
            for j, lambda_val in enumerate(lambda_vals):
                for k, dt in enumerate(dt_vals):
                    stable = self.is_stable(scheme, lambda_val, dt)
                    stability_matrix[j, k] = 1 if stable else 0
            
            # Plot stability region
            im = ax.imshow(stability_matrix, cmap='RdYlGn', aspect='auto',
                          extent=[dt_vals[0], dt_vals[-1], 0, len(lambda_vals)-1])
            
            ax.set_xlabel('Time Step dt')
            ax.set_ylabel('Eigenvalue Index')
            ax.set_title(f'{scheme.replace("_", " ").title()}')
            
            # Add colorbar
            plt.colorbar(im, ax=ax, label='Stable (1) / Unstable (0)')
        
        plt.tight_layout()
        return fig
    
    def plot_amplification_factors(self, dt_vals: List[float]):
        """
        Plot amplification factors for our Langevin system.
        
        Args:
            dt_vals: Time step values to test
        """
        lambda_val = -1.0  # Our system eigenvalue
        
        fig, ax = plt.subplots(figsize=(10, 6))
        
        for scheme in self.schemes:
            G_vals = [self.amplification_factor(scheme, lambda_val, dt) for dt in dt_vals]
            G_magnitudes = [abs(G) for G in G_vals]
            
            ax.plot(dt_vals, G_magnitudes, label=scheme.replace('_', ' ').title(), 
                   linewidth=2, marker='o', markersize=4)
        
        # Add stability threshold
        ax.axhline(y=1, color='red', linestyle='--', alpha=0.7, label='Stability Threshold |G| = 1')
        
        ax.set_xlabel('Time Step dt')
        ax.set_ylabel('|G(λ, dt)|')
        ax.set_title('Von Neumann Amplification Factors for dx/dt = -x + 0.1')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        return fig
    
    def print_stability_analysis(self, dt: float):
        """
        Print comprehensive stability analysis.
        
        Args:
            dt: Time step size to analyze
        """
        print("🔍 Von Neumann Stability Analysis")
        print("=" * 50)
        print(f"System: dx/dt = -x + 0.1")
        print(f"Eigenvalue: λ = -1 (stable continuous system)")
        print(f"Time step: dt = {dt}")
        print()
        
        results = self.analyze_langevin_stability(dt)
        
        print("📊 Stability Analysis Results:")
        print("-" * 30)
        
        for scheme, result in results.items():
            scheme_name = scheme.replace('_', ' ').title()
            status = "✅ STABLE" if result['is_stable'] else "❌ UNSTABLE"
            
            print(f"{scheme_name}:")
            print(f"  Amplification factor: G = {result['amplification_factor']:.6f}")
            print(f"  Magnitude: |G| = {result['magnitude']:.6f}")
            print(f"  Status: {status}")
            print(f"  Max stable dt: {result['max_stable_dt']}")
            print(f"  Stability margin: {result['stability_margin']}")
            print()
        
        # Overall assessment
        all_stable = all(result['is_stable'] for result in results.values())
        if all_stable:
            print("🎯 OVERALL ASSESSMENT: All schemes are stable for this time step!")
        else:
            print("⚠️  OVERALL ASSESSMENT: Some schemes are unstable for this time step.")
        
        print(f"\n📈 Stability Summary:")
        print(f"• Our choice dt = {dt} is {'very stable' if dt <= 0.1 else 'stable' if dt <= 1.0 else 'conditionally stable' if dt <= 2.0 else 'unstable'}")
        print(f"• Explicit Euler: Stable for dt ≤ 2.0")
        print(f"• Implicit Euler: Unconditionally stable")
        print(f"• Trapezoidal: Unconditionally stable")
        print(f"• RK4: Stable for dt ≤ 2.78")

def main():
    """Main function to demonstrate von Neumann stability analysis."""
    
    print("🎯 Von Neumann Stability Analysis for Langevin Equations")
    print("=" * 60)
    print("Addressing the 'no proof of stability' limitation")
    print()
    
    # Initialize analyzer
    analyzer = VonNeumannStability()
    
    # Test our current time step
    dt_current = 0.01
    print(f"🔍 Testing stability for our current time step: dt = {dt_current}")
    print()
    
    analyzer.print_stability_analysis(dt_current)
    
    # Test different time steps
    print("\n" + "="*60)
    print("🔍 Testing different time steps:")
    print()
    
    test_dts = [0.001, 0.01, 0.1, 1.0, 2.0, 3.0]
    for dt in test_dts:
        results = analyzer.analyze_langevin_stability(dt)
        stable_count = sum(1 for r in results.values() if r['is_stable'])
        print(f"dt = {dt:6.3f}: {stable_count}/{len(results)} schemes stable")
    
    # Create stability plots
    print("\n📊 Generating stability plots...")
    
    # Plot 1: Amplification factors
    dt_vals = np.linspace(0.01, 3.0, 100)
    fig1 = analyzer.plot_amplification_factors(dt_vals)
    fig1.savefig('von_neumann_amplification_factors.png', dpi=300, bbox_inches='tight')
    print("✅ Saved: von_neumann_amplification_factors.png")
    
    # Plot 2: Stability regions
    lambda_vals = [-1.0, -0.5, -2.0, -3.0]  # Different eigenvalues
    fig2 = analyzer.plot_stability_regions(lambda_vals)
    fig2.savefig('von_neumann_stability_regions.png', dpi=300, bbox_inches='tight')
    print("✅ Saved: von_neumann_stability_regions.png")
    
    print("\n🎉 Von Neumann stability analysis complete!")
    print("   This addresses the stability limitations in our project")

if __name__ == "__main__":
    main() 