#!/usr/bin/env python3
"""
Vector Langevin Dynamics Python Bindings

This module provides Python bindings for N-dimensional vector Langevin equations,
matching the Lean formalizations in src/simple_vector_proof.lean

The system: dx_i/dt = -x_i + ω_i(t) for i = 1, 2, 3
where ω_i(t) is noise in each dimension
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from typing import List, Tuple, Dict, Any

class VectorLangevinBindings:
    """Python bindings for N-dimensional vector Langevin dynamics"""
    
    def __init__(self, dimension: int = 3):
        """
        Initialize vector Langevin bindings
        
        Parameters:
        - dimension: Number of dimensions (default: 3)
        """
        self.dimension = dimension
        print(f"🎯 Initializing {dimension}D Vector Langevin Dynamics")
        print("=" * 50)
        
        # Core mathematical functions (matching Lean proofs)
        self.vector_flow = self._simple_vector_flow
        self.vector_noise = self._simple_vector_noise
        self.vector_evolution_equation = self._vector_evolution_equation
        
        # Vector operations (matching Lean definitions)
        self.vector_add = self._vector_add
        self.vector_scale = self._vector_scale
        
        # Simulation functions
        self.simulate_vector_langevin = self._simulate_vector_langevin
        self.plot_vector_trajectories = self._plot_vector_trajectories
        self.analyze_vector_dynamics = self._analyze_vector_dynamics
        
        print("✅ Vector Langevin bindings initialized!")
        print(f"   Dimension: {dimension}D")
        print(f"   Flow: dx_i/dt = -x_i + ω_i(t)")
        print(f"   Vector operations: addition, scaling")
        print()
    
    def _simple_vector_flow(self, x: np.ndarray) -> np.ndarray:
        """
        Vector flow function: f_i(x) = -x_i for each component
        
        Parameters:
        - x: Vector state of shape (dimension,)
        
        Returns:
        - Vector flow of shape (dimension,)
        """
        return -x
    
    def _simple_vector_noise(self, c: float, t: float) -> np.ndarray:
        """
        Vector noise function: ω_i(t) = c for each component
        
        Parameters:
        - c: Noise amplitude
        - t: Time
        
        Returns:
        - Vector noise of shape (dimension,)
        """
        return c * np.ones(self.dimension)
    
    def _vector_evolution_equation(self, x: np.ndarray, t: float) -> np.ndarray:
        """
        Vector evolution equation: dx_i/dt = f_i(x) + ω_i(t)
        
        Parameters:
        - x: Vector state
        - t: Time
        
        Returns:
        - Vector evolution of shape (dimension,)
        """
        return self.vector_add(self.vector_flow(x), self.vector_noise(0.1, t))
    
    def _vector_add(self, v1: np.ndarray, v2: np.ndarray) -> np.ndarray:
        """
        Vector addition: (v1 + v2)_i = v1_i + v2_i
        
        Parameters:
        - v1: First vector
        - v2: Second vector
        
        Returns:
        - Sum vector
        """
        return v1 + v2
    
    def _vector_scale(self, c: float, v: np.ndarray) -> np.ndarray:
        """
        Vector scaling: (c * v)_i = c * v_i
        
        Parameters:
        - c: Scalar
        - v: Vector
        
        Returns:
        - Scaled vector
        """
        return c * v
    
    def _simulate_vector_langevin(self, x0: np.ndarray, T: float, dt: float) -> Dict[str, Any]:
        """
        Simulate N-dimensional vector Langevin dynamics
        
        Parameters:
        - x0: Initial vector state of shape (dimension,)
        - T: Total time
        - dt: Time step
        
        Returns:
        - Dictionary with time, trajectories, and metadata
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        # Initialize trajectory array: (time_steps, dimension)
        x = np.zeros((time_steps, self.dimension))
        x[0] = x0
        
        # Euler integration for each time step
        for i in range(1, time_steps):
            # Current state
            x_current = x[i-1]
            
            # Evolution equation: dx/dt = -x + 0.1
            dx_dt = self.vector_evolution_equation(x_current, t[i-1])
            
            # Euler step: x[i] = x[i-1] + dt * dx_dt
            x[i] = x_current + dt * dx_dt
        
        return {
            'time': t,
            'trajectories': x,  # Shape: (time_steps, dimension)
            'dimension': self.dimension,
            'initial_state': x0,
            'total_time': T,
            'time_step': dt
        }
    
    def _plot_vector_trajectories(self, simulation_data: Dict[str, Any], save_path: str = None):
        """
        Plot N-dimensional vector trajectories
        
        Parameters:
        - simulation_data: Output from simulate_vector_langevin
        - save_path: Optional path to save plot
        """
        t = simulation_data['time']
        x = simulation_data['trajectories']
        dimension = simulation_data['dimension']
        
        # Create subplots
        if dimension == 3:
            fig = plt.figure(figsize=(15, 10))
            
            # Plot 1: 3D phase space trajectory
            ax1 = fig.add_subplot(2, 2, 1, projection='3d')
            ax1.plot(x[:, 0], x[:, 1], x[:, 2], 'b-', linewidth=2, alpha=0.8)
            ax1.plot(x[0, 0], x[0, 1], x[0, 2], 'ro', markersize=8, label='Start')
            ax1.plot(x[-1, 0], x[-1, 1], x[-1, 2], 'go', markersize=8, label='End')
            ax1.set_xlabel('x₁(t)')
            ax1.set_ylabel('x₂(t)')
            ax1.set_zlabel('x₃(t)')
            ax1.set_title('3D Phase Space Trajectory')
            ax1.legend()
            
            # Plot 2: Component-wise time series
            ax2 = fig.add_subplot(2, 2, 2)
            for i in range(dimension):
                ax2.plot(t, x[:, i], linewidth=2, label=f'x_{i+1}(t)')
            ax2.set_xlabel('Time t')
            ax2.set_ylabel('State x_i(t)')
            ax2.set_title('Component-wise Time Evolution')
            ax2.legend()
            ax2.grid(True, alpha=0.3)
            
            # Plot 3: 2D projections
            ax3 = fig.add_subplot(2, 2, 3)
            ax3.plot(x[:, 0], x[:, 1], 'purple', linewidth=2, alpha=0.8)
            ax3.plot(x[0, 0], x[0, 1], 'ro', markersize=8, label='Start')
            ax3.plot(x[-1, 0], x[-1, 1], 'go', markersize=8, label='End')
            ax3.set_xlabel('x₁(t)')
            ax3.set_ylabel('x₂(t)')
            ax3.set_title('2D Projection: x₁ vs x₂')
            ax3.legend()
            ax3.grid(True, alpha=0.3)
            
            # Plot 4: Vector magnitude over time
            ax4 = fig.add_subplot(2, 2, 4)
            vector_magnitude = np.sqrt(np.sum(x**2, axis=1))
            ax4.plot(t, vector_magnitude, 'orange', linewidth=2)
            ax4.set_xlabel('Time t')
            ax4.set_ylabel('||x(t)||')
            ax4.set_title('Vector Magnitude Evolution')
            ax4.grid(True, alpha=0.3)
            
        else:
            # Generic plotting for other dimensions
            fig, axes = plt.subplots(2, 2, figsize=(15, 10))
            
            # Component-wise time series
            for i in range(dimension):
                axes[0, 0].plot(t, x[:, i], linewidth=2, label=f'x_{i+1}(t)')
            axes[0, 0].set_xlabel('Time t')
            axes[0, 0].set_ylabel('State x_i(t)')
            axes[0, 0].set_title('Component-wise Time Evolution')
            axes[0, 0].legend()
            axes[0, 0].grid(True, alpha=0.3)
            
            # Vector magnitude
            vector_magnitude = np.sqrt(np.sum(x**2, axis=1))
            axes[0, 1].plot(t, vector_magnitude, 'orange', linewidth=2)
            axes[0, 1].set_xlabel('Time t')
            axes[0, 1].set_ylabel('||x(t)||')
            axes[0, 1].set_title('Vector Magnitude Evolution')
            axes[0, 1].grid(True, alpha=0.3)
            
            # Phase space projections
            if dimension >= 2:
                axes[1, 0].plot(x[:, 0], x[:, 1], 'purple', linewidth=2, alpha=0.8)
                axes[1, 0].set_xlabel('x₁(t)')
                axes[1, 0].set_ylabel('x₂(t)')
                axes[1, 0].set_title('2D Projection: x₁ vs x₂')
                axes[1, 0].grid(True, alpha=0.3)
            
            if dimension >= 3:
                axes[1, 1].plot(x[:, 1], x[:, 2], 'green', linewidth=2, alpha=0.8)
                axes[1, 1].set_xlabel('x₂(t)')
                axes[1, 1].set_ylabel('x₃(t)')
                axes[1, 1].set_title('2D Projection: x₂ vs x₃')
                axes[1, 1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Vector Langevin plot saved to {save_path}")
        
        plt.show()
    
    def _analyze_vector_dynamics(self, simulation_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Analyze N-dimensional vector dynamics
        
        Parameters:
        - simulation_data: Output from simulate_vector_langevin
        
        Returns:
        - Dictionary with analysis results
        """
        x = simulation_data['trajectories']
        t = simulation_data['time']
        dimension = simulation_data['dimension']
        
        # Calculate component-wise statistics
        component_stats = {}
        for i in range(dimension):
            trajectory = x[:, i]
            component_stats[f'x_{i+1}'] = {
                'mean': np.mean(trajectory),
                'std': np.std(trajectory),
                'min': np.min(trajectory),
                'max': np.max(trajectory),
                'final_value': trajectory[-1]
            }
        
        # Calculate vector magnitude statistics
        vector_magnitude = np.sqrt(np.sum(x**2, axis=1))
        magnitude_stats = {
            'mean': np.mean(vector_magnitude),
            'std': np.std(vector_magnitude),
            'min': np.min(vector_magnitude),
            'max': np.max(vector_magnitude),
            'final_value': vector_magnitude[-1]
        }
        
        # Calculate convergence rates (exponential decay)
        # For dx/dt = -x, solution is x(t) = x₀ * exp(-t)
        # So ln|x(t)| = ln|x₀| - t
        convergence_rates = {}
        for i in range(dimension):
            trajectory = x[:, i]
            # Skip if trajectory crosses zero
            if np.all(trajectory > 0) or np.all(trajectory < 0):
                log_trajectory = np.log(np.abs(trajectory))
                # Linear fit to ln|x(t)| vs t
                coeffs = np.polyfit(t, log_trajectory, 1)
                convergence_rates[f'x_{i+1}'] = -coeffs[0]  # Negative slope = decay rate
            else:
                convergence_rates[f'x_{i+1}'] = np.nan
        
        # Plot analysis
        fig, axes = plt.subplots(2, 2, figsize=(15, 10))
        
        # Plot 1: Component convergence
        axes[0, 0].plot(t, np.abs(x), alpha=0.7)
        axes[0, 0].set_xlabel('Time t')
        axes[0, 0].set_ylabel('|x_i(t)|')
        axes[0, 0].set_title('Component Convergence (log scale)')
        axes[0, 0].set_yscale('log')
        axes[0, 0].grid(True, alpha=0.3)
        
        # Plot 2: Vector magnitude convergence
        axes[0, 1].plot(t, vector_magnitude, 'orange', linewidth=2)
        axes[0, 1].set_xlabel('Time t')
        axes[0, 1].set_ylabel('||x(t)||')
        axes[0, 1].set_title('Vector Magnitude Convergence')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Plot 3: Component statistics
        component_names = list(component_stats.keys())
        final_values = [component_stats[name]['final_value'] for name in component_names]
        axes[1, 0].bar(component_names, final_values, alpha=0.7)
        axes[1, 0].set_xlabel('Component')
        axes[1, 0].set_ylabel('Final Value')
        axes[1, 0].set_title('Final Component Values')
        axes[1, 0].grid(True, alpha=0.3)
        
        # Plot 4: Convergence rates
        convergence_values = [convergence_rates[name] for name in component_names]
        valid_rates = [rate for rate in convergence_values if not np.isnan(rate)]
        if valid_rates:
            axes[1, 1].bar(component_names, convergence_values, alpha=0.7)
            axes[1, 1].set_xlabel('Component')
            axes[1, 1].set_ylabel('Convergence Rate')
            axes[1, 1].set_title('Component Convergence Rates')
            axes[1, 1].grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Print analysis results
        print(f"🎯 {dimension}D Vector Langevin Analysis:")
        print("=" * 40)
        print(f"   Dimension: {dimension}D")
        print(f"   Total time: {simulation_data['total_time']:.2f}")
        print(f"   Time step: {simulation_data['time_step']:.3f}")
        print()
        
        print("📊 Component Statistics:")
        for name, stats in component_stats.items():
            print(f"   {name}: mean={stats['mean']:.3f}, std={stats['std']:.3f}")
            print(f"      range=[{stats['min']:.3f}, {stats['max']:.3f}], final={stats['final_value']:.3f}")
        
        print()
        print("📈 Vector Magnitude:")
        print(f"   Mean: {magnitude_stats['mean']:.3f}")
        print(f"   Final: {magnitude_stats['final_value']:.3f}")
        
        print()
        print("🔬 Convergence Analysis:")
        for name, rate in convergence_rates.items():
            if not np.isnan(rate):
                print(f"   {name}: rate = {rate:.3f} (theoretical: 1.0)")
            else:
                print(f"   {name}: rate = N/A (crosses zero)")
        
        return {
            'component_stats': component_stats,
            'magnitude_stats': magnitude_stats,
            'convergence_rates': convergence_rates
        }

    # ============================================================================
    # STEP 2: STRUCTURED VECTOR LANGEVIN SYSTEM
    # This matches src/vector_langevin_proof.lean
    # ============================================================================
    
    def create_structured_vector_equation(self, flow_type='linear', noise_type='diagonal', 
                                        variance=0.1, coupling_strength=0.0):
        """
        Create a structured vector Langevin equation (matching Lean structure)
        
        Parameters:
        - flow_type: 'linear', 'nonlinear', 'coupled'
        - noise_type: 'diagonal', 'correlated', 'anisotropic'
        - variance: Noise variance
        - coupling_strength: Strength of inter-component coupling
        
        Returns:
        - Dictionary representing the structured equation
        """
        # Define flow functions (matching Lean definitions)
        if flow_type == 'linear':
            flow_func = lambda x: -x  # Linear flow: f_i(x) = -x_i
        elif flow_type == 'nonlinear':
            flow_func = lambda x: -x + 0.1 * x**2  # Nonlinear flow
        elif flow_type == 'coupled':
            flow_func = lambda x: -x + coupling_strength * np.roll(x, 1)  # Coupled flow
        else:
            flow_func = lambda x: -x
        
        # Define noise functions (matching Lean definitions)
        if noise_type == 'diagonal':
            noise_func = lambda t: np.sqrt(variance) * np.random.normal(0, 1, self.dimension)
        elif noise_type == 'correlated':
            # Correlated noise with covariance matrix
            noise_func = lambda t: self._generate_correlated_noise(variance, coupling_strength)
        elif noise_type == 'anisotropic':
            # Different variance for each component
            variances = variance * np.array([1.0, 1.5, 2.0])[:self.dimension]
            noise_func = lambda t: np.random.normal(0, np.sqrt(variances))
        else:
            noise_func = lambda t: np.sqrt(variance) * np.random.normal(0, 1, self.dimension)
        
        # Create variance matrix (matching Lean structure)
        if noise_type == 'diagonal':
            variance_matrix = variance * np.eye(self.dimension)
        elif noise_type == 'correlated':
            variance_matrix = self._create_correlation_matrix(variance, coupling_strength)
        else:
            variance_matrix = variance * np.eye(self.dimension)
        
        # Create structured equation (matching Lean vector_langevin_equation)
        structured_equation = {
            'flow': flow_func,
            'noise': noise_func,
            'variance_matrix': variance_matrix,
            'flow_type': flow_type,
            'noise_type': noise_type,
            'variance': variance,
            'coupling_strength': coupling_strength
        }
        
        return structured_equation
    
    def _generate_correlated_noise(self, variance, coupling):
        """Generate correlated noise with given variance and coupling"""
        # Create correlation matrix
        corr_matrix = self._create_correlation_matrix(variance, coupling)
        
        # Generate correlated noise using Cholesky decomposition
        try:
            L = np.linalg.cholesky(corr_matrix)
            uncorrelated_noise = np.random.normal(0, 1, self.dimension)
            correlated_noise = L @ uncorrelated_noise
            return correlated_noise
        except np.linalg.LinAlgError:
            # Fallback to diagonal if correlation matrix is not positive definite
            return np.sqrt(variance) * np.random.normal(0, 1, self.dimension)
    
    def _create_correlation_matrix(self, variance, coupling):
        """Create correlation matrix for noise"""
        # Start with diagonal matrix
        corr_matrix = variance * np.eye(self.dimension)
        
        # Add off-diagonal correlations
        for i in range(self.dimension):
            for j in range(self.dimension):
                if i != j:
                    corr_matrix[i, j] = coupling * variance
        
        # Ensure positive definiteness
        eigenvalues = np.linalg.eigvals(corr_matrix)
        if np.any(eigenvalues <= 0):
            # Adjust to make positive definite
            min_eigenvalue = np.min(eigenvalues)
            corr_matrix += (0.1 - min_eigenvalue) * np.eye(self.dimension)
        
        return corr_matrix
    
    def simulate_structured_vector_langevin(self, structured_equation, x0, T, dt):
        """
        Simulate structured vector Langevin dynamics
        
        Parameters:
        - structured_equation: Output from create_structured_vector_equation
        - x0: Initial vector state
        - T: Total time
        - dt: Time step
        
        Returns:
        - Dictionary with simulation results
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        # Initialize trajectory array
        x = np.zeros((time_steps, self.dimension))
        x[0] = x0
        
        # Get functions from structured equation
        flow_func = structured_equation['flow']
        noise_func = structured_equation['noise']
        
        # Euler integration with structured functions
        for i in range(1, time_steps):
            # Current state
            x_current = x[i-1]
            
            # Flow term: f(x)
            flow_term = flow_func(x_current)
            
            # Noise term: ω(t)
            noise_term = noise_func(t[i-1])
            
            # Evolution: dx/dt = f(x) + ω(t)
            dx_dt = flow_term + noise_term
            
            # Euler step
            x[i] = x_current + dt * dx_dt
        
        return {
            'time': t,
            'trajectories': x,
            'dimension': self.dimension,
            'initial_state': x0,
            'total_time': T,
            'time_step': dt,
            'structured_equation': structured_equation
        }
    
    def analyze_structured_dynamics(self, simulation_data):
        """
        Analyze structured vector Langevin dynamics
        
        Parameters:
        - simulation_data: Output from simulate_structured_vector_langevin
        
        Returns:
        - Dictionary with analysis results
        """
        x = simulation_data['trajectories']
        t = simulation_data['time']
        structured_equation = simulation_data['structured_equation']
        
        # Basic statistics (same as before)
        component_stats = {}
        for i in range(self.dimension):
            trajectory = x[:, i]
            component_stats[f'x_{i+1}'] = {
                'mean': np.mean(trajectory),
                'std': np.std(trajectory),
                'min': np.min(trajectory),
                'max': np.max(trajectory),
                'final_value': trajectory[-1]
            }
        
        # Vector magnitude statistics
        vector_magnitude = np.sqrt(np.sum(x**2, axis=1))
        magnitude_stats = {
            'mean': np.mean(vector_magnitude),
            'std': np.std(vector_magnitude),
            'min': np.min(vector_magnitude),
            'max': np.max(vector_magnitude),
            'final_value': vector_magnitude[-1]
        }
        
        # Advanced analysis for structured systems
        flow_type = structured_equation['flow_type']
        noise_type = structured_equation['noise_type']
        coupling = structured_equation['coupling_strength']
        
        # Coupling analysis
        coupling_analysis = {}
        if coupling > 0:
            # Analyze inter-component correlations
            for i in range(self.dimension):
                for j in range(i+1, self.dimension):
                    correlation = np.corrcoef(x[:, i], x[:, j])[0, 1]
                    coupling_analysis[f'corr_{i+1}_{j+1}'] = correlation
        
        # Stability analysis
        stability_analysis = {}
        for i in range(self.dimension):
            trajectory = x[:, i]
            # Calculate local Lyapunov exponent
            if len(trajectory) > 1:
                # Simple stability measure: rate of change
                changes = np.diff(trajectory)
                stability_measure = np.mean(np.abs(changes))
                stability_analysis[f'stability_{i+1}'] = stability_measure
        
        # Plot structured analysis
        self._plot_structured_analysis(simulation_data, component_stats, 
                                     magnitude_stats, coupling_analysis, 
                                     save_path=f"structured_{flow_type}_{noise_type}.png")
        
        # Print analysis results
        print(f"🎯 Structured {self.dimension}D Vector Langevin Analysis:")
        print("=" * 50)
        print(f"   Flow type: {flow_type}")
        print(f"   Noise type: {noise_type}")
        print(f"   Coupling strength: {coupling:.3f}")
        print(f"   Variance: {structured_equation['variance']:.3f}")
        print()
        
        print("📊 Component Statistics:")
        for name, stats in component_stats.items():
            print(f"   {name}: mean={stats['mean']:.3f}, std={stats['std']:.3f}")
            print(f"      final={stats['final_value']:.3f}")
        
        print()
        print("📈 Vector Magnitude:")
        print(f"   Mean: {magnitude_stats['mean']:.3f}")
        print(f"   Final: {magnitude_stats['final_value']:.3f}")
        
        if coupling_analysis:
            print()
            print("🔗 Coupling Analysis:")
            for name, corr in coupling_analysis.items():
                print(f"   {name}: correlation = {corr:.3f}")
        
        return {
            'component_stats': component_stats,
            'magnitude_stats': magnitude_stats,
            'coupling_analysis': coupling_analysis,
            'stability_analysis': stability_analysis
        }
    
    def _plot_structured_analysis(self, simulation_data, component_stats, 
                                 magnitude_stats, coupling_analysis, save_path=None):
        """Plot structured analysis results"""
        x = simulation_data['trajectories']
        t = simulation_data['time']
        structured_equation = simulation_data['structured_equation']
        
        fig, axes = plt.subplots(2, 3, figsize=(18, 12))
        
        # Plot 1: Component trajectories
        for i in range(self.dimension):
            axes[0, 0].plot(t, x[:, i], linewidth=2, label=f'x_{i+1}(t)')
        axes[0, 0].set_xlabel('Time t')
        axes[0, 0].set_ylabel('State x_i(t)')
        axes[0, 0].set_title(f'Component Evolution ({structured_equation["flow_type"]} flow)')
        axes[0, 0].legend()
        axes[0, 0].grid(True, alpha=0.3)
        
        # Plot 2: Vector magnitude
        vector_magnitude = np.sqrt(np.sum(x**2, axis=1))
        axes[0, 1].plot(t, vector_magnitude, 'orange', linewidth=2)
        axes[0, 1].set_xlabel('Time t')
        axes[0, 1].set_ylabel('||x(t)||')
        axes[0, 1].set_title('Vector Magnitude Evolution')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Plot 3: Phase space projection
        if self.dimension >= 2:
            axes[0, 2].plot(x[:, 0], x[:, 1], 'purple', linewidth=2, alpha=0.8)
            axes[0, 2].plot(x[0, 0], x[0, 1], 'ro', markersize=8, label='Start')
            axes[0, 2].plot(x[-1, 0], x[-1, 1], 'go', markersize=8, label='End')
            axes[0, 2].set_xlabel('x₁(t)')
            axes[0, 2].set_ylabel('x₂(t)')
            axes[0, 2].set_title('Phase Space: x₁ vs x₂')
            axes[0, 2].legend()
            axes[0, 2].grid(True, alpha=0.3)
        
        # Plot 4: Component statistics
        component_names = list(component_stats.keys())
        final_values = [component_stats[name]['final_value'] for name in component_names]
        axes[1, 0].bar(component_names, final_values, alpha=0.7)
        axes[1, 0].set_xlabel('Component')
        axes[1, 0].set_ylabel('Final Value')
        axes[1, 0].set_title('Final Component Values')
        axes[1, 0].grid(True, alpha=0.3)
        
        # Plot 5: Coupling analysis
        if coupling_analysis:
            coupling_names = list(coupling_analysis.keys())
            coupling_values = list(coupling_analysis.values())
            axes[1, 1].bar(coupling_names, coupling_values, alpha=0.7, color='green')
            axes[1, 1].set_xlabel('Component Pair')
            axes[1, 1].set_ylabel('Correlation')
            axes[1, 1].set_title('Inter-Component Correlations')
            axes[1, 1].grid(True, alpha=0.3)
        
        # Plot 6: Variance matrix visualization
        variance_matrix = structured_equation['variance_matrix']
        im = axes[1, 2].imshow(variance_matrix, cmap='viridis', aspect='auto')
        axes[1, 2].set_xlabel('Component i')
        axes[1, 2].set_ylabel('Component j')
        axes[1, 2].set_title('Noise Variance Matrix')
        plt.colorbar(im, ax=axes[1, 2])
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Structured analysis plot saved to {save_path}")
        
        plt.show() 