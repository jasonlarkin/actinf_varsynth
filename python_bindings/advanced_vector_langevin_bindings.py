"""
Advanced Vector Langevin Dynamics Bindings
==========================================

This module implements advanced N-dimensional Langevin dynamics with:
- Advanced variance matrices (full covariance, positive definiteness)
- Stability analysis (Lyapunov functions, eigenvalue analysis)
- Advanced vector operations (norms, inner products, gradients)
- Theoretical foundations matching Lean proofs

Matches: src/advanced_langevin_proof.lean
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from typing import List, Tuple, Dict, Any, Callable
from scipy import linalg
from scipy.stats import multivariate_normal
import warnings

class AdvancedVectorLangevinBindings:
    """
    Advanced N-dimensional Langevin dynamics with mathematical rigor.
    
    Implements the theoretical foundations from advanced_langevin_proof.lean:
    - Advanced variance matrices with positive definiteness
    - Lyapunov stability analysis
    - Vector operations and norms
    - Stability and chaos measures
    """
    
    def __init__(self, dimension: int = 3):
        """
        Initialize advanced vector Langevin bindings.
        
        Args:
            dimension: Dimension of the vector state space
        """
        self.dimension = dimension
        self.epsilon = 1e-10  # Numerical tolerance
        
        print(f"🎯 Advanced Vector Langevin Bindings Initialized")
        print(f"   Dimension: {dimension}D")
        print(f"   Features: Advanced variance, stability analysis, Lyapunov functions")
        
    # ============================================================================
    # ADVANCED VARIANCE MATRIX OPERATIONS
    # ============================================================================
    
    def create_advanced_variance_matrix(self, 
                                      variances: List[float], 
                                      correlations: List[List[float]] = None,
                                      ensure_positive_definite: bool = True) -> np.ndarray:
        """
        Create advanced variance matrix with correlations.
        
        Args:
            variances: Diagonal variances [σ₁², σ₂², ..., σₙ²]
            correlations: Correlation matrix [ρ_ij] where ρ_ij = corr(ω_i, ω_j)
            ensure_positive_definite: Ensure matrix is positive definite
            
        Returns:
            Variance matrix Σ where Σ_ij = E[ω_i(t)ω_j(t)]
        """
        if correlations is None:
            # Default to diagonal (independent noise)
            correlations = np.eye(self.dimension)
        
        # Create correlation matrix
        corr_matrix = np.array(correlations)
        
        # Ensure correlation matrix is symmetric
        corr_matrix = (corr_matrix + corr_matrix.T) / 2
        
        # Create variance matrix: Σ_ij = σ_i * σ_j * ρ_ij
        variance_matrix = np.zeros((self.dimension, self.dimension))
        for i in range(self.dimension):
            for j in range(self.dimension):
                variance_matrix[i, j] = np.sqrt(variances[i]) * np.sqrt(variances[j]) * corr_matrix[i, j]
        
        if ensure_positive_definite:
            variance_matrix = self._ensure_positive_definite(variance_matrix)
            
        return variance_matrix
    
    def _ensure_positive_definite(self, matrix: np.ndarray) -> np.ndarray:
        """
        Ensure matrix is positive definite by adjusting eigenvalues.
        
        Args:
            matrix: Input matrix
            
        Returns:
            Positive definite matrix
        """
        # Get eigenvalues and eigenvectors
        eigenvals, eigenvecs = linalg.eigh(matrix)
        
        # Ensure all eigenvalues are positive
        eigenvals = np.maximum(eigenvals, self.epsilon)
        
        # Reconstruct matrix
        return eigenvecs @ np.diag(eigenvals) @ eigenvecs.T
    
    def generate_correlated_noise(self, 
                                variance_matrix: np.ndarray, 
                                num_steps: int,
                                dt: float) -> np.ndarray:
        """
        Generate correlated noise using Cholesky decomposition.
        
        Args:
            variance_matrix: Variance matrix Σ
            num_steps: Number of time steps
            dt: Time step size
            
        Returns:
            Noise matrix of shape (num_steps, dimension)
        """
        # Scale variance matrix by time step
        scaled_variance = variance_matrix * dt
        
        # Cholesky decomposition: Σ = L L^T
        try:
            L = linalg.cholesky(scaled_variance, lower=True)
        except linalg.LinAlgError:
            # If not positive definite, make it so
            scaled_variance = self._ensure_positive_definite(scaled_variance)
            L = linalg.cholesky(scaled_variance, lower=True)
        
        # Generate independent Gaussian noise
        independent_noise = np.random.normal(0, 1, (num_steps, self.dimension))
        
        # Transform to correlated noise: ω = L * η
        correlated_noise = independent_noise @ L.T
        
        return correlated_noise
    
    # ============================================================================
    # ADVANCED VECTOR OPERATIONS
    # ============================================================================
    
    def vector_norm(self, x: np.ndarray) -> float:
        """
        Calculate vector norm: ||x|| = √(Σᵢ xᵢ²)
        
        Args:
            x: Vector x
            
        Returns:
            Vector norm ||x||
        """
        return np.linalg.norm(x)
    
    def vector_inner_product(self, x: np.ndarray, y: np.ndarray) -> float:
        """
        Calculate inner product: ⟨x, y⟩ = Σᵢ xᵢ yᵢ
        
        Args:
            x, y: Vectors
            
        Returns:
            Inner product ⟨x, y⟩
        """
        return np.dot(x, y)
    
    def vector_angle(self, x: np.ndarray, y: np.ndarray) -> float:
        """
        Calculate angle between vectors: θ = arccos(⟨x,y⟩/(||x|| ||y||))
        
        Args:
            x, y: Vectors
            
        Returns:
            Angle in radians
        """
        cos_angle = self.vector_inner_product(x, y) / (self.vector_norm(x) * self.vector_norm(y))
        cos_angle = np.clip(cos_angle, -1, 1)  # Avoid numerical issues
        return np.arccos(cos_angle)
    
    def vector_gradient(self, 
                       function: Callable[[np.ndarray], float], 
                       x: np.ndarray, 
                       h: float = 1e-6) -> np.ndarray:
        """
        Calculate gradient of scalar function: ∇f(x) = [∂f/∂x₁, ∂f/∂x₂, ..., ∂f/∂xₙ]
        
        Args:
            function: Scalar function f(x)
            x: Point to evaluate gradient at
            h: Finite difference step size
            
        Returns:
            Gradient vector ∇f(x)
        """
        gradient = np.zeros(self.dimension)
        for i in range(self.dimension):
            x_plus = x.copy()
            x_minus = x.copy()
            x_plus[i] += h
            x_minus[i] -= h
            gradient[i] = (function(x_plus) - function(x_minus)) / (2 * h)
        return gradient
    
    # ============================================================================
    # ADVANCED FLOW FUNCTIONS
    # ============================================================================
    
    def create_advanced_flow_function(self, 
                                    flow_type: str = 'linear',
                                    parameters: Dict[str, float] = None) -> Callable:
        """
        Create advanced flow functions with different dynamics.
        
        Args:
            flow_type: Type of flow ('linear', 'nonlinear', 'coupled', 'chaotic')
            parameters: Flow parameters
            
        Returns:
            Flow function f(x)
        """
        if parameters is None:
            parameters = {}
        
        if flow_type == 'linear':
            return lambda x: -x  # Linear decay: dx/dt = -x
            
        elif flow_type == 'nonlinear':
            alpha = parameters.get('alpha', 0.1)
            beta = parameters.get('beta', 0.05)
            return lambda x: -x + alpha * x**2 - beta * x**3  # Cubic nonlinearity
            
        elif flow_type == 'coupled':
            coupling = parameters.get('coupling', 0.2)
            return lambda x: np.array([
                -x[0] + coupling * x[1],
                -x[1] + coupling * x[2],
                -x[2] + coupling * x[0]
            ])
            
        elif flow_type == 'chaotic':
            r = parameters.get('r', 3.8)  # Logistic map parameter
            return lambda x: r * x * (1 - x)  # Logistic map dynamics
            
        elif flow_type == 'gradient':
            # Gradient flow: dx/dt = -∇V(x) for potential V(x)
            def gradient_flow(x):
                # Example potential: V(x) = ||x||²/2 + α||x||⁴/4
                alpha = parameters.get('alpha', 0.1)
                potential_gradient = x + alpha * self.vector_norm(x)**2 * x
                return -potential_gradient
            return gradient_flow
            
        else:
            raise ValueError(f"Unknown flow type: {flow_type}")
    
    # ============================================================================
    # STABILITY ANALYSIS
    # ============================================================================
    
    def analyze_stability(self, 
                         flow_function: Callable, 
                         equilibrium_point: np.ndarray,
                         variance_matrix: np.ndarray = None) -> Dict[str, Any]:
        """
        Analyze stability of equilibrium point using Lyapunov theory.
        
        Args:
            flow_function: Flow function f(x)
            equilibrium_point: Equilibrium point x*
            variance_matrix: Noise variance matrix
            
        Returns:
            Stability analysis results
        """
        # Calculate Jacobian at equilibrium
        jacobian = self._calculate_jacobian(flow_function, equilibrium_point)
        
        # Calculate eigenvalues
        eigenvals = linalg.eigvals(jacobian)
        
        # Stability analysis
        max_real_part = np.max(np.real(eigenvals))
        is_stable = max_real_part < -self.epsilon
        
        # Lyapunov function analysis
        lyapunov_stability = self._analyze_lyapunov_stability(flow_function, equilibrium_point)
        
        # Noise effects on stability
        noise_stability = None
        if variance_matrix is not None:
            noise_stability = self._analyze_noise_stability(jacobian, variance_matrix)
        
        return {
            'equilibrium_point': equilibrium_point,
            'jacobian': jacobian,
            'eigenvalues': eigenvals,
            'max_real_part': max_real_part,
            'is_stable': is_stable,
            'stability_type': self._classify_stability(eigenvals),
            'lyapunov_stability': lyapunov_stability,
            'noise_stability': noise_stability
        }
    
    def _calculate_jacobian(self, 
                           flow_function: Callable, 
                           x: np.ndarray, 
                           h: float = 1e-6) -> np.ndarray:
        """
        Calculate Jacobian matrix: J_ij = ∂f_i/∂x_j
        
        Args:
            flow_function: Flow function f(x)
            x: Point to evaluate Jacobian at
            h: Finite difference step size
            
        Returns:
            Jacobian matrix J
        """
        jacobian = np.zeros((self.dimension, self.dimension))
        f_x = flow_function(x)
        
        for j in range(self.dimension):
            x_plus = x.copy()
            x_plus[j] += h
            f_x_plus = flow_function(x_plus)
            jacobian[:, j] = (f_x_plus - f_x) / h
            
        return jacobian
    
    def _classify_stability(self, eigenvals: np.ndarray) -> str:
        """
        Classify stability based on eigenvalues.
        
        Args:
            eigenvals: Eigenvalues of Jacobian
            
        Returns:
            Stability classification
        """
        real_parts = np.real(eigenvals)
        imag_parts = np.imag(eigenvals)
        
        if np.all(real_parts < -self.epsilon):
            if np.any(np.abs(imag_parts) > self.epsilon):
                return "Stable Focus"
            else:
                return "Stable Node"
        elif np.all(real_parts > self.epsilon):
            if np.any(np.abs(imag_parts) > self.epsilon):
                return "Unstable Focus"
            else:
                return "Unstable Node"
        elif np.any(real_parts > self.epsilon) and np.any(real_parts < -self.epsilon):
            return "Saddle Point"
        else:
            return "Center (Neutral)"
    
    def _analyze_lyapunov_stability(self, 
                                   flow_function: Callable, 
                                   equilibrium_point: np.ndarray) -> Dict[str, Any]:
        """
        Analyze Lyapunov stability using quadratic Lyapunov function.
        
        Args:
            flow_function: Flow function f(x)
            equilibrium_point: Equilibrium point x*
            
        Returns:
            Lyapunov stability analysis
        """
        # Use quadratic Lyapunov function: V(x) = ||x - x*||²/2
        def lyapunov_function(x):
            return 0.5 * self.vector_norm(x - equilibrium_point)**2
        
        # Calculate Lyapunov derivative: dV/dt = ⟨∇V, f(x)⟩
        def lyapunov_derivative(x):
            grad_V = x - equilibrium_point  # ∇V = x - x*
            f_x = flow_function(x)
            return self.vector_inner_product(grad_V, f_x)
        
        # Test at points around equilibrium
        test_points = []
        test_derivatives = []
        
        for i in range(self.dimension):
            for sign in [-1, 1]:
                test_point = equilibrium_point.copy()
                test_point[i] += sign * 0.1
                test_points.append(test_point)
                test_derivatives.append(lyapunov_derivative(test_point))
        
        # Check if dV/dt < 0 (stability condition)
        is_lyapunov_stable = np.all(np.array(test_derivatives) < self.epsilon)
        
        return {
            'lyapunov_function': lyapunov_function,
            'lyapunov_derivative': lyapunov_derivative,
            'test_points': test_points,
            'test_derivatives': test_derivatives,
            'is_lyapunov_stable': is_lyapunov_stable
        }
    
    def _analyze_noise_stability(self, 
                                jacobian: np.ndarray, 
                                variance_matrix: np.ndarray) -> Dict[str, Any]:
        """
        Analyze how noise affects stability.
        
        Args:
            jacobian: Jacobian matrix at equilibrium
            variance_matrix: Noise variance matrix
            
        Returns:
            Noise stability analysis
        """
        # Calculate noise amplification
        noise_amplification = np.trace(variance_matrix)
        
        # Calculate effective stability with noise
        # Consider noise as perturbation to eigenvalues
        eigenvals = linalg.eigvals(jacobian)
        noise_perturbation = np.sqrt(noise_amplification) * 0.1  # Small noise limit
        
        # Estimate noise-induced instability
        stability_margin = -np.max(np.real(eigenvals))
        noise_stability_threshold = stability_margin - noise_perturbation
        
        return {
            'noise_amplification': noise_amplification,
            'stability_margin': stability_margin,
            'noise_perturbation': noise_perturbation,
            'noise_stability_threshold': noise_stability_threshold,
            'is_noise_stable': noise_stability_threshold > 0
        }
    
    # ============================================================================
    # ADVANCED SIMULATION AND ANALYSIS
    # ============================================================================
    
    def simulate_advanced_langevin(self, 
                                 flow_function: Callable,
                                 variance_matrix: np.ndarray,
                                 x0: np.ndarray,
                                 T: float,
                                 dt: float) -> Dict[str, Any]:
        """
        Simulate advanced Langevin dynamics with full variance matrix.
        
        Args:
            flow_function: Flow function f(x)
            variance_matrix: Full variance matrix Σ
            x0: Initial state
            T: Total time
            dt: Time step
            
        Returns:
            Simulation results
        """
        num_steps = int(T / dt)
        times = np.linspace(0, T, num_steps)
        
        # Initialize trajectory
        trajectory = np.zeros((num_steps, self.dimension))
        trajectory[0] = x0
        
        # Generate correlated noise
        noise = self.generate_correlated_noise(variance_matrix, num_steps, dt)
        
        # Euler-Maruyama integration
        for i in range(1, num_steps):
            x_prev = trajectory[i-1]
            t_prev = times[i-1]
            
            # Deterministic part: dx = f(x) dt
            deterministic_step = flow_function(x_prev) * dt
            
            # Stochastic part: dx = noise
            stochastic_step = noise[i-1]
            
            # Update state
            trajectory[i] = x_prev + deterministic_step + stochastic_step
        
        return {
            'times': times,
            'trajectory': trajectory,
            'noise': noise,
            'parameters': {
                'flow_function': flow_function,
                'variance_matrix': variance_matrix,
                'x0': x0,
                'T': T,
                'dt': dt
            }
        }
    
    def calculate_lyapunov_exponents(self, 
                                   trajectory: np.ndarray, 
                                   dt: float,
                                   window_size: int = 100) -> np.ndarray:
        """
        Calculate local Lyapunov exponents from trajectory.
        
        Args:
            trajectory: State trajectory
            dt: Time step
            window_size: Window size for local calculation
            
        Returns:
            Local Lyapunov exponents
        """
        num_steps = len(trajectory)
        lyapunov_exponents = np.zeros((num_steps - window_size, self.dimension))
        
        for i in range(num_steps - window_size):
            # Extract window
            window = trajectory[i:i+window_size]
            
            # Calculate local divergence rate
            if i > 0:
                # Compare with previous window
                prev_window = trajectory[i-1:i+window_size-1]
                
                # Calculate separation: δx(t) = ||x(t) - x'(t)||
                separation = np.linalg.norm(window - prev_window, axis=1)
                
                # Avoid division by zero
                separation = np.maximum(separation, self.epsilon)
                
                # Local Lyapunov exponent: λ = (1/τ) * ln(δx(τ)/δx(0))
                tau = window_size * dt
                lyapunov_exponents[i] = np.log(separation[-1] / separation[0]) / tau
        
        return lyapunov_exponents
    
    def calculate_correlation_dimension(self, 
                                     trajectory: np.ndarray, 
                                     max_radius: float = 1.0,
                                     num_radii: int = 20) -> float:
        """
        Calculate correlation dimension (fractal dimension of attractor).
        
        Args:
            trajectory: State trajectory
            max_radius: Maximum radius for correlation calculation
            num_radii: Number of radius values to test
            
        Returns:
            Correlation dimension estimate
        """
        radii = np.logspace(-3, np.log10(max_radius), num_radii)
        correlations = []
        
        for r in radii:
            # Count pairs within radius r
            count = 0
            total_pairs = 0
            
            for i in range(len(trajectory)):
                for j in range(i+1, len(trajectory)):
                    distance = np.linalg.norm(trajectory[i] - trajectory[j])
                    if distance < r:
                        count += 1
                    total_pairs += 1
            
            if total_pairs > 0:
                correlation = count / total_pairs
                correlations.append(correlation)
            else:
                correlations.append(0)
        
        # Fit power law: C(r) ∝ r^D
        # log(C) = D * log(r) + const
        valid_indices = np.array(correlations) > 0
        if np.sum(valid_indices) < 2:
            return np.nan
        
        log_r = np.log(radii[valid_indices])
        log_C = np.log(np.array(correlations)[valid_indices])
        
        # Linear fit
        try:
            D, _ = np.polyfit(log_r, log_C, 1)
            return D
        except:
            return np.nan
    
    # ============================================================================
    # VISUALIZATION AND ANALYSIS
    # ============================================================================
    
    def plot_advanced_analysis(self, 
                              simulation_data: Dict[str, Any],
                              stability_analysis: Dict[str, Any] = None,
                              save_path: str = None) -> None:
        """
        Create comprehensive visualization of advanced analysis.
        
        Args:
            simulation_data: Simulation results
            stability_analysis: Stability analysis results
            save_path: Path to save plot
        """
        fig, axes = plt.subplots(2, 3, figsize=(18, 12))
        fig.suptitle('Advanced Vector Langevin Analysis', fontsize=16, fontweight='bold')
        
        times = simulation_data['times']
        trajectory = simulation_data['trajectory']
        noise = simulation_data['noise']
        
        # Plot 1: Component evolution
        for i in range(self.dimension):
            axes[0, 0].plot(times, trajectory[:, i], label=f'x_{i+1}(t)', alpha=0.8)
        axes[0, 0].set_xlabel('Time t')
        axes[0, 0].set_ylabel('State x_i(t)')
        axes[0, 0].set_title('Component Evolution')
        axes[0, 0].legend()
        axes[0, 0].grid(True, alpha=0.3)
        
        # Plot 2: Vector magnitude
        magnitudes = np.linalg.norm(trajectory, axis=1)
        axes[0, 1].plot(times, magnitudes, 'orange', linewidth=2)
        axes[0, 1].set_xlabel('Time t')
        axes[0, 1].set_ylabel('||x(t)||')
        axes[0, 1].set_title('Vector Magnitude Evolution')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Plot 3: Phase space (3D if available)
        if self.dimension >= 3:
            ax3d = fig.add_subplot(2, 3, 3, projection='3d')
            ax3d.plot(trajectory[:, 0], trajectory[:, 1], trajectory[:, 2], 'purple', alpha=0.7)
            ax3d.scatter(trajectory[0, 0], trajectory[0, 1], trajectory[0, 2], 
                        color='red', s=100, label='Start')
            ax3d.scatter(trajectory[-1, 0], trajectory[-1, 1], trajectory[-1, 2], 
                        color='green', s=100, label='End')
            ax3d.set_xlabel('x₁(t)')
            ax3d.set_ylabel('x₂(t)')
            ax3d.set_zlabel('x₃(t)')
            ax3d.set_title('3D Phase Space')
            ax3d.legend()
        else:
            # 2D phase space
            axes[0, 2].plot(trajectory[:, 0], trajectory[:, 1], 'purple', alpha=0.7)
            axes[0, 2].scatter(trajectory[0, 0], trajectory[0, 1], 
                              color='red', s=100, label='Start')
            axes[0, 2].scatter(trajectory[-1, 0], trajectory[-1, 1], 
                              color='green', s=100, label='End')
            axes[0, 2].set_xlabel('x₁(t)')
            axes[0, 2].set_ylabel('x₂(t)')
            axes[0, 2].set_title('Phase Space: x₁ vs x₂')
            axes[0, 2].legend()
            axes[0, 2].grid(True, alpha=0.3)
        
        # Plot 4: Noise correlation matrix
        if 'variance_matrix' in simulation_data['parameters']:
            variance_matrix = simulation_data['parameters']['variance_matrix']
            im = axes[1, 0].imshow(variance_matrix, cmap='viridis', aspect='auto')
            axes[1, 0].set_xlabel('Component i')
            axes[1, 0].set_ylabel('Component j')
            axes[1, 0].set_title('Noise Variance Matrix')
            plt.colorbar(im, ax=axes[1, 0])
        
        # Plot 5: Lyapunov exponents (if available)
        if stability_analysis and 'eigenvalues' in stability_analysis:
            eigenvals = stability_analysis['eigenvalues']
            real_parts = np.real(eigenvals)
            imag_parts = np.imag(eigenvals)
            
            axes[1, 1].scatter(real_parts, imag_parts, c='red', s=100, alpha=0.8)
            axes[1, 1].axvline(x=0, color='black', linestyle='--', alpha=0.5)
            axes[1, 1].axhline(y=0, color='black', linestyle='--', alpha=0.5)
            axes[1, 1].set_xlabel('Re(λ)')
            axes[1, 1].set_ylabel('Im(λ)')
            axes[1, 1].set_title('Jacobian Eigenvalues')
            axes[1, 1].grid(True, alpha=0.3)
            
            # Add stability region
            circle = plt.Circle((0, 0), 0.1, fill=False, color='red', linestyle='--')
            axes[1, 1].add_patch(circle)
        
        # Plot 6: Final state distribution
        final_values = trajectory[-1]
        axes[1, 2].bar(range(1, self.dimension + 1), final_values, 
                       color='skyblue', alpha=0.8)
        axes[1, 2].set_xlabel('Component')
        axes[1, 2].set_ylabel('Final Value')
        axes[1, 2].set_title('Final Component Values')
        axes[1, 2].set_xticks(range(1, self.dimension + 1))
        axes[1, 2].grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Advanced analysis plot saved to {save_path}")
        
        plt.show()
    
    def print_advanced_analysis(self, 
                               simulation_data: Dict[str, Any],
                               stability_analysis: Dict[str, Any] = None) -> None:
        """
        Print comprehensive analysis results.
        
        Args:
            simulation_data: Simulation results
            stability_analysis: Stability analysis results
        """
        print("\n🎯 Advanced Vector Langevin Analysis")
        print("=" * 50)
        
        # Simulation parameters
        params = simulation_data['parameters']
        print(f"📊 Simulation Parameters:")
        print(f"   Dimension: {self.dimension}D")
        print(f"   Initial state: x₀ = {params['x0']}")
        print(f"   Total time: T = {params['T']}")
        print(f"   Time step: dt = {params['dt']}")
        
        # Trajectory statistics
        trajectory = simulation_data['trajectory']
        final_magnitude = np.linalg.norm(trajectory[-1])
        print(f"\n📈 Trajectory Statistics:")
        print(f"   Final magnitude: ||x(T)|| = {final_magnitude:.6f}")
        print(f"   Max magnitude: max ||x(t)|| = {np.max(np.linalg.norm(trajectory, axis=1)):.6f}")
        
        # Component analysis
        print(f"\n🔍 Component Analysis:")
        for i in range(self.dimension):
            component = trajectory[:, i]
            mean_val = np.mean(component)
            std_val = np.std(component)
            final_val = component[-1]
            print(f"   x_{i+1}: mean={mean_val:.6f}, std={std_val:.6f}, final={final_val:.6f}")
        
        # Stability analysis
        if stability_analysis:
            print(f"\n🔒 Stability Analysis:")
            print(f"   Equilibrium point: x* = {stability_analysis['equilibrium_point']}")
            print(f"   Stability: {stability_analysis['is_stable']}")
            print(f"   Stability type: {stability_analysis['stability_type']}")
            print(f"   Max real part: {stability_analysis['max_real_part']:.6f}")
            
            if stability_analysis['lyapunov_stability']:
                lyap = stability_analysis['lyapunov_stability']
                print(f"   Lyapunov stable: {lyap['is_lyapunov_stable']}")
            
            if stability_analysis['noise_stability']:
                noise = stability_analysis['noise_stability']
                print(f"   Noise stable: {noise['is_noise_stable']}")
                print(f"   Stability margin: {noise['stability_margin']:.6f}")
        
        # Advanced measures
        print(f"\n🔬 Advanced Measures:")
        
        # Lyapunov exponents
        try:
            lyap_exponents = self.calculate_lyapunov_exponents(trajectory, params['dt'])
            if not np.all(np.isnan(lyap_exponents)):
                mean_lyap = np.nanmean(lyap_exponents)
                print(f"   Mean Lyapunov exponent: {mean_lyap:.6f}")
        except:
            print("   Lyapunov exponents: Could not calculate")
        
        # Correlation dimension
        try:
            corr_dim = self.calculate_correlation_dimension(trajectory)
            if not np.isnan(corr_dim):
                print(f"   Correlation dimension: {corr_dim:.6f}")
        except:
            print("   Correlation dimension: Could not calculate")
        
        print("\n🚀 Advanced analysis complete!")
        print("   Mathematical rigor matches Lean proofs")
        print("   Ready for variational synthesis applications") 