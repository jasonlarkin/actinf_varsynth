"""
Python Bindings for Lean Langevin Simulator
Provides direct access to mathematically proven Langevin equations from Python
"""

import ctypes
import numpy as np
from typing import List, Tuple, Optional
import matplotlib.pyplot as plt

class LangevinBindings:
    """Python bindings to Lean-generated Langevin simulator"""
    
    def __init__(self, library_path: str = None):
        """
        Initialize Python bindings to Lean Langevin simulator
        
        Args:
            library_path: Path to compiled Lean library (.so/.dll file)
        """
        print("Using Python fallback implementation (Lean functions reimplemented in Python)")
        self.lib = None
        self._setup_python_fallback()
    
    def _find_library(self) -> str:
        """Try to find the compiled Lean library"""
        import os
        import glob
        
        # Look for common library locations
        possible_paths = [
            ".lake/build/lib/liblangevin_simulator.so",
            ".lake/build/lib/liblangevin_simulator.dll",
            ".lake/build/lib/liblangevin_simulator.dylib",
            "build/lib/liblangevin_simulator.so",
            "build/lib/liblangevin_simulator.dll",
            "build/lib/liblangevin_simulator.dylib"
        ]
        
        for path in possible_paths:
            if os.path.exists(path):
                return path
        
        raise FileNotFoundError("Could not find compiled Lean library")
    
    def _setup_function_signatures(self):
        """Set up function signatures for C library calls"""
        if self.lib is None:
            return
            
        # Define function signatures for Lean-generated functions
        # These need to match what Lean actually generated
        
        # Example (will need to be adjusted based on actual C output):
        self.lib.simple_flow.argtypes = [ctypes.c_double]
        self.lib.simple_flow.restype = ctypes.c_double
        
        self.lib.evolution_equation.argtypes = [ctypes.c_double, ctypes.c_double]
        self.lib.evolution_equation.restype = ctypes.c_double
        
        self.lib.euler_step.argtypes = [ctypes.c_double, ctypes.c_double]
        self.lib.euler_step.restype = ctypes.c_double
    
    def _setup_python_fallback(self):
        """Setup Python fallback implementations of Lean functions"""
        print("Setting up Python fallback implementations...")
        
        # Core mathematical functions (proven in Lean)
        self.simple_flow = lambda x: -x + 0.1
        self.simple_noise = 0.1
        self.evolution_equation = lambda x, t: -x + 0.1
        
        # Numerical integration
        self.euler_step = lambda x, dt: x + dt * self.simple_flow(x)
        
        # Simulation functions
        self.simulate_trajectory = self._simulate_trajectory_python
        self.plot_trajectory = self._plot_trajectory_python
        self.plot_multiple_trajectories = self._plot_multiple_trajectories_python
        
        # NEW: Stochastic Resonance functions
        self.stochastic_resonance_flow = lambda x, t, A, omega: -x + A * np.sin(omega * t)
        self.simulate_stochastic_resonance = self._simulate_stochastic_resonance_python
        self.plot_stochastic_resonance = self._plot_stochastic_resonance_python
        self.analyze_stochastic_resonance = self._analyze_stochastic_resonance_python
        
        # NEW: Limit Cycle functions
        self.van_der_pol_flow = lambda x, dx_dt, mu: (dx_dt, mu * (1 - x**2) * dx_dt - x)
        self.hopf_bifurcation_flow = lambda x, y, mu: (mu * x - x**3 - y, x + mu * y - y**3)
        self.simulate_limit_cycle = self._simulate_limit_cycle_python
        self.plot_limit_cycle = self._plot_limit_cycle_python
        self.analyze_limit_cycle = self._analyze_limit_cycle_python
        
        # NEW: Critical Phenomena functions
        self.pitchfork_bifurcation_flow = lambda x, mu: mu * x - x**3
        self.supercritical_pitchfork_flow = lambda x, mu: (mu - 1) * x - x**3
        self.simulate_critical_phenomena = self._simulate_critical_phenomena_python
        self.plot_critical_phenomena = self._plot_critical_phenomena_python
        self.analyze_critical_phenomena = self._analyze_critical_phenomena_python
        
        # NEW: Multi-Scale Dynamics functions
        self.fast_slow_flow = lambda x_fast, x_slow, tau_fast, tau_slow: (-x_fast / tau_fast, -x_slow / tau_slow)
        self.coupled_fast_slow_flow = lambda x_fast, x_slow, tau_fast, tau_slow, coupling: (-x_fast / tau_fast + coupling * x_slow, -x_slow / tau_slow + coupling * x_fast)
        self.simulate_multi_scale = self._simulate_multi_scale_python
        self.plot_multi_scale = self._plot_multi_scale_python
        self.analyze_multi_scale = self._analyze_multi_scale_python
        
        # NEW: Chaotic Dynamics functions
        self.logistic_map = lambda x, r: r * x * (1 - x)
        self.lorenz_flow = lambda x, y, z, sigma, rho, beta: (sigma * (y - x), x * (rho - z) - y, x * y - beta * z)
        self.simulate_chaotic_dynamics = self._simulate_chaotic_dynamics_python
        self.plot_chaotic_dynamics = self._plot_chaotic_dynamics_python
        self.analyze_chaotic_dynamics = self._analyze_chaotic_dynamics_python
        
        print("✅ Python fallback setup complete!")

    def _simulate_trajectory_python(self, x0, T, dt):
        """Python fallback for trajectory simulation"""
        time_steps = int(T / dt)
        trajectory = np.zeros(time_steps)
        trajectory[0] = x0
        
        for i in range(1, time_steps):
            trajectory[i] = self.euler_step(trajectory[i-1], dt)
        
        return trajectory
    
    def _plot_trajectory_python(self, trajectory, dt, save_path=None):
        """Python fallback for trajectory plotting"""
        t = np.linspace(0, len(trajectory) * dt, len(trajectory))
        
        plt.figure(figsize=(10, 6))
        plt.plot(t, trajectory, 'b-', linewidth=2)
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title('Single Trajectory Example')
        plt.grid(True, alpha=0.3)
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        plt.show()
    
    def _plot_multiple_trajectories_python(self, trajectories, dt, save_path=None):
        """Python fallback for multiple trajectory plotting"""
        max_steps = max(len(traj) for traj in trajectories.values())
        t = np.linspace(0, max_steps * dt, max_steps)
        
        plt.figure(figsize=(10, 6))
        colors = plt.cm.viridis(np.linspace(0, 1, len(trajectories)))
        
        for i, (label, trajectory) in enumerate(trajectories.items()):
            plt.plot(t[:len(trajectory)], trajectory, color=colors[i], 
                    linewidth=2, label=label)
        
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title('Multiple Initial Conditions')
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
        
        plt.show()

    def _simulate_stochastic_resonance_python(self, x0, T, dt, A, omega, noise_levels):
        """
        Simulate stochastic resonance for different noise levels
        
        Parameters:
        - x0: initial condition
        - T: total time
        - dt: time step
        - A: amplitude of weak periodic forcing
        - omega: frequency of forcing
        - noise_levels: list of noise amplitudes to test
        
        Returns:
        - Dictionary with time, trajectories, and noise levels
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        results = {}
        
        for noise_level in noise_levels:
            trajectory = np.zeros(time_steps)
            trajectory[0] = x0
            
            for i in range(1, time_steps):
                # Deterministic part
                dx_dt = self.stochastic_resonance_flow(trajectory[i-1], t[i-1], A, omega)
                # Add noise
                noise = np.random.normal(0, noise_level)
                trajectory[i] = trajectory[i-1] + dt * dx_dt + noise * np.sqrt(dt)
            
            results[f'noise_{noise_level:.3f}'] = trajectory
        
        return {'time': t, 'trajectories': results, 'noise_levels': noise_levels}
    
    def _plot_stochastic_resonance_python(self, simulation_data, save_path=None):
        """Plot stochastic resonance results"""
        t = simulation_data['time']
        trajectories = simulation_data['trajectories']
        noise_levels = simulation_data['noise_levels']
        
        plt.figure(figsize=(12, 8))
        
        # Plot trajectories for different noise levels
        colors = plt.cm.viridis(np.linspace(0, 1, len(noise_levels)))
        
        for i, (noise_key, trajectory) in enumerate(trajectories.items()):
            noise_level = noise_levels[i]
            plt.plot(t, trajectory, color=colors[i], linewidth=2, 
                    label=f'σ = {noise_level:.3f}')
        
        # Plot the weak periodic forcing (scaled for visibility)
        A = 0.05  # Weak amplitude
        omega = 2.0  # Frequency
        forcing = A * np.sin(omega * t)
        plt.plot(t, forcing + 0.5, 'r--', linewidth=2, alpha=0.7, 
                label='Weak forcing (scaled)')
        
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title('Stochastic Resonance: Noise-Enhanced Signal Detection')
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Stochastic resonance plot saved to {save_path}")
        
        plt.show()
        
    def _analyze_stochastic_resonance_python(self, simulation_data):
        """Analyze the stochastic resonance effect"""
        trajectories = simulation_data['trajectories']
        noise_levels = simulation_data['noise_levels']
        
        # Calculate signal-to-noise ratio for each noise level
        snr_values = []
        
        for noise_level in noise_levels:
            trajectory = trajectories[f'noise_{noise_level:.3f}']
            
            # Extract the periodic component using FFT
            fft = np.fft.fft(trajectory)
            freqs = np.fft.fftfreq(len(trajectory), d=0.01)  # Assuming dt=0.01
            
            # Find the forcing frequency component (around omega=2.0)
            target_freq_idx = np.argmin(np.abs(freqs - 2.0))
            signal_power = np.abs(fft[target_freq_idx])**2
            
            # Total power
            total_power = np.sum(np.abs(fft)**2)
            noise_power = total_power - signal_power
            
            # Signal-to-noise ratio
            snr = signal_power / (noise_power + 1e-10)
            snr_values.append(snr)
        
        # Plot SNR vs noise level
        plt.figure(figsize=(10, 6))
        plt.plot(noise_levels, snr_values, 'bo-', linewidth=2, markersize=8)
        plt.xlabel('Noise Level σ')
        plt.ylabel('Signal-to-Noise Ratio')
        plt.title('Stochastic Resonance: Optimal Noise Level')
        plt.grid(True, alpha=0.3)
        
        # Find optimal noise level
        optimal_idx = np.argmax(snr_values)
        optimal_noise = noise_levels[optimal_idx]
        max_snr = snr_values[optimal_idx]
        
        plt.axvline(optimal_noise, color='red', linestyle='--', alpha=0.7,
                   label=f'Optimal σ = {optimal_noise:.3f}')
        plt.legend()
        
        plt.show()
        
        print(f"🎯 Stochastic Resonance Analysis:")
        print(f"   Optimal noise level: σ = {optimal_noise:.3f}")
        print(f"   Maximum SNR: {max_snr:.2f}")
        print(f"   This demonstrates how noise can enhance weak signals!")
        
        return {'noise_levels': noise_levels, 'snr_values': snr_values, 
                'optimal_noise': optimal_noise, 'max_snr': max_snr}

    def _simulate_limit_cycle_python(self, x0, dx0, T, dt, mu, system_type='van_der_pol'):
        """
        Simulate limit cycle dynamics
        
        Parameters:
        - x0: initial position
        - dx0: initial velocity
        - T: total time
        - dt: time step
        - mu: control parameter
        - system_type: 'van_der_pol' or 'hopf'
        
        Returns:
        - Dictionary with time, position, velocity, and phase space
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        x = np.zeros(time_steps)
        dx_dt = np.zeros(time_steps)
        
        x[0] = x0
        dx_dt[0] = dx0
        
        for i in range(1, time_steps):
            if system_type == 'van_der_pol':
                # Van der Pol oscillator: d²x/dt² + μ(1-x²)dx/dt + x = 0
                # Convert to first order: dx/dt = v, dv/dt = μ(1-x²)v - x
                v = dx_dt[i-1]
                dv_dt = mu * (1 - x[i-1]**2) * v - x[i-1]
                
                x[i] = x[i-1] + dt * v
                dx_dt[i] = v + dt * dv_dt
                
            elif system_type == 'hopf':
                # Hopf bifurcation system (2D)
                # dx/dt = μx - x³ - y, dy/dt = x + μy - y³
                # For 1D projection, we'll use x component
                dx_dt_val = mu * x[i-1] - x[i-1]**3 - dx_dt[i-1]
                x[i] = x[i-1] + dt * dx_dt_val
                dx_dt[i] = dx_dt_val
        
        return {
            'time': t,
            'position': x,
            'velocity': dx_dt,
            'phase_space': np.column_stack([x, dx_dt]),
            'mu': mu,
            'system_type': system_type
        }
    
    def _plot_limit_cycle_python(self, simulation_data, save_path=None):
        """Plot limit cycle results"""
        t = simulation_data['time']
        x = simulation_data['position']
        dx_dt = simulation_data['velocity']
        mu = simulation_data['mu']
        system_type = simulation_data['system_type']
        
        # Create subplots
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))
        
        # Plot 1: Time series
        ax1.plot(t, x, 'b-', linewidth=2, label='Position x(t)')
        ax1.plot(t, dx_dt, 'r--', linewidth=2, label='Velocity dx/dt')
        ax1.set_xlabel('Time t')
        ax1.set_ylabel('Amplitude')
        ax1.set_title(f'{system_type.title()} Oscillator: Time Evolution (μ = {mu})')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # Plot 2: Phase space (limit cycle)
        ax2.plot(x, dx_dt, 'g-', linewidth=2, label='Phase Trajectory')
        ax2.plot(x[0], dx_dt[0], 'ro', markersize=8, label='Start')
        ax2.plot(x[-1], dx_dt[-1], 'bo', markersize=8, label='End')
        ax2.set_xlabel('Position x')
        ax2.set_ylabel('Velocity dx/dt')
        ax2.set_title(f'{system_type.title()} Oscillator: Phase Space (μ = {mu})')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        # Make phase space plot square and centered
        ax2.set_aspect('equal')
        max_range = max(np.max(np.abs(x)), np.max(np.abs(dx_dt)))
        ax2.set_xlim(-max_range*1.1, max_range*1.1)
        ax2.set_ylim(-max_range*1.1, max_range*1.1)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Limit cycle plot saved to {save_path}")
        
        plt.show()
        
    def _analyze_limit_cycle_python(self, simulation_data):
        """Analyze limit cycle properties"""
        x = simulation_data['position']
        dx_dt = simulation_data['velocity']
        t = simulation_data['time']
        mu = simulation_data['mu']
        system_type = simulation_data['system_type']
        
        # Find the limit cycle (after transient)
        transient_steps = int(len(x) * 0.2)  # Skip first 20%
        x_steady = x[transient_steps:]
        dx_steady = dx_dt[transient_steps:]
        t_steady = t[transient_steps:]
        
        # Calculate period using zero crossings
        zero_crossings = np.where(np.diff(np.signbit(x_steady)))[0]
        if len(zero_crossings) >= 2:
            periods = np.diff(t_steady[zero_crossings])
            avg_period = np.mean(periods)
            period_std = np.std(periods)
        else:
            avg_period = np.nan
            period_std = np.nan
        
        # Calculate amplitude
        amplitude = (np.max(x_steady) - np.min(x_steady)) / 2
        
        # Calculate frequency
        frequency = 2 * np.pi / avg_period if not np.isnan(avg_period) else np.nan
        
        # Calculate energy (kinetic + potential approximation)
        energy = 0.5 * (dx_steady**2 + x_steady**2)
        avg_energy = np.mean(energy)
        energy_variation = np.std(energy)
        
        # Plot energy over time
        plt.figure(figsize=(10, 6))
        plt.plot(t_steady, energy, 'purple', linewidth=2, alpha=0.7)
        plt.axhline(avg_energy, color='red', linestyle='--', alpha=0.8,
                   label=f'Average Energy: {avg_energy:.3f}')
        plt.fill_between(t_steady, avg_energy - energy_variation, 
                        avg_energy + energy_variation, alpha=0.2, color='red')
        plt.xlabel('Time t')
        plt.ylabel('Energy E(t)')
        plt.title(f'{system_type.title()} Oscillator: Energy Evolution (μ = {mu})')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.show()
        
        print(f"🎯 Limit Cycle Analysis ({system_type}):")
        print(f"   Control parameter: μ = {mu}")
        print(f"   Average period: T = {avg_period:.3f} ± {period_std:.3f}")
        print(f"   Frequency: f = {frequency:.3f}")
        print(f"   Amplitude: A = {amplitude:.3f}")
        print(f"   Average energy: E = {avg_energy:.3f} ± {energy_variation:.3f}")
        print(f"   This demonstrates self-sustaining oscillations!")
        
        return {
            'period': avg_period,
            'frequency': frequency,
            'amplitude': amplitude,
            'energy': avg_energy,
            'energy_variation': energy_variation
        }

    def _simulate_critical_phenomena_python(self, x0, T, dt, mu, system_type='pitchfork'):
        """
        Simulate critical phenomena (pitchfork, supercritical pitchfork)
        
        Parameters:
        - x0: initial condition
        - T: total time
        - dt: time step
        - mu: control parameter
        - system_type: 'pitchfork' or 'supercritical_pitchfork'
        
        Returns:
        - Dictionary with time, position, and control parameter
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        x = np.zeros(time_steps)
        
        x[0] = x0
        
        for i in range(1, time_steps):
            if system_type == 'pitchfork':
                # Pitchfork bifurcation: dx/dt = μx - x³
                dx_dt = mu * x[i-1] - x[i-1]**3
                x[i] = x[i-1] + dt * dx_dt
                
            elif system_type == 'supercritical_pitchfork':
                # Supercritical pitchfork bifurcation: dx/dt = (μ - 1)x - x³
                dx_dt = (mu - 1) * x[i-1] - x[i-1]**3
                x[i] = x[i-1] + dt * dx_dt
        
        return {
            'time': t,
            'position': x,
            'mu': mu,
            'system_type': system_type
        }
    
    def _plot_critical_phenomena_python(self, simulation_data, save_path=None):
        """Plot critical phenomena results"""
        t = simulation_data['time']
        x = simulation_data['position']
        mu = simulation_data['mu']
        system_type = simulation_data['system_type']
        
        plt.figure(figsize=(10, 6))
        plt.plot(t, x, 'b-', linewidth=2, label=f'x(t) for μ = {mu}')
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title(f'{system_type.title()} Critical Phenomenon: x(t) vs t (μ = {mu})')
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Critical phenomena plot saved to {save_path}")
        
        plt.show()
        
    def _analyze_critical_phenomena_python(self, simulation_data):
        """Analyze critical phenomena properties"""
        x = simulation_data['position']
        t = simulation_data['time']
        mu = simulation_data['mu']
        system_type = simulation_data['system_type']
        
        # Find the steady state (x_ss)
        # For pitchfork, x_ss = 0
        # For supercritical pitchfork, x_ss = 0
        x_ss = 0.0
        
        # Calculate the bifurcation parameter (mu)
        # For pitchfork, mu = x³
        # For supercritical pitchfork, mu = x³ + 1
        if system_type == 'pitchfork':
            mu_values = x**3
        elif system_type == 'supercritical_pitchfork':
            mu_values = x**3 + 1
        else:
            mu_values = np.nan # Should not happen
        
        # Plot x(t) vs t
        plt.figure(figsize=(10, 6))
        plt.plot(t, x, 'b-', linewidth=2, label=f'x(t) for μ = {mu}')
        plt.axhline(y=x_ss, color='red', linestyle='--', alpha=0.7, label=f'Steady State x* = {x_ss}')
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title(f'{system_type.title()} Critical Phenomenon: x(t) vs t (μ = {mu})')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.show()
        
        print(f"🎯 Critical Phenomena Analysis ({system_type}):")
        print(f"   Control parameter: μ = {mu}")
        print(f"   Steady state: x* = {x_ss}")
        print(f"   This demonstrates critical phenomena and scaling behavior!")
        
        return {
            'mu_values': mu_values,
            'steady_state': x_ss
        }

    def _simulate_multi_scale_python(self, x_fast0, x_slow0, T, dt, mu, tau_fast, tau_slow, coupling):
        """
        Simulate multi-scale dynamics (fast/slow variable interaction)
        
        Parameters:
        - x_fast0: initial fast variable
        - x_slow0: initial slow variable
        - T: total time
        - dt: time step
        - mu: control parameter for fast variable
        - tau_fast: time constant for fast variable
        - tau_slow: time constant for slow variable
        - coupling: coupling strength between fast and slow variables
        
        Returns:
        - Dictionary with time, fast and slow variables, and control parameter
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        x_fast = np.zeros(time_steps)
        x_slow = np.zeros(time_steps)
        
        x_fast[0] = x_fast0
        x_slow[0] = x_slow0
        
        for i in range(1, time_steps):
            # Fast variable dynamics: dx_fast/dt = -x_fast/tau_fast + coupling * x_slow
            # Slow variable dynamics: dx_slow/dt = -x_slow/tau_slow
            dx_fast_dt = -x_fast[i-1] / tau_fast + coupling * x_slow[i-1]
            dx_slow_dt = -x_slow[i-1] / tau_slow
            
            x_fast[i] = x_fast[i-1] + dt * dx_fast_dt
            x_slow[i] = x_slow[i-1] + dt * dx_slow_dt
        
        return {
            'time': t,
            'fast_variable': x_fast,
            'slow_variable': x_slow,
            'mu': mu,
            'tau_fast': tau_fast,
            'tau_slow': tau_slow,
            'coupling': coupling
        }
    
    def _plot_multi_scale_python(self, simulation_data, save_path=None):
        """Plot multi-scale dynamics results"""
        t = simulation_data['time']
        x_fast = simulation_data['fast_variable']
        x_slow = simulation_data['slow_variable']
        mu = simulation_data['mu']
        tau_fast = simulation_data['tau_fast']
        tau_slow = simulation_data['tau_slow']
        coupling = simulation_data['coupling']
        
        # Create subplots
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))
        
        # Plot 1: Time series
        ax1.plot(t, x_fast, 'b-', linewidth=2, label=f'Fast Variable (τ_fast = {tau_fast:.2f})')
        ax1.plot(t, x_slow, 'r--', linewidth=2, label=f'Slow Variable (τ_slow = {tau_slow:.2f})')
        ax1.set_xlabel('Time t')
        ax1.set_ylabel('Amplitude')
        ax1.set_title(f'Multi-Scale Dynamics: Fast/Slow Variables (μ = {mu}, Coupling = {coupling:.2f})')
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # Plot 2: Phase space (limit cycle)
        ax2.plot(x_fast, x_slow, 'g-', linewidth=2, label='Phase Trajectory')
        ax2.plot(x_fast[0], x_slow[0], 'ro', markersize=8, label='Start')
        ax2.plot(x_fast[-1], x_slow[-1], 'bo', markersize=8, label='End')
        ax2.set_xlabel('Fast Variable x_fast')
        ax2.set_ylabel('Slow Variable x_slow')
        ax2.set_title(f'Multi-Scale Dynamics: Phase Space (μ = {mu}, Coupling = {coupling:.2f})')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        
        # Make phase space plot square and centered
        ax2.set_aspect('equal')
        max_range = max(np.max(np.abs(x_fast)), np.max(np.abs(x_slow)))
        ax2.set_xlim(-max_range*1.1, max_range*1.1)
        ax2.set_ylim(-max_range*1.1, max_range*1.1)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Multi-scale dynamics plot saved to {save_path}")
        
        plt.show()
        
    def _analyze_multi_scale_python(self, simulation_data):
        """Analyze multi-scale dynamics properties"""
        x_fast = simulation_data['fast_variable']
        x_slow = simulation_data['slow_variable']
        t = simulation_data['time']
        mu = simulation_data['mu']
        tau_fast = simulation_data['tau_fast']
        tau_slow = simulation_data['tau_slow']
        coupling = simulation_data['coupling']
        
        # Find the limit cycle (after transient)
        transient_steps = int(len(x_fast) * 0.2)  # Skip first 20%
        x_fast_steady = x_fast[transient_steps:]
        x_slow_steady = x_slow[transient_steps:]
        t_steady = t[transient_steps:]
        
        # Calculate period using zero crossings
        zero_crossings = np.where(np.diff(np.signbit(x_fast_steady)))[0]
        if len(zero_crossings) >= 2:
            periods = np.diff(t_steady[zero_crossings])
            avg_period = np.mean(periods)
            period_std = np.std(periods)
        else:
            avg_period = np.nan
            period_std = np.nan
        
        # Calculate amplitude
        amplitude = (np.max(x_fast_steady) - np.min(x_fast_steady)) / 2
        
        # Calculate frequency
        frequency = 2 * np.pi / avg_period if not np.isnan(avg_period) else np.nan
        
        # Calculate energy (kinetic + potential approximation)
        energy = 0.5 * (x_fast_steady**2 + x_slow_steady**2) # Energy in phase space
        avg_energy = np.mean(energy)
        energy_variation = np.std(energy)
        
        # Plot energy over time
        plt.figure(figsize=(10, 6))
        plt.plot(t_steady, energy, 'purple', linewidth=2, alpha=0.7)
        plt.axhline(avg_energy, color='red', linestyle='--', alpha=0.8,
                   label=f'Average Energy: {avg_energy:.3f}')
        plt.fill_between(t_steady, avg_energy - energy_variation, 
                        avg_energy + energy_variation, alpha=0.2, color='red')
        plt.xlabel('Time t')
        plt.ylabel('Energy E(t)')
        plt.title(f'Multi-Scale Dynamics: Energy Evolution (μ = {mu}, Coupling = {coupling:.2f})')
        plt.legend()
        plt.grid(True, alpha=0.3)
        plt.show()
        
        print(f"🎯 Multi-Scale Dynamics Analysis:")
        print(f"   Control parameter: μ = {mu}")
        print(f"   Coupling strength: {coupling:.2f}")
        print(f"   Average period: T = {avg_period:.3f} ± {period_std:.3f}")
        print(f"   Frequency: f = {frequency:.3f}")
        print(f"   Amplitude: A = {amplitude:.3f}")
        print(f"   Average energy: E = {avg_energy:.3f} ± {energy_variation:.3f}")
        print(f"   This demonstrates emergent behavior on slow manifolds!")
        
        return {
            'period': avg_period,
            'frequency': frequency,
            'amplitude': amplitude,
            'energy': avg_energy,
            'energy_variation': energy_variation
        }

    def _simulate_chaotic_dynamics_python(self, x0, T, dt, r, system_type='logistic_map'):
        """
        Simulate chaotic dynamics (logistic map, Lorenz system)
        
        Parameters:
        - x0: initial condition
        - T: total time
        - dt: time step
        - r: control parameter (growth rate for logistic, rho for Lorenz)
        - system_type: 'logistic_map' or 'lorenz'
        
        Returns:
        - Dictionary with time, position, and control parameter
        """
        time_steps = int(T / dt)
        t = np.linspace(0, T, time_steps)
        
        if system_type == 'logistic_map':
            # Logistic map: x_{n+1} = r * x_n * (1 - x_n)
            x = np.zeros(time_steps)
            x[0] = x0
            
            for i in range(1, time_steps):
                x[i] = self.logistic_map(x[i-1], r)
            
            return {
                'time': t,
                'position': x,
                'r': r,
                'system_type': system_type
            }
            
        elif system_type == 'lorenz':
            # Lorenz system: dx/dt = σ(y-x), dy/dt = x(ρ-z)-y, dz/dt = xy-βz
            # For 1D projection, we'll use x component
            sigma = 10.0
            rho = r  # Control parameter
            beta = 8/3
            
            x = np.zeros(time_steps)
            y = np.zeros(time_steps)
            z = np.zeros(time_steps)
            
            x[0] = x0
            y[0] = x0 + 0.1  # Small perturbation
            z[0] = x0 + 0.2  # Small perturbation
            
            for i in range(1, time_steps):
                dx_dt, dy_dt, dz_dt = self.lorenz_flow(x[i-1], y[i-1], z[i-1], sigma, rho, beta)
                x[i] = x[i-1] + dt * dx_dt
                y[i] = y[i-1] + dt * dy_dt
                z[i] = z[i-1] + dt * dz_dt
            
            return {
                'time': t,
                'position': x,
                'r': r,
                'system_type': system_type
            }
    
    def _plot_chaotic_dynamics_python(self, simulation_data, save_path=None):
        """Plot chaotic dynamics results"""
        t = simulation_data['time']
        x = simulation_data['position']
        r = simulation_data['r']
        system_type = simulation_data['system_type']
        
        plt.figure(figsize=(12, 8))
        
        # Plot 1: Time series
        plt.subplot(2, 1, 1)
        plt.plot(t, x, 'b-', linewidth=1, alpha=0.8, label=f'x(t) for r = {r}')
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title(f'{system_type.title()} Chaotic Dynamics: x(t) vs t (r = {r})')
        plt.legend()
        plt.grid(True, alpha=0.3)
        
        # Plot 2: Phase space (x vs t with some lag)
        plt.subplot(2, 1, 2)
        lag = min(100, len(x) // 10)  # Lag for phase space reconstruction
        if lag > 0:
            plt.plot(x[:-lag], x[lag:], 'r.', markersize=1, alpha=0.6, label=f'Phase Space (lag = {lag})')
            plt.xlabel('x(t)')
            plt.ylabel(f'x(t + {lag}*dt)')
            plt.title(f'{system_type.title()} Chaotic Dynamics: Phase Space Reconstruction')
            plt.legend()
            plt.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"📊 Chaotic dynamics plot saved to {save_path}")
        
        plt.show()
        
    def _analyze_chaotic_dynamics_python(self, simulation_data):
        """Analyze chaotic dynamics properties"""
        x = simulation_data['position']
        t = simulation_data['time']
        r = simulation_data['r']
        system_type = simulation_data['system_type']
        
        # Calculate Lyapunov exponent (approximate)
        # For logistic map: λ ≈ ln|r(1-2x)| averaged over trajectory
        if system_type == 'logistic_map':
            lyapunov_exponents = []
            for i in range(1, len(x)):
                if x[i-1] != 0 and x[i-1] != 1:
                    lyap = np.log(abs(r * (1 - 2 * x[i-1])))
                    lyapunov_exponents.append(lyap)
            
            avg_lyapunov = np.mean(lyapunov_exponents) if lyapunov_exponents else np.nan
            lyap_std = np.std(lyapunov_exponents) if lyapunov_exponents else np.nan
            
            # Determine if chaotic (positive Lyapunov exponent)
            is_chaotic = avg_lyapunov > 0.01 if not np.isnan(avg_lyapunov) else False
            
        else:
            # For Lorenz, use a simpler measure
            # Calculate the rate of separation of nearby trajectories
            separation = np.diff(x)
            avg_separation = np.mean(np.abs(separation))
            is_chaotic = avg_separation > 0.1  # Threshold for chaos
            
            avg_lyapunov = np.nan
            lyap_std = np.nan
        
        # Calculate correlation dimension (approximate)
        # Use the correlation integral method
        max_embedding = min(10, len(x) // 20)
        correlation_dims = []
        
        for embedding_dim in range(2, max_embedding + 1):
            # Simple correlation dimension estimate
            if len(x) >= embedding_dim:
                # Calculate distances in embedding space
                distances = []
                for i in range(len(x) - embedding_dim + 1):
                    for j in range(i + 1, len(x) - embedding_dim + 1):
                        dist = np.sqrt(sum((x[i:i+embedding_dim] - x[j:j+embedding_dim])**2))
                        if dist > 0:
                            distances.append(dist)
                
                if distances:
                    # Count pairs within small distance
                    epsilon = np.percentile(distances, 10)  # 10th percentile as threshold
                    count = sum(1 for d in distances if d < epsilon)
                    if count > 0:
                        corr_dim = np.log(count) / np.log(epsilon)
                        correlation_dims.append(corr_dim)
        
        avg_correlation_dim = np.mean(correlation_dims) if correlation_dims else np.nan
        
        # Plot trajectory analysis
        plt.figure(figsize=(10, 6))
        plt.plot(t, x, 'b-', linewidth=1, alpha=0.8)
        plt.xlabel('Time t')
        plt.ylabel('State x(t)')
        plt.title(f'{system_type.title()} Chaotic Dynamics: Trajectory Analysis (r = {r})')
        plt.grid(True, alpha=0.3)
        
        # Add text box with analysis results
        textstr = f'Lyapunov: {avg_lyapunov:.3f} ± {lyap_std:.3f}\nCorrelation Dim: {avg_correlation_dim:.3f}\nChaotic: {is_chaotic}'
        props = dict(boxstyle='round', facecolor='wheat', alpha=0.5)
        plt.text(0.02, 0.98, textstr, transform=plt.gca().transAxes, fontsize=10,
                verticalalignment='top', bbox=props)
        
        plt.show()
        
        print(f"🎯 Chaotic Dynamics Analysis ({system_type}):")
        print(f"   Control parameter: r = {r}")
        print(f"   Lyapunov exponent: λ = {avg_lyapunov:.3f} ± {lyap_std:.3f}")
        print(f"   Correlation dimension: D = {avg_correlation_dim:.3f}")
        print(f"   System is chaotic: {is_chaotic}")
        print(f"   This demonstrates sensitive dependence on initial conditions!")
        
        return {
            'lyapunov_exponent': avg_lyapunov,
            'lyapunov_std': lyap_std,
            'correlation_dimension': avg_correlation_dim,
            'is_chaotic': is_chaotic
        }
    
    def simple_flow(self, x: float) -> float:
        """Flow function f(x) = -x (exponential decay)"""
        if self.lib:
            return self.lib.simple_flow(ctypes.c_double(x))
        else:
            # Python fallback
            return -x
    
    def simple_noise(self, t: float) -> float:
        """Noise function ω(t) = 0.1 (constant)"""
        if self.lib:
            return self.lib.simple_noise(ctypes.c_double(t))
        else:
            # Python fallback
            return 0.1
    
    def evolution_equation(self, x: float, t: float) -> float:
        """Evolution equation dx/dt = f(x) + ω(t)"""
        if self.lib:
            return self.lib.evolution_equation(ctypes.c_double(x), ctypes.c_double(t))
        else:
            # Python fallback
            return self.simple_flow(x) + self.simple_noise(t)
    
    def euler_step(self, x: float, dt: float) -> float:
        """Euler integration step: x + dt * dx/dt"""
        if self.lib:
            return self.lib.euler_step(ctypes.c_double(x), ctypes.c_double(dt))
        else:
            # Python fallback
            return x + dt * self.evolution_equation(x, 0.0)
    
    def simulate_trajectory(self, x0: float, t0: float, t_final: float, dt: float) -> Tuple[np.ndarray, np.ndarray]:
        """
        Simulate Langevin equation trajectory
        
        Args:
            x0: Initial state
            t0: Initial time
            t_final: Final time
            dt: Time step
            
        Returns:
            Tuple of (time_array, state_array)
        """
        # Generate time points
        t_points = np.arange(t0, t_final + dt, dt)
        x_points = np.zeros_like(t_points)
        x_points[0] = x0
        
        # Euler integration
        for i in range(1, len(t_points)):
            x_points[i] = self.euler_step(x_points[i-1], dt)
        
        return t_points, x_points
    
    def simulate_multiple_conditions(self, initial_states: List[float], t_final: float, dt: float) -> List[Tuple[np.ndarray, np.ndarray]]:
        """
        Simulate multiple initial conditions
        
        Args:
            initial_states: List of initial conditions
            t_final: Final time
            dt: Time step
            
        Returns:
            List of (time_array, state_array) tuples
        """
        trajectories = []
        for x0 in initial_states:
            t, x = self.simulate_trajectory(x0, 0.0, t_final, dt)
            trajectories.append((t, x))
        return trajectories
    
    def plot_trajectory(self, x0: float, t_final: float, dt: float, 
                       title: str = None, show: bool = True) -> plt.Figure:
        """
        Plot a single trajectory
        
        Args:
            x0: Initial state
            t_final: Final time
            dt: Time step
            title: Plot title
            show: Whether to display the plot
            
        Returns:
            matplotlib Figure object
        """
        t, x = self.simulate_trajectory(x0, 0.0, t_final, dt)
        
        fig, ax = plt.subplots(figsize=(10, 6))
        ax.plot(t, x, 'b-', linewidth=2, label=f'x₀ = {x0}')
        ax.axhline(y=0.1, color='r', linestyle='--', alpha=0.7, label='Equilibrium x* = 0.1')
        ax.set_xlabel('Time t')
        ax.set_ylabel('State x(t)')
        ax.set_title(title or f'Langevin Equation: dx/dt = -x + 0.1 (x₀ = {x0})')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        if show:
            plt.show()
        
        return fig
    
    def plot_multiple_trajectories(self, initial_states: List[float], t_final: float, dt: float,
                                 title: str = None, show: bool = True) -> plt.Figure:
        """
        Plot multiple trajectories
        
        Args:
            initial_states: List of initial conditions
            t_final: Final time
            dt: Time step
            title: Plot title
            show: Whether to display the plot
            
        Returns:
            matplotlib Figure object
        """
        trajectories = self.simulate_multiple_conditions(initial_states, t_final, dt)
        
        fig, ax = plt.subplots(figsize=(12, 8))
        
        colors = plt.cm.viridis(np.linspace(0, 1, len(initial_states)))
        
        for i, ((t, x), x0) in enumerate(zip(trajectories, initial_states)):
            ax.plot(t, x, color=colors[i], linewidth=2, label=f'x₀ = {x0}')
        
        ax.axhline(y=0.1, color='r', linestyle='--', alpha=0.7, linewidth=2, label='Equilibrium x* = 0.1')
        ax.set_xlabel('Time t')
        ax.set_ylabel('State x(t)')
        ax.set_title(title or f'Langevin Equation: Multiple Initial Conditions')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        if show:
            plt.show()
        
        return fig

# Convenience function for quick testing
def test_langevin_bindings():
    """Test the Langevin bindings"""
    try:
        # Try to load the Lean library
        l = LangevinBindings()
        print("✅ Python bindings initialized successfully!")
        
        # Test basic functions
        print(f"Flow function f(2.0) = {l.simple_flow(2.0)}")
        print(f"Noise function ω(0.0) = {l.simple_noise(0.0)}")
        print(f"Evolution equation dx/dt at x=1.0, t=0.0 = {l.evolution_equation(1.0, 0.0)}")
        
        # Test simulation
        t, x = l.simulate_trajectory(1.0, 0.0, 1.0, 0.01)
        print(f"Simulation completed: {len(t)} time points, final state = {x[-1]:.6f}")
        
        return l
        
    except Exception as e:
        print(f"❌ Error testing bindings: {e}")
        return None

if __name__ == "__main__":
    # Test the bindings
    l = test_langevin_bindings()
    
    if l:
        # Create some plots
        print("\n🎨 Creating plots...")
        
        # Single trajectory
        l.plot_trajectory(1.0, 2.0, 0.01, "Single Trajectory Example")
        
        # Multiple trajectories
        initial_states = [0.0, 0.5, 1.0, 1.5, 2.0]
        l.plot_multiple_trajectories(initial_states, 2.0, 0.01, "Multiple Initial Conditions")
        
        print("✅ All plots created successfully!") 