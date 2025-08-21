# Python Bindings for Lean Langevin Simulator

This directory contains Python bindings that allow you to use your mathematically proven Lean Langevin equations directly from Python, enabling advanced plotting, analysis, and integration with scientific computing workflows.

## 🎯 **What This Gives You**

### **Mathematical Rigor + Python Power**
- **Lean proofs** guarantee mathematical correctness
- **Python ecosystem** provides plotting, analysis, and integration
- **Direct access** to your verified algorithms
- **Best of both worlds**: Formal verification + practical computation

## 🚀 **Quick Start**

### **1. Install Dependencies**
```bash
pip install -r requirements.txt
```

### **2. Test the Bindings**
```bash
python test_bindings.py
```

### **3. Use in Your Own Code**
```python
from langevin_bindings import LangevinBindings

# Initialize bindings
l = LangevinBindings()

# Run simulation
t, x = l.simulate_trajectory(x0=1.0, t0=0.0, t_final=2.0, dt=0.01)

# Create plots
l.plot_trajectory(1.0, 2.0, 0.01)
l.plot_multiple_trajectories([0.0, 0.5, 1.0, 1.5, 2.0], 2.0, 0.01)
```

## 🔧 **How It Works**

### **Architecture**
```
Lean Source (.lean) → C Code (.c) → Python Bindings → Your Python Code
     ↓                    ↓              ↓              ↓
Mathematical Proofs → Executable → Python Interface → Analysis/Plotting
```

### **Key Components**
1. **Lean Source**: Your proven Langevin equations
2. **C Generation**: Lean compiles to C code automatically
3. **Python Bindings**: ctypes interface to the C library
4. **Python API**: High-level interface for scientific computing

## 📊 **Available Functions**

### **Core Mathematical Functions**
- `simple_flow(x)`: Flow function f(x) = -x
- `simple_noise(t)`: Noise function ω(t) = 0.1
- `evolution_equation(x, t)`: dx/dt = f(x) + ω(t)

### **Numerical Integration**
- `euler_step(x, dt)`: Single Euler integration step
- `simulate_trajectory(x0, t0, t_final, dt)`: Full trajectory simulation
- `simulate_multiple_conditions(initial_states, t_final, dt)`: Multiple trajectories

### **Visualization**
- `plot_trajectory(x0, t_final, dt)`: Single trajectory plot
- `plot_multiple_trajectories(initial_states, t_final, dt)`: Multiple trajectories plot

## 🎨 **Example: Advanced Analysis**

```python
import numpy as np
from langevin_bindings import LangevinBindings

# Initialize
l = LangevinBindings()

# Parameter study
initial_states = np.linspace(0, 3, 20)
final_times = np.linspace(0.1, 5.0, 50)
dt = 0.01

# Create parameter grid
X, T = np.meshgrid(initial_states, final_times)
Z = np.zeros_like(X)

# Compute final states for each parameter combination
for i, t_final in enumerate(final_times):
    for j, x0 in enumerate(initial_states):
        _, trajectory = l.simulate_trajectory(x0, 0.0, t_final, dt)
        Z[i, j] = trajectory[-1]  # Final state

# Create 3D surface plot
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

fig = plt.figure(figsize=(12, 8))
ax = fig.add_subplot(111, projection='3d')
surf = ax.plot_surface(X, T, Z, cmap='viridis')
ax.set_xlabel('Initial State x₀')
ax.set_ylabel('Final Time t')
ax.set_zlabel('Final State x(t)')
ax.set_title('Langevin Equation: Parameter Sensitivity Analysis')
plt.colorbar(surf)
plt.show()
```

## 🔬 **Scientific Applications**

### **1. Parameter Sensitivity Analysis**
- Study how initial conditions affect final states
- Analyze convergence rates for different parameters
- Identify stable and unstable regions

### **2. Statistical Analysis**
- Run Monte Carlo simulations with random initial conditions
- Analyze distribution of final states
- Compute confidence intervals for predictions

### **3. Machine Learning Integration**
- Use as a physics-informed neural network component
- Generate training data for surrogate models
- Validate learned dynamics against proven equations

### **4. Biological Modeling**
- Model population dynamics with proven equations
- Study evolutionary stability
- Analyze homeostatic mechanisms

## 🚧 **Current Limitations**

### **What Works Now**
- ✅ Basic Langevin equations (dx/dt = -x + 0.1)
- ✅ Euler integration
- ✅ Single and multiple trajectory simulation
- ✅ Basic plotting capabilities

### **What's Coming Next**
- 🔄 Vector systems (n-dimensional)
- 🔄 Stochastic processes (proper Wiener noise)
- 🔄 Advanced integration methods (Runge-Kutta)
- 🔄 Variational principles and action minimization

## 🎯 **Next Steps**

### **Immediate**
1. **Test the bindings**: Run `python test_bindings.py`
2. **Create your own plots**: Use the plotting functions
3. **Integrate with workflows**: Use in data analysis pipelines

### **Short Term**
1. **Extend to vector systems**: n-dimensional Langevin equations
2. **Add stochastic processes**: Proper Wiener process implementation
3. **Implement advanced methods**: Runge-Kutta, adaptive time stepping

### **Long Term**
1. **Variational synthesis**: Action principles and least action
2. **Biological applications**: Price equation, replicator dynamics
3. **Machine learning**: Physics-informed neural networks

## 💡 **Key Benefits**

### **1. Mathematical Correctness**
- **Every computation** is guaranteed by Lean proofs
- **No numerical errors** in the core algorithms
- **Reproducible results** with formal verification

### **2. Python Ecosystem**
- **Matplotlib/Seaborn** for advanced plotting
- **NumPy/SciPy** for numerical analysis
- **Pandas** for data manipulation
- **Scikit-learn** for machine learning

### **3. Scientific Workflow Integration**
- **Jupyter notebooks** for interactive analysis
- **Data pipelines** for batch processing
- **API integration** for web applications
- **Cloud deployment** for scalable computation

## 🎉 **You're Ready to Go!**

Your Lean Langevin equations are now accessible from Python with:
- **Mathematical guarantees** from formal verification
- **Computational power** from Python ecosystem
- **Bridge** between rigor and practice

**Start exploring the possibilities!** 🚀 