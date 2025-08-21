#!/usr/bin/env python3
"""
Setup script for Lean Langevin Python bindings
Helps configure and test the bindings
"""

import os
import sys
import subprocess
import shutil

def check_python_version():
    """Check if Python version is compatible"""
    if sys.version_info < (3, 7):
        print("❌ Python 3.7+ required. Current version:", sys.version)
        return False
    print(f"✅ Python version: {sys.version}")
    return True

def install_requirements():
    """Install required Python packages"""
    print("\n📦 Installing Python dependencies...")
    try:
        subprocess.check_call([sys.executable, "-m", "pip", "install", "-r", "requirements.txt"])
        print("✅ Dependencies installed successfully!")
        return True
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to install dependencies: {e}")
        return False

def check_lean_library():
    """Check if Lean library exists and is accessible"""
    print("\n🔍 Checking for Lean library...")
    
    # Look for the Lean library
    lean_lib_paths = [
        "../.lake/build/lib/liblangevin_simulator.so",
        "../.lake/build/lib/liblangevin_simulator.dll",
        "../.lake/build/lib/liblangevin_simulator.dylib",
        "../build/lib/liblangevin_simulator.so",
        "../build/lib/liblangevin_simulator.dll",
        "../build/lib/liblangevin_simulator.dylib"
    ]
    
    for path in lean_lib_paths:
        if os.path.exists(path):
            print(f"✅ Found Lean library: {path}")
            return path
    
    print("⚠️  Lean library not found. Will use Python fallback implementation.")
    return None

def create_symlink_to_library(library_path):
    """Create a symlink to the Lean library for easier access"""
    if not library_path:
        return
    
    target_name = "langevin_simulator_lib"
    if os.path.exists(target_name):
        os.remove(target_name)
    
    try:
        os.symlink(library_path, target_name)
        print(f"✅ Created symlink: {target_name} -> {library_path}")
    except OSError:
        # On Windows, try to copy instead
        try:
            shutil.copy2(library_path, target_name)
            print(f"✅ Copied library: {target_name}")
        except Exception as e:
            print(f"⚠️  Could not create symlink or copy: {e}")

def test_import():
    """Test if the bindings can be imported"""
    print("\n🧪 Testing import...")
    try:
        from langevin_bindings import LangevinBindings
        print("✅ Successfully imported LangevinBindings!")
        return True
    except ImportError as e:
        print(f"❌ Import failed: {e}")
        return False

def run_tests():
    """Run the test suite"""
    print("\n🚀 Running tests...")
    try:
        result = subprocess.run([sys.executable, "test_bindings.py"], 
                              capture_output=True, text=True)
        if result.returncode == 0:
            print("✅ Tests completed successfully!")
            print("\n📊 Test Output:")
            print(result.stdout)
        else:
            print("❌ Tests failed!")
            print("Error output:")
            print(result.stderr)
        return result.returncode == 0
    except Exception as e:
        print(f"❌ Failed to run tests: {e}")
        return False

def main():
    """Main setup function"""
    print("🚀 Setting up Lean Langevin Python Bindings")
    print("=" * 50)
    
    # Check Python version
    if not check_python_version():
        return False
    
    # Install requirements
    if not install_requirements():
        return False
    
    # Check for Lean library
    library_path = check_lean_library()
    
    # Create symlink if library found
    if library_path:
        create_symlink_to_library(library_path)
    
    # Test import
    if not test_import():
        return False
    
    # Run tests
    if not run_tests():
        return False
    
    print("\n🎉 Setup completed successfully!")
    print("=" * 50)
    print("Your Python bindings are ready to use!")
    print("\nNext steps:")
    print("1. Use in Jupyter notebooks: from langevin_bindings import LangevinBindings")
    print("2. Create custom analysis scripts")
    print("3. Integrate with scientific computing workflows")
    print("4. Extend for your specific research needs")
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1) 