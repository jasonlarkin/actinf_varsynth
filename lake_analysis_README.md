# Lake Directory Analyzer

A comprehensive Python script to analyze Lean 4 `.lake` build directories and provide insights into project structure, dependencies, and build health.

## Features

### 🔍 **Project Metadata Analysis**
- Extracts project name, Lean version, and configuration
- Identifies executables and library targets
- Analyzes dependency declarations

### 🔨 **Build Artifacts Analysis**
- Scans executables, libraries, and intermediate files
- Reports file counts and sizes
- Analyzes source code structure

### 📦 **Dependency Analysis**
- Comprehensive package inventory
- Size analysis of all dependencies
- Identification of largest packages
- File count statistics per package

### ⚙️ **Cache & Configuration Analysis**
- Build trace information
- Platform and hash details
- Lock file status
- Configuration integrity checks

### 🏗️ **Build Status Assessment**
- Overall build health evaluation
- Missing component detection
- Warning and error reporting
- Optimization suggestions

## Usage

### Basic Analysis
```bash
python3 analyze_lake.py
```

### Custom Lake Directory
```bash
python3 analyze_lake.py /path/to/.lake
```

### With Custom Project Root
```bash
python3 analyze_lake.py .lake --project-root /path/to/project
```

### JSON Output
```bash
python3 analyze_lake.py --format json
```

### Save Report to File
```bash
python3 analyze_lake.py --output analysis_report.txt
python3 analyze_lake.py --format json --output analysis_report.json
```

## Command Line Options

- `lake_path`: Path to .lake directory (default: ./.lake)
- `--project-root`: Path to project root directory
- `--output`: Output file path for the report
- `--format`: Output format - `text` or `json` (default: text)

## Example Output

```
================================================================================
LEAN 4 LAKE BUILD ANALYSIS REPORT
================================================================================
Generated: 2025-08-22 12:25:10
Project: /home/trim/Documents/GitHub/actinf_varsynth

📋 PROJECT OVERVIEW
----------------------------------------
Project Name: actinf_varsynth
Lean Version: leanprover/lean4:v4.5.0
Has Executables: True
Executables: langevin_simulator
Direct Dependencies: 1

🏗️  BUILD STATUS
----------------------------------------
Health: 🟡 GOOD
Optimization Suggestions:
  💡 Consider reviewing large dependency 'mathlib' (2.4 GB)

🔨 BUILD ARTIFACTS
----------------------------------------
Total Files: 26
Total Size: 12.3 MB
Executables: 1
  • langevin_simulator (2.1 MB)
Libraries: 2
Source Files: 13
```

## Requirements

- Python 3.6+
- Standard library only (no external dependencies)

## Health Indicators

- 🟢 **EXCELLENT**: All components present, no warnings
- 🟡 **GOOD**: Minor issues or optimization opportunities
- 🟠 **INCOMPLETE**: Missing components but no errors
- 🔴 **ERROR**: Build errors detected

## Analysis Categories

The script analyzes seven major aspects of your Lean 4 project:

1. **Metadata**: Project configuration and toolchain info
2. **Artifacts**: Built executables, libraries, and intermediates
3. **Dependencies**: Package dependencies and their sizes
4. **Cache**: Build cache status and configuration traces
5. **Status**: Overall build health and recommendations
6. **Performance**: Optimization suggestions based on analysis
7. **Structure**: File organization and completeness checks

## Use Cases

- **Project Assessment**: Quick overview of project size and complexity
- **Build Debugging**: Identify missing components or configuration issues
- **Dependency Management**: Understand which packages consume the most space
- **Performance Optimization**: Get suggestions for reducing build size
- **Documentation**: Generate reports for project documentation

## Integration

This script can be integrated into:
- CI/CD pipelines for automated build analysis
- Development workflows for regular project health checks
- Documentation generation processes
- Build optimization workflows
