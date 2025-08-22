#!/usr/bin/env python3
"""
Comprehensive Lake Build Directory Analyzer for Lean 4 Projects

This script analyzes the .lake directory structure, build artifacts, dependencies,
and provides insights into Lean 4 project configuration and build status.
"""

import os
import json
import hashlib
import time
from datetime import datetime, timedelta
from pathlib import Path
import argparse
from typing import Dict, List, Optional, Tuple, Any
import subprocess

class LakeAnalyzer:
    """Main analyzer class for .lake directory structure."""

    def __init__(self, lake_path: str, project_root: Optional[str] = None):
        """
        Initialize the Lake analyzer.

        Args:
            lake_path: Path to the .lake directory
            project_root: Path to the project root (optional)
        """
        self.lake_path = Path(lake_path).resolve()
        self.project_root = Path(project_root) if project_root else self.lake_path.parent
        self.build_path = self.lake_path / "build"
        self.packages_path = self.lake_path / "packages"
        self.analysis_results = {}

        # Validate paths
        if not self.lake_path.exists():
            raise FileNotFoundError(f".lake directory not found at: {self.lake_path}")
        if not self.project_root.exists():
            raise FileNotFoundError(f"Project root not found at: {self.project_root}")

    def analyze_project_metadata(self) -> Dict[str, Any]:
        """Analyze project configuration and metadata."""
        print("🔍 Analyzing project metadata...")

        metadata = {}

        # Read lakefile.lean
        lakefile_path = self.project_root / "lakefile.lean"
        if lakefile_path.exists():
            with open(lakefile_path, 'r', encoding='utf-8') as f:
                metadata['lakefile_content'] = f.read()

            # Parse basic project info
            metadata['project_name'] = self._extract_project_name(metadata['lakefile_content'])
            metadata['has_executable'] = 'lean_exe' in metadata['lakefile_content']
            metadata['executable_names'] = self._extract_executable_names(metadata['lakefile_content'])
            metadata['dependencies'] = self._extract_dependencies(metadata['lakefile_content'])

        # Read lake-manifest.json
        manifest_path = self.project_root / "lake-manifest.json"
        if manifest_path.exists():
            with open(manifest_path, 'r', encoding='utf-8') as f:
                manifest_data = json.load(f)
                metadata['manifest'] = manifest_data
                metadata['package_count'] = len(manifest_data.get('packages', []))
                metadata['direct_dependencies'] = [
                    pkg['name'] for pkg in manifest_data.get('packages', [])
                    if not pkg.get('inherited', False)
                ]

        # Read lean-toolchain
        toolchain_path = self.project_root / "lean-toolchain"
        if toolchain_path.exists():
            with open(toolchain_path, 'r', encoding='utf-8') as f:
                metadata['lean_version'] = f.read().strip()

        # Read README if available
        readme_path = self.project_root / "README.md"
        if readme_path.exists():
            with open(readme_path, 'r', encoding='utf-8') as f:
                metadata['readme_preview'] = f.read()[:500] + "..." if len(f.read()) > 500 else f.read()

        self.analysis_results['metadata'] = metadata
        return metadata

    def analyze_build_artifacts(self) -> Dict[str, Any]:
        """Analyze build artifacts and their status."""
        print("🔨 Analyzing build artifacts...")

        artifacts = {
            'executables': [],
            'libraries': [],
            'intermediate_files': [],
            'source_files': [],
            'total_size': 0,
            'file_count': 0
        }

        if not self.build_path.exists():
            print("⚠️  Build directory not found")
            return artifacts

        # Analyze bin directory
        bin_path = self.build_path / "bin"
        if bin_path.exists():
            for file_path in bin_path.rglob("*"):
                if file_path.is_file():
                    file_info = self._analyze_file(file_path)
                    if file_path.suffix == "":
                        artifacts['executables'].append(file_info)
                    artifacts['file_count'] += 1
                    artifacts['total_size'] += file_info['size']

        # Analyze lib directory
        lib_path = self.build_path / "lib"
        if lib_path.exists():
            for file_path in lib_path.rglob("*"):
                if file_path.is_file():
                    file_info = self._analyze_file(file_path)
                    if file_path.suffix in ['.olean', '.ilean']:
                        artifacts['libraries'].append(file_info)
                    artifacts['file_count'] += 1
                    artifacts['total_size'] += file_info['size']

        # Analyze ir directory
        ir_path = self.build_path / "ir"
        if ir_path.exists():
            for file_path in ir_path.rglob("*"):
                if file_path.is_file():
                    file_info = self._analyze_file(file_path)
                    if file_path.suffix in ['.c', '.o']:
                        artifacts['intermediate_files'].append(file_info)
                    artifacts['file_count'] += 1
                    artifacts['total_size'] += file_info['size']

        # Analyze source files in project
        src_path = self.project_root / "src"
        if src_path.exists():
            for file_path in src_path.rglob("*.lean"):
                if file_path.is_file():
                    file_info = self._analyze_file(file_path)
                    artifacts['source_files'].append(file_info)
                    artifacts['file_count'] += 1
                    artifacts['total_size'] += file_info['size']

        self.analysis_results['artifacts'] = artifacts
        return artifacts

    def analyze_dependencies(self) -> Dict[str, Any]:
        """Analyze package dependencies and their status."""
        print("📦 Analyzing dependencies...")

        dependencies = {
            'packages': [],
            'total_package_size': 0,
            'largest_packages': [],
            'package_file_counts': {}
        }

        if not self.packages_path.exists():
            print("⚠️  Packages directory not found")
            return dependencies

        for package_dir in self.packages_path.iterdir():
            if package_dir.is_dir():
                package_info = self._analyze_package(package_dir)
                dependencies['packages'].append(package_info)
                dependencies['total_package_size'] += package_info['size']
                dependencies['package_file_counts'][package_info['name']] = package_info['file_count']

        # Sort packages by size
        dependencies['largest_packages'] = sorted(
            dependencies['packages'],
            key=lambda x: x['size'],
            reverse=True
        )[:5]

        self.analysis_results['dependencies'] = dependencies
        return dependencies

    def analyze_cache_and_config(self) -> Dict[str, Any]:
        """Analyze cache files, configuration, and build traces."""
        print("⚙️  Analyzing cache and configuration...")

        cache_info = {}

        # Analyze lakefile.olean
        olean_path = self.lake_path / "lakefile.olean"
        if olean_path.exists():
            cache_info['olean_file'] = self._analyze_file(olean_path)
            # Note: .olean files are binary, so we can't read them directly

        # Analyze lakefile.olean.trace
        trace_path = self.lake_path / "lakefile.olean.trace"
        if trace_path.exists():
            with open(trace_path, 'r', encoding='utf-8') as f:
                trace_content = f.read().strip()
                if trace_content:
                    try:
                        trace_data = json.loads(trace_content)
                        cache_info['trace_data'] = trace_data
                        cache_info['platform'] = trace_data.get('platform')
                        cache_info['lean_hash'] = trace_data.get('leanHash')
                        cache_info['config_hash'] = trace_data.get('configHash')
                    except json.JSONDecodeError:
                        cache_info['trace_raw'] = trace_content

            cache_info['trace_file'] = self._analyze_file(trace_path)

        # Analyze lakefile.olean.lock
        lock_path = self.lake_path / "lakefile.olean.lock"
        if lock_path.exists():
            cache_info['lock_file'] = self._analyze_file(lock_path)
            with open(lock_path, 'r', encoding='utf-8') as f:
                lock_content = f.read().strip()
                cache_info['lock_content'] = lock_content
                cache_info['is_locked'] = len(lock_content) > 0

        self.analysis_results['cache'] = cache_info
        return cache_info

    def analyze_build_status(self) -> Dict[str, Any]:
        """Analyze overall build status and health."""
        print("🏗️  Analyzing build status...")

        status = {
            'build_health': 'unknown',
            'warnings': [],
            'errors': [],
            'missing_components': [],
            'optimization_suggestions': []
        }

        # Check for essential components
        if not self.build_path.exists():
            status['missing_components'].append("Build directory (.lake/build)")
        else:
            bin_path = self.build_path / "bin"
            lib_path = self.build_path / "lib"

            if not bin_path.exists() or not any(bin_path.iterdir()):
                status['missing_components'].append("Built executables")
            if not lib_path.exists() or not any(lib_path.iterdir()):
                status['missing_components'].append("Built libraries")

        # Check dependency health
        if 'dependencies' in self.analysis_results:
            deps = self.analysis_results['dependencies']
            if not deps.get('packages'):
                status['warnings'].append("No dependencies found in packages directory")

            # Check for potentially unused large dependencies
            large_packages = deps.get('largest_packages', [])
            if large_packages:
                largest = large_packages[0]
                if largest['size'] > 100 * 1024 * 1024:  # 100MB
                    status['optimization_suggestions'].append(
                        f"Consider reviewing large dependency '{largest['name']}' ({self._format_size(largest['size'])})"
                    )

        # Check cache health
        if 'cache' in self.analysis_results:
            cache = self.analysis_results['cache']
            if cache.get('is_locked'):
                status['warnings'].append("Build lock file is present (ongoing build?)")
            if not cache.get('trace_data'):
                status['warnings'].append("Build trace information is missing")

        # Determine overall health
        if not status['errors'] and not status['missing_components']:
            if not status['warnings'] and not status['optimization_suggestions']:
                status['build_health'] = 'excellent'
            else:
                status['build_health'] = 'good'
        elif status['errors']:
            status['build_health'] = 'error'
        else:
            status['build_health'] = 'incomplete'

        self.analysis_results['status'] = status
        return status

    def generate_report(self) -> str:
        """Generate a comprehensive analysis report."""
        print("📊 Generating analysis report...")

        report_lines = []
        report_lines.append("=" * 80)
        report_lines.append("LEAN 4 LAKE BUILD ANALYSIS REPORT")
        report_lines.append("=" * 80)
        report_lines.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report_lines.append(f"Project: {self.project_root}")
        report_lines.append("")

        # Project Overview
        if 'metadata' in self.analysis_results:
            meta = self.analysis_results['metadata']
            report_lines.append("📋 PROJECT OVERVIEW")
            report_lines.append("-" * 40)
            if 'project_name' in meta:
                report_lines.append(f"Project Name: {meta['project_name']}")
            if 'lean_version' in meta:
                report_lines.append(f"Lean Version: {meta['lean_version']}")
            if 'has_executable' in meta:
                report_lines.append(f"Has Executables: {meta['has_executable']}")
            if meta.get('executable_names'):
                report_lines.append(f"Executables: {', '.join(meta['executable_names'])}")
            if 'direct_dependencies' in meta:
                report_lines.append(f"Direct Dependencies: {len(meta['direct_dependencies'])}")
            report_lines.append("")

        # Build Status
        if 'status' in self.analysis_results:
            status = self.analysis_results['status']
            report_lines.append("🏗️  BUILD STATUS")
            report_lines.append("-" * 40)
            health_emoji = {'excellent': '🟢', 'good': '🟡', 'incomplete': '🟠', 'error': '🔴'}
            report_lines.append(f"Health: {health_emoji.get(status['build_health'], '⚪')} {status['build_health'].upper()}")

            if status['missing_components']:
                report_lines.append("Missing Components:")
                for comp in status['missing_components']:
                    report_lines.append(f"  • {comp}")

            if status['warnings']:
                report_lines.append("Warnings:")
                for warn in status['warnings']:
                    report_lines.append(f"  ⚠️  {warn}")

            if status['errors']:
                report_lines.append("Errors:")
                for err in status['errors']:
                    report_lines.append(f"  ❌ {err}")

            if status['optimization_suggestions']:
                report_lines.append("Optimization Suggestions:")
                for sugg in status['optimization_suggestions']:
                    report_lines.append(f"  💡 {sugg}")
            report_lines.append("")

        # Build Artifacts
        if 'artifacts' in self.analysis_results:
            artifacts = self.analysis_results['artifacts']
            report_lines.append("🔨 BUILD ARTIFACTS")
            report_lines.append("-" * 40)
            report_lines.append(f"Total Files: {artifacts['file_count']}")
            report_lines.append(f"Total Size: {self._format_size(artifacts['total_size'])}")

            if artifacts['executables']:
                report_lines.append(f"Executables: {len(artifacts['executables'])}")
                for exe in artifacts['executables']:
                    report_lines.append(f"  • {exe['name']} ({self._format_size(exe['size'])})")

            if artifacts['libraries']:
                report_lines.append(f"Libraries: {len(artifacts['libraries'])}")

            if artifacts['source_files']:
                report_lines.append(f"Source Files: {len(artifacts['source_files'])}")
            report_lines.append("")

        # Dependencies
        if 'dependencies' in self.analysis_results:
            deps = self.analysis_results['dependencies']
            report_lines.append("📦 DEPENDENCIES")
            report_lines.append("-" * 40)
            report_lines.append(f"Total Packages: {len(deps['packages'])}")
            report_lines.append(f"Total Dependency Size: {self._format_size(deps['total_package_size'])}")

            if deps['largest_packages']:
                report_lines.append("Largest Dependencies:")
                for pkg in deps['largest_packages'][:3]:
                    report_lines.append(f"  • {pkg['name']}: {self._format_size(pkg['size'])} ({pkg['file_count']} files)")
            report_lines.append("")

        # Cache Information
        if 'cache' in self.analysis_results:
            cache = self.analysis_results['cache']
            report_lines.append("⚙️  CACHE & CONFIGURATION")
            report_lines.append("-" * 40)
            if 'platform' in cache:
                report_lines.append(f"Platform: {cache['platform']}")
            if 'lean_hash' in cache:
                report_lines.append(f"Lean Hash: {cache['lean_hash'][:12]}...")
            if 'is_locked' in cache:
                report_lines.append(f"Build Lock: {'Present' if cache['is_locked'] else 'Clear'}")
            report_lines.append("")

        return "\n".join(report_lines)

    def run_full_analysis(self) -> str:
        """Run complete analysis and return report."""
        print(f"🚀 Starting comprehensive analysis of: {self.lake_path}")
        print(f"📂 Project root: {self.project_root}")
        print()

        try:
            self.analyze_project_metadata()
            self.analyze_build_artifacts()
            self.analyze_dependencies()
            self.analyze_cache_and_config()
            self.analyze_build_status()

            report = self.generate_report()
            return report

        except Exception as e:
            error_msg = f"❌ Analysis failed: {str(e)}"
            print(error_msg)
            return error_msg

    # Helper methods
    def _extract_project_name(self, lakefile_content: str) -> str:
        """Extract project name from lakefile.lean content."""
        for line in lakefile_content.split('\n'):
            if 'package' in line and 'where' in line:
                parts = line.split()
                if len(parts) >= 2:
                    return parts[1].strip('«»"')
        return "Unknown"

    def _extract_executable_names(self, lakefile_content: str) -> List[str]:
        """Extract executable names from lakefile.lean."""
        executables = []
        for line in lakefile_content.split('\n'):
            if 'lean_exe' in line:
                parts = line.split()
                for i, part in enumerate(parts):
                    if part == 'lean_exe' and i + 1 < len(parts):
                        name = parts[i + 1].strip('«»"')
                        if name != 'where':
                            executables.append(name)
        return executables

    def _extract_dependencies(self, lakefile_content: str) -> List[str]:
        """Extract dependencies from lakefile.lean."""
        dependencies = []
        for line in lakefile_content.split('\n'):
            if 'require' in line and 'from' in line:
                parts = line.split()
                if len(parts) >= 2:
                    dep_name = parts[1]
                    dependencies.append(dep_name)
        return dependencies

    def _analyze_file(self, file_path: Path) -> Dict[str, Any]:
        """Analyze a single file and return metadata."""
        stat = file_path.stat()
        return {
            'path': str(file_path.relative_to(self.project_root)),
            'name': file_path.name,
            'size': stat.st_size,
            'modified': datetime.fromtimestamp(stat.st_mtime).isoformat(),
            'permissions': oct(stat.st_mode)[-3:],
            'extension': file_path.suffix
        }

    def _analyze_package(self, package_dir: Path) -> Dict[str, Any]:
        """Analyze a package directory."""
        total_size = 0
        file_count = 0
        lean_files = 0

        for file_path in package_dir.rglob("*"):
            if file_path.is_file():
                total_size += file_path.stat().st_size
                file_count += 1
                if file_path.suffix == '.lean':
                    lean_files += 1

        return {
            'name': package_dir.name,
            'path': str(package_dir.relative_to(self.lake_path)),
            'size': total_size,
            'file_count': file_count,
            'lean_files': lean_files,
            'subdirectories': len([d for d in package_dir.rglob("*") if d.is_dir()])
        }

    def _format_size(self, size_bytes: int) -> str:
        """Format size in human readable format."""
        for unit in ['B', 'KB', 'MB', 'GB']:
            if size_bytes < 1024.0:
                return ".1f"
            size_bytes /= 1024.0
        return ".1f"


def main():
    """Main entry point for the script."""
    parser = argparse.ArgumentParser(description="Analyze Lean 4 .lake directory")
    parser.add_argument(
        "lake_path",
        nargs="?",
        default="./.lake",
        help="Path to .lake directory (default: ./.lake)"
    )
    parser.add_argument(
        "--project-root",
        help="Path to project root (default: parent of .lake directory)"
    )
    parser.add_argument(
        "--output",
        help="Output file for report (default: print to stdout)"
    )
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)"
    )

    args = parser.parse_args()

    try:
        analyzer = LakeAnalyzer(args.lake_path, args.project_root)
        report = analyzer.run_full_analysis()

        if args.format == "json":
            import json
            output_data = {
                "analysis_results": analyzer.analysis_results,
                "report": report,
                "timestamp": datetime.now().isoformat()
            }
            output = json.dumps(output_data, indent=2)
        else:
            output = report

        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(output)
            print(f"📄 Report saved to: {args.output}")
        else:
            print(output)

    except Exception as e:
        print(f"❌ Error: {e}")
        return 1

    return 0


if __name__ == "__main__":
    exit(main())
