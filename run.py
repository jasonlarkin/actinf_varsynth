#!/usr/bin/env python3
"""
Lean-FEP Proof Runner
=====================

This script runs all Lean proofs in the src/ directory and saves outputs to a configurable folder.
It automatically discovers all .lean files and executes them using Lake.

Usage:
    python run.py --output-dir ./proof_outputs --verbose
    python run.py --config config.json
"""

import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any
import re


class LeanProofRunner:
    """Main class for running Lean proofs and collecting outputs."""

    def __init__(self, src_dir: str = "src", lake_cmd: str = "lake"):
        """
        Initialize the proof runner.

        Args:
            src_dir: Directory containing Lean source files
            lake_cmd: Lake command to use (default: 'lake')
        """
        self.src_dir = Path(src_dir)
        self.lake_cmd = lake_cmd
        self.results = {}
        self.errors = []

        if not self.src_dir.exists():
            raise FileNotFoundError(f"Source directory {src_dir} does not exist")

    def find_lean_files(self) -> List[Path]:
        """Find all .lean files in the source directory."""
        return sorted(list(self.src_dir.glob("*.lean")))

    def run_lean_file(self, file_path: Path, verbose: bool = False) -> Dict[str, Any]:
        """
        Run a single Lean file and capture output.

        Args:
            file_path: Path to the Lean file
            verbose: Whether to show detailed output

        Returns:
            Dictionary containing results
        """
        result = {
            'file': str(file_path),
            'success': False,
            'output': '',
            'error': '',
            'runtime': 0.0,
            'timestamp': datetime.now().isoformat()
        }

        start_time = time.time()

        try:
            # Run the Lean file
            cmd = [self.lake_cmd, "env", "lean", "--run", str(file_path)]
            process = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,  # 5 minute timeout
                cwd=Path.cwd()
            )

            result['runtime'] = time.time() - start_time

            if process.returncode == 0:
                result['success'] = True
                result['output'] = process.stdout
                if verbose:
                    print(f"✅ {file_path.name}: SUCCESS")
            else:
                result['error'] = f"Exit code {process.returncode}\nStdout: {process.stdout}\nStderr: {process.stderr}"
                if verbose:
                    print(f"❌ {file_path.name}: FAILED (exit code {process.returncode})")

        except subprocess.TimeoutExpired:
            result['error'] = "Timeout after 5 minutes"
            result['runtime'] = time.time() - start_time
            if verbose:
                print(f"⏰ {file_path.name}: TIMEOUT")
        except Exception as e:
            result['error'] = str(e)
            result['runtime'] = time.time() - start_time
            if verbose:
                print(f"💥 {file_path.name}: ERROR - {e}")

        return result

    def extract_eval_outputs(self, output: str) -> List[str]:
        """Extract #eval outputs from Lean output."""
        lines = output.strip().split('\n')
        eval_lines = [line.strip() for line in lines if line.strip()]
        return eval_lines

    def generate_summary(self) -> Dict[str, Any]:
        """Generate summary statistics."""
        total_files = len(self.results)
        successful = sum(1 for r in self.results.values() if r['success'])
        failed = total_files - successful

        total_runtime = sum(r['runtime'] for r in self.results.values())

        # Extract all eval outputs
        all_eval_outputs = []
        for result in self.results.values():
            if result['success'] and result['output']:
                eval_lines = self.extract_eval_outputs(result['output'])
                all_eval_outputs.extend(eval_lines)

        return {
            'total_files': total_files,
            'successful': successful,
            'failed': failed,
            'success_rate': f"{(successful/total_files*100):.1f}%" if total_files > 0 else "0%",
            'total_runtime': f"{total_runtime:.2f}s",
            'all_eval_outputs': all_eval_outputs,
            'errors': [r['error'] for r in self.results.values() if not r['success']],
            'timestamp': datetime.now().isoformat()
        }

    def save_results(self, output_dir: Path) -> None:
        """Save all results to files."""
        output_dir.mkdir(parents=True, exist_ok=True)

        # Save individual results
        individual_dir = output_dir / "individual_results"
        individual_dir.mkdir(exist_ok=True)

        for file_path, result in self.results.items():
            filename = Path(file_path).stem + ".json"
            with open(individual_dir / filename, 'w') as f:
                json.dump(result, f, indent=2)

        # Save summary
        summary = self.generate_summary()
        with open(output_dir / "summary.json", 'w') as f:
            json.dump(summary, f, indent=2)

        # Save human-readable summary
        with open(output_dir / "README.md", 'w') as f:
            f.write("# Lean-FEP Proof Execution Summary\n\n")
            f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")

            f.write("## 📊 Statistics\n\n")
            f.write(f"- **Total Files**: {summary['total_files']}\n")
            f.write(f"- **Successful**: {summary['successful']}\n")
            f.write(f"- **Failed**: {summary['failed']}\n")
            f.write(f"- **Success Rate**: {summary['success_rate']}\n")
            f.write(f"- **Total Runtime**: {summary['total_runtime']}\n\n")

            f.write("## 🎉 All Proof Outputs\n\n")
            for i, output in enumerate(summary['all_eval_outputs'], 1):
                f.write(f"{i}. {output}\n")
            f.write("\n")

            if summary['errors']:
                f.write("## ❌ Errors\n\n")
                for i, error in enumerate(summary['errors'], 1):
                    f.write(f"### Error {i}\n```\n{error}\n```\n\n")

        # Save raw outputs
        raw_dir = output_dir / "raw_outputs"
        raw_dir.mkdir(exist_ok=True)

        for file_path, result in self.results.items():
            filename = Path(file_path).stem + ".txt"
            with open(raw_dir / filename, 'w') as f:
                f.write(f"File: {result['file']}\n")
                f.write(f"Timestamp: {result['timestamp']}\n")
                f.write(f"Runtime: {result['runtime']:.2f}s\n")
                f.write(f"Success: {result['success']}\n\n")

                if result['success']:
                    f.write("=== OUTPUT ===\n")
                    f.write(result['output'])
                else:
                    f.write("=== ERROR ===\n")
                    f.write(result['error'])

    def run_all_proofs(self, verbose: bool = False) -> Dict[str, Any]:
        """Run all Lean proofs and return results."""
        lean_files = self.find_lean_files()

        if verbose:
            print(f"🔍 Found {len(lean_files)} Lean files:")
            for file in lean_files:
                print(f"  - {file.name}")
            print()

        for file_path in lean_files:
            if verbose:
                print(f"🚀 Running {file_path.name}...")

            result = self.run_lean_file(file_path, verbose)
            self.results[str(file_path)] = result

            if not result['success']:
                self.errors.append({
                    'file': str(file_path),
                    'error': result['error']
                })

        return self.generate_summary()


def load_config(config_file: str) -> Dict[str, Any]:
    """Load configuration from JSON file."""
    with open(config_file, 'r') as f:
        return json.load(f)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Run Lean-FEP proofs and collect outputs")
    parser.add_argument(
        "--output-dir",
        type=str,
        default="./proof_outputs",
        help="Output directory for results (default: ./proof_outputs)"
    )
    parser.add_argument(
        "--src-dir",
        type=str,
        default="src",
        help="Source directory containing Lean files (default: src)"
    )
    parser.add_argument(
        "--config",
        type=str,
        help="Configuration file (JSON format)"
    )
    parser.add_argument(
        "--lake-cmd",
        type=str,
        default="lake",
        help="Lake command to use (default: lake)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be run without executing"
    )

    args = parser.parse_args()

    # Load config if provided
    config = {}
    if args.config:
        try:
            config = load_config(args.config)
        except Exception as e:
            print(f"❌ Error loading config: {e}")
            sys.exit(1)

    # Override config with command line arguments
    final_config = {
        'output_dir': args.output_dir,
        'src_dir': args.src_dir,
        'lake_cmd': args.lake_cmd,
        'verbose': args.verbose,
        **config
    }

    # Create timestamped output directory
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = Path(final_config['output_dir']) / f"run_{timestamp}"

    if args.dry_run:
        print("🔍 DRY RUN MODE")
        print(f"Output directory: {output_dir}")
        print(f"Source directory: {final_config['src_dir']}")
        print(f"Lake command: {final_config['lake_cmd']}")

        runner = LeanProofRunner(final_config['src_dir'], final_config['lake_cmd'])
        lean_files = runner.find_lean_files()
        print(f"Would run {len(lean_files)} files:")
        for file in lean_files:
            print(f"  - {file.name}")
        return

    try:
        # Initialize runner
        runner = LeanProofRunner(final_config['src_dir'], final_config['lake_cmd'])

        # Run all proofs
        if final_config['verbose']:
            print("🚀 Starting Lean-FEP proof execution...")
            print(f"Output directory: {output_dir}")
            print()

        summary = runner.run_all_proofs(final_config['verbose'])

        # Save results
        runner.save_results(output_dir)

        # Print summary
        print("\n📊 EXECUTION SUMMARY")
        print(f"Total Files: {summary['total_files']}")
        print(f"Successful: {summary['successful']}")
        print(f"Failed: {summary['failed']}")
        print(f"Success Rate: {summary['success_rate']}")
        print(f"Total Runtime: {summary['total_runtime']}")
        print(f"Results saved to: {output_dir}")

        if summary['all_eval_outputs']:
            print("\n🎉 PROOF OUTPUTS:")
            for i, output in enumerate(summary['all_eval_outputs'], 1):
                print(f"  {i}. {output}")

        if summary['errors']:
            print("\n❌ ERRORS:")
            for i, error in enumerate(summary['errors'], 1):
                print(f"  {i}. {error}")

        # Exit with appropriate code
        sys.exit(0 if summary['failed'] == 0 else 1)

    except Exception as e:
        print(f"💥 Fatal error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
