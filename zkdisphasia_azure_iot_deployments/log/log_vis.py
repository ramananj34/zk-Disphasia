#!/usr/bin/env python3
"""
Analyze ZK-DISPHASIA Test Harness Logs
"""

import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
from pathlib import Path
from scipy import stats

# Set style
sns.set_theme(style="whitegrid")
plt.rcParams['figure.figsize'] = (12, 6)

def load_logs(filepath):
    """Load JSONL file into pandas DataFrame"""
    print(f"Loading logs from {filepath}...")
    
    data = []
    with open(filepath, 'r') as f:
        for line in f:
            try:
                data.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    
    df = pd.DataFrame(data)
    
    # Flatten nested test_config
    if 'test_config' in df.columns:
        config_df = pd.json_normalize(df['test_config'])
        df = pd.concat([df.drop('test_config', axis=1), config_df], axis=1)
    
    print(f"✓ Loaded {len(df)} test results")
    return df

def basic_statistics(df):
    """Print basic statistics"""
    print("\n" + "="*60)
    print("BASIC STATISTICS")
    print("="*60)
    
    # Overall summary
    total_tests = len(df)
    successes = (df['status'] == 'SUCCESS').sum()
    failures = (df['status'] == 'FAILED').sum()
    
    print(f"\nTotal tests: {total_tests}")
    print(f"Successes: {successes} ({successes/total_tests*100:.1f}%)")
    print(f"Failures: {failures} ({failures/total_tests*100:.1f}%)")
    
    if failures > 0:
        print("\nFailure reasons:")
        print(df[df['status'] == 'FAILED']['failure_reason'].value_counts())
    
    # Filter successful tests for metrics
    success_df = df[df['status'] == 'SUCCESS'].copy()
    
    # Timing statistics (convert to milliseconds)
    print("\n" + "-"*60)
    print("TIMING METRICS (milliseconds)")
    print("-"*60)
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    
    timing_stats = success_df['wall_time_ms'].describe()
    print(f"Wall time: min={timing_stats['min']:.2f}ms, "
          f"mean={timing_stats['mean']:.2f}ms, "
          f"median={timing_stats['50%']:.2f}ms, "
          f"max={timing_stats['max']:.2f}ms")
    
    # Memory statistics (MB)
    print("\n" + "-"*60)
    print("MEMORY METRICS (MB)")
    print("-"*60)
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    success_df['delta_rss_mb'] = success_df['delta_rss_kb'] / 1024
    
    mem_stats = success_df['peak_rss_mb'].describe()
    print(f"Peak RSS: min={mem_stats['min']:.2f}MB, "
          f"mean={mem_stats['mean']:.2f}MB, "
          f"median={mem_stats['50%']:.2f}MB, "
          f"max={mem_stats['max']:.2f}MB")
    
    # Energy statistics
    if 'energy_estimate_joules' in success_df.columns:
        # Filter out None values
        energy_data = success_df['energy_estimate_joules'].dropna()
        if len(energy_data) > 0:
            print("\n" + "-"*60)
            print("ENERGY METRICS (Joules)")
            print("-"*60)
            energy_stats = energy_data.describe()
            print(f"Energy: min={energy_stats['min']:.4f}J, "
                f"mean={energy_stats['mean']:.4f}J, "
                f"median={energy_stats['50%']:.4f}J, "
                f"max={energy_stats['max']:.4f}J")
        else:
            print("\n⚠ No energy data available")

def function_comparison(df):
    """Compare performance across functions"""
    print("\n" + "="*60)
    print("PERFORMANCE BY FUNCTION")
    print("="*60)
    
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    # Group by function
    func_stats = success_df.groupby('function').agg({
        'wall_time_ms': ['mean', 'std', 'min', 'max'],
        'peak_rss_mb': ['mean', 'std'],
        'output_size_bytes': 'mean'
    }).round(2)
    
    print("\n", func_stats)
    
    return success_df

def network_size_scaling(df):
    """Analyze how metrics scale with network size"""
    print("\n" + "="*60)
    print("SCALING WITH NETWORK SIZE (n)")
    print("="*60)
    
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    
    # Group by n and function
    scaling = success_df.groupby(['n', 'function'])['wall_time_ms'].mean().reset_index()
    
    print("\nAverage wall time (ms) by network size:")
    pivot = scaling.pivot(index='n', columns='function', values='wall_time_ms')
    print(pivot.round(2))
    
    return scaling

def zkp_comparison(df):
    """Compare ZKP types (for ProofGen and ProofVerify only)"""
    print("\n" + "="*60)
    print("ZKP TYPE COMPARISON")
    print("="*60)
    
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024  # <-- ADD THIS LINE
    
    # Filter ZKP-specific functions
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])].copy()
    
    if len(zkp_df) == 0:
        print("No ZKP-specific tests found")
        return None
    
    # Group by ZKP type and function
    agg_dict = {
        'wall_time_ms': ['mean', 'std'],
        'peak_rss_mb': 'mean'
    }
    
    # Only include energy if it exists
    if 'energy_estimate_joules' in zkp_df.columns and zkp_df['energy_estimate_joules'].notna().any():
        agg_dict['energy_estimate_joules'] = 'mean'
    
    zkp_stats = zkp_df.groupby(['zkp_type', 'function']).agg(agg_dict).round(2)
    
    print("\n", zkp_stats)
    
    return zkp_df

def create_visualizations(df, output_dir='plots'):
    """Create visualization plots"""
    print("\n" + "="*60)
    print("CREATING VISUALIZATIONS")
    print("="*60)
    
    Path(output_dir).mkdir(exist_ok=True)
    
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    # 1. Wall time by function
    plt.figure(figsize=(12, 6))
    sns.boxplot(data=success_df, x='function', y='wall_time_ms')
    plt.xticks(rotation=45)
    plt.ylabel('Wall Time (ms)')
    plt.title('Execution Time by Function')
    plt.tight_layout()
    plt.savefig(f'{output_dir}/time_by_function.png', dpi=150)
    print(f"✓ Saved {output_dir}/time_by_function.png")
    plt.close()
    
    # 2. Scaling with network size
    plt.figure(figsize=(12, 6))
    for func in success_df['function'].unique():
        func_data = success_df[success_df['function'] == func]
        scaling = func_data.groupby('n')['wall_time_ms'].mean()
        plt.plot(scaling.index, scaling.values, marker='o', label=func)
    
    plt.xlabel('Network Size (n)')
    plt.ylabel('Average Wall Time (ms)')
    plt.title('Performance Scaling with Network Size')
    plt.legend()
    plt.xscale('log')
    plt.yscale('log')
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f'{output_dir}/scaling_by_n.png', dpi=150)
    print(f"✓ Saved {output_dir}/scaling_by_n.png")
    plt.close()
    
    # 3. Memory usage by function
    plt.figure(figsize=(12, 6))
    sns.boxplot(data=success_df, x='function', y='peak_rss_mb')
    plt.xticks(rotation=45)
    plt.ylabel('Peak RSS (MB)')
    plt.title('Memory Usage by Function')
    plt.tight_layout()
    plt.savefig(f'{output_dir}/memory_by_function.png', dpi=150)
    print(f"✓ Saved {output_dir}/memory_by_function.png")
    plt.close()
    
    # 4. ZKP comparison (if available)
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])]
    if len(zkp_df) > 0 and 'zkp_type' in zkp_df.columns:
        plt.figure(figsize=(12, 6))
        sns.barplot(data=zkp_df, x='function', y='wall_time_ms', hue='zkp_type')
        plt.ylabel('Wall Time (ms)')
        plt.title('ZKP Type Comparison')
        plt.tight_layout()
        plt.savefig(f'{output_dir}/zkp_comparison.png', dpi=150)
        print(f"✓ Saved {output_dir}/zkp_comparison.png")
        plt.close()
    
    # 5. Energy consumption
    if 'energy_estimate_joules' in success_df.columns:
        # Filter out None/NaN values
        energy_data = success_df[success_df['energy_estimate_joules'].notna()].copy()
        
        if len(energy_data) > 0:
            plt.figure(figsize=(12, 6))
            sns.boxplot(data=energy_data, x='function', y='energy_estimate_joules')
            plt.xticks(rotation=45)
            plt.ylabel('Energy (Joules)')
            plt.title('Energy Consumption by Function')
            plt.tight_layout()
            plt.savefig(f'{output_dir}/energy_by_function.png', dpi=150)
            print(f"✓ Saved {output_dir}/energy_by_function.png")
            plt.close()
        else:
            print(f"⚠ Skipped energy_by_function.png (no energy data)")
    
    # 6. Time vs n scatter (all functions)
    plt.figure(figsize=(14, 8))
    for func in success_df['function'].unique():
        func_data = success_df[success_df['function'] == func]
        plt.scatter(func_data['n'], func_data['wall_time_ms'], 
                   alpha=0.5, label=func, s=20)
    
    plt.xlabel('Network Size (n)')
    plt.ylabel('Wall Time (ms)')
    plt.title('Performance Distribution across Network Sizes')
    plt.legend()
    plt.xscale('log')
    plt.yscale('log')
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f'{output_dir}/scatter_time_vs_n.png', dpi=150)
    print(f"✓ Saved {output_dir}/scatter_time_vs_n.png")
    plt.close()

def export_summary_csv(df, output_file='summary_statistics.csv'):
    """Export summary statistics to CSV"""
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    # Calculate summary by function and n
    summary = success_df.groupby(['function', 'n']).agg({
        'wall_time_ms': ['mean', 'std', 'min', 'max'],
        'peak_rss_mb': ['mean', 'std'],
        'delta_rss_kb': 'mean',
        'energy_estimate_joules': 'mean',
        'output_size_bytes': 'mean',
        'run': 'count'  # Number of runs
    }).round(4)
    
    summary.to_csv(output_file)
    print(f"\n✓ Exported summary statistics to {output_file}")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='Analyze ZK-DISPHASIA test logs')
    parser.add_argument('logfile', help='Path to JSONL log file')
    parser.add_argument('--plots', default='plots', help='Output directory for plots')
    parser.add_argument('--csv', default='summary.csv', help='Output CSV file')
    parser.add_argument('--no-plots', action='store_true', help='Skip plot generation')
    
    args = parser.parse_args()
    
    # Load data
    df = load_logs(args.logfile)
    
    # Run analyses
    basic_statistics(df)
    function_comparison(df)
    network_size_scaling(df)
    zkp_comparison(df)
    
    # Create visualizations
    if not args.no_plots:
        create_visualizations(df, args.plots)
    
    # Export summary
    export_summary_csv(df, args.csv)
    
    print("\n" + "="*60)
    print("ANALYSIS COMPLETE")
    print("="*60)

if __name__ == '__main__':
    main()