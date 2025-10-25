#This was made with AI Assistance

import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
from pathlib import Path

sns.set_theme(style="whitegrid")
plt.rcParams['figure.figsize'] = (12, 6)

def load_logs(filepath):
    print(f"Loading logs from {filepath}...")
    data = []
    with open(filepath, 'r') as f:
        for line in f:
            try: data.append(json.loads(line))
            except json.JSONDecodeError: continue
    df = pd.DataFrame(data)
    if 'test_config' in df.columns:
        config_df = pd.json_normalize(df['test_config'])
        df = pd.concat([df.drop('test_config', axis=1), config_df], axis=1)
    print(f"✓ Loaded {len(df)} test results")
    return df

def basic_statistics(df):
    print("\n" + "="*60 + "\nBASIC STATISTICS\n" + "="*60)
    total_tests = len(df)
    successes = (df['status'] == 'SUCCESS').sum()
    failures = (df['status'] == 'FAILED').sum()
    print(f"\nTotal tests: {total_tests}\nSuccesses: {successes} ({successes/total_tests*100:.1f}%)\nFailures: {failures} ({failures/total_tests*100:.1f}%)")
    if failures > 0:
        print("\nFailure reasons:")
        print(df[df['status'] == 'FAILED']['failure_reason'].value_counts())
    
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    print("\n" + "-"*60 + "\nTEST DISTRIBUTION\n" + "-"*60)
    print("\nTests by function:")
    print(success_df['function'].value_counts().sort_index())
    
    zkp_tests = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])]
    if len(zkp_tests) > 0:
        print("\nZKP tests by type:")
        print(zkp_tests.groupby(['function', 'zkp_type']).size().unstack(fill_value=0))

def network_scaled_analysis(df):
    """Analyze functions that scale with network size: DKG1, DKG2, DKG3, PartialGen, AggCompute"""
    print("\n" + "="*60 + "\nNETWORK-SCALED FUNCTIONS\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    scaled_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'AggCompute']
    scaled_df = success_df[success_df['function'].isin(scaled_funcs)].copy()
    
    if len(scaled_df) == 0:
        print("No network-scaled tests found")
        return None
    
    scaled_df['wall_time_ms'] = scaled_df['wall_time_us'] / 1000
    scaled_df['peak_rss_mb'] = scaled_df['peak_rss_kb'] / 1024
    scaled_df['t_ratio'] = scaled_df['t'] / scaled_df['n']
    
    print("\n--- Performance by Network Size ---")
    print("\nMean wall time (ms) by function and n:")
    pivot = scaled_df.groupby(['function', 'n'])['wall_time_ms'].mean().unstack()
    print(pivot.round(2))
    
    print("\n--- Scaling Factors ---")
    for func in scaled_funcs:
        func_data = scaled_df[scaled_df['function'] == func]
        scaling = func_data.groupby('n')['wall_time_ms'].mean().sort_index()
        if len(scaling) > 1:
            growth = scaling.iloc[-1] / scaling.iloc[0]
            print(f"\n{func}:")
            print(f"  n={scaling.index[0]}: {scaling.iloc[0]:.2f}ms")
            print(f"  n={scaling.index[-1]}: {scaling.iloc[-1]:.2f}ms")
            print(f"  Growth factor: {growth:.2f}x")
    
    print("\n--- Threshold Ratio Impact ---")
    print("\nMean wall time (ms) by function and threshold ratio:")
    threshold_pivot = scaled_df.groupby(['function', 't_ratio'])['wall_time_ms'].mean().unstack()
    print(threshold_pivot.round(2))
    
    print("\n--- Memory Usage ---")
    print("\nMean peak RSS (MB) by function and n:")
    mem_pivot = scaled_df.groupby(['function', 'n'])['peak_rss_mb'].mean().unstack()
    print(mem_pivot.round(2))
    
    if 'energy_estimate_joules' in scaled_df.columns:
        energy_data = scaled_df['energy_estimate_joules'].dropna()
        if len(energy_data) > 0:
            print("\n--- Energy Usage ---")
            print("\nMean energy (J) by function and n:")
            energy_pivot = scaled_df.groupby(['function', 'n'])['energy_estimate_joules'].mean().unstack()
            print(energy_pivot.round(4))
    
    return scaled_df

def partial_verify_analysis(df):
    """Analyze PartialVerify (tested once at n=5, t=3)"""
    print("\n" + "="*60 + "\nPARTIAL VERIFY (Single Configuration)\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    pv_df = success_df[success_df['function'] == 'PartialVerify'].copy()
    
    if len(pv_df) == 0:
        print("No PartialVerify tests found")
        return None
    
    pv_df['wall_time_ms'] = pv_df['wall_time_us'] / 1000
    pv_df['peak_rss_mb'] = pv_df['peak_rss_kb'] / 1024
    
    print(f"\nTested at n={pv_df['n'].iloc[0]}, t={pv_df['t'].iloc[0]}")
    print(f"Number of runs: {len(pv_df)}")
    
    stats = pv_df['wall_time_ms'].describe()
    print(f"\nWall time statistics:")
    print(f"  Mean: {stats['mean']:.2f}ms")
    print(f"  Std:  {stats['std']:.2f}ms")
    print(f"  Min:  {stats['min']:.2f}ms")
    print(f"  Max:  {stats['max']:.2f}ms")
    
    mem_stats = pv_df['peak_rss_mb'].describe()
    print(f"\nMemory statistics:")
    print(f"  Mean: {mem_stats['mean']:.2f}MB")
    print(f"  Std:  {mem_stats['std']:.2f}MB")
    
    if 'energy_estimate_joules' in pv_df.columns:
        energy_data = pv_df['energy_estimate_joules'].dropna()
        if len(energy_data) > 0:
            energy_stats = energy_data.describe()
            print(f"\nEnergy statistics:")
            print(f"  Mean: {energy_stats['mean']:.4f}J")
            print(f"  Std:  {energy_stats['std']:.4f}J")
    
    return pv_df

def zkp_comparison_analysis(df):
    """Compare ZKP types for ProofGen and ProofVerify (tested at n=5, t=3)"""
    print("\n" + "="*60 + "\nZKP TYPE COMPARISON\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    zkp_funcs = ['ProofGen', 'ProofVerify']
    zkp_df = success_df[success_df['function'].isin(zkp_funcs)].copy()
    
    if len(zkp_df) == 0:
        print("No ZKP tests found")
        return None
    
    zkp_df['wall_time_ms'] = zkp_df['wall_time_us'] / 1000
    zkp_df['peak_rss_mb'] = zkp_df['peak_rss_kb'] / 1024
    
    print(f"\nAll tests at n={zkp_df['n'].iloc[0]}, t={zkp_df['t'].iloc[0]}")
    
    print("\n--- ProofGen Performance ---")
    proofgen = zkp_df[zkp_df['function'] == 'ProofGen']
    pg_summary = proofgen.groupby('zkp_type')['wall_time_ms'].agg(['mean', 'std', 'min', 'max', 'count'])
    print("\nWall time by ZKP type:")
    print(pg_summary.round(2))
    
    print("\n--- ProofVerify Performance ---")
    proofverify = zkp_df[zkp_df['function'] == 'ProofVerify']
    pv_summary = proofverify.groupby('zkp_type')['wall_time_ms'].agg(['mean', 'std', 'min', 'max', 'count'])
    print("\nWall time by ZKP type:")
    print(pv_summary.round(2))
    
    print("\n--- Memory Comparison ---")
    print("\nProofGen memory (MB) by ZKP type:")
    pg_mem = proofgen.groupby('zkp_type')['peak_rss_mb'].agg(['mean', 'std'])
    print(pg_mem.round(2))
    
    print("\nProofVerify memory (MB) by ZKP type:")
    pv_mem = proofverify.groupby('zkp_type')['peak_rss_mb'].agg(['mean', 'std'])
    print(pv_mem.round(2))
    
    if 'energy_estimate_joules' in zkp_df.columns:
        energy_data = zkp_df['energy_estimate_joules'].dropna()
        if len(energy_data) > 0:
            print("\n--- Energy Comparison ---")
            print("\nProofGen energy (J) by ZKP type:")
            pg_energy = proofgen.groupby('zkp_type')['energy_estimate_joules'].agg(['mean', 'std'])
            print(pg_energy.round(4))
            
            print("\nProofVerify energy (J) by ZKP type:")
            pv_energy = proofverify.groupby('zkp_type')['energy_estimate_joules'].agg(['mean', 'std'])
            print(pv_energy.round(4))
    
    print("\n--- Rankings ---")
    print("\nProofGen (fastest to slowest):")
    pg_ranking = proofgen.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
    for zkp_type, time in pg_ranking.items():
        print(f"  {zkp_type}: {time:.2f}ms")
    
    print("\nProofVerify (fastest to slowest):")
    pv_ranking = proofverify.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
    for zkp_type, time in pv_ranking.items():
        print(f"  {zkp_type}: {time:.2f}ms")
    
    print("\n--- Relative Performance ---")
    if len(pg_ranking) > 1:
        fastest_pg = pg_ranking.iloc[0]
        print("\nProofGen relative to fastest:")
        for zkp_type, time in pg_ranking.items():
            ratio = time / fastest_pg
            print(f"  {zkp_type}: {ratio:.2f}x")
    
    if len(pv_ranking) > 1:
        fastest_pv = pv_ranking.iloc[0]
        print("\nProofVerify relative to fastest:")
        for zkp_type, time in pv_ranking.items():
            ratio = time / fastest_pv
            print(f"  {zkp_type}: {ratio:.2f}x")
    
    return zkp_df

def create_visualizations(df, output_dir='plots'):
    print("\n" + "="*60 + "\nCREATING VISUALIZATIONS\n" + "="*60)
    Path(output_dir).mkdir(exist_ok=True)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    # 1. Network-scaled functions: Time scaling
    scaled_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'AggCompute']
    scaled_df = success_df[success_df['function'].isin(scaled_funcs)]
    
    if len(scaled_df) > 0:
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        # Linear scale
        for func in scaled_funcs:
            func_data = scaled_df[scaled_df['function'] == func]
            scaling = func_data.groupby('n')['wall_time_ms'].mean()
            ax1.plot(scaling.index, scaling.values, marker='o', label=func, linewidth=2, markersize=8)
        ax1.set_xlabel('Network Size (n)', fontsize=12)
        ax1.set_ylabel('Average Wall Time (ms)', fontsize=12)
        ax1.set_title('Network-Scaled Functions: Linear Scale', fontsize=14)
        ax1.legend()
        ax1.grid(True, alpha=0.3)
        
        # Log scale
        for func in scaled_funcs:
            func_data = scaled_df[scaled_df['function'] == func]
            scaling = func_data.groupby('n')['wall_time_ms'].mean()
            ax2.plot(scaling.index, scaling.values, marker='o', label=func, linewidth=2, markersize=8)
        ax2.set_xlabel('Network Size (n)', fontsize=12)
        ax2.set_ylabel('Average Wall Time (ms)', fontsize=12)
        ax2.set_title('Network-Scaled Functions: Log Scale', fontsize=14)
        ax2.legend()
        ax2.set_xscale('log')
        ax2.set_yscale('log')
        ax2.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig(f'{output_dir}/network_scaling.png', dpi=150)
        print(f"✓ Saved {output_dir}/network_scaling.png")
        plt.close()
        
        # 2. Memory scaling
        plt.figure(figsize=(14, 8))
        for func in scaled_funcs:
            func_data = scaled_df[scaled_df['function'] == func]
            mem_scaling = func_data.groupby('n')['peak_rss_mb'].mean()
            plt.plot(mem_scaling.index, mem_scaling.values, marker='o', label=func, linewidth=2, markersize=8)
        plt.xlabel('Network Size (n)', fontsize=12)
        plt.ylabel('Peak Memory (MB)', fontsize=12)
        plt.title('Network-Scaled Functions: Memory Usage', fontsize=14)
        plt.legend()
        plt.xscale('log')
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.savefig(f'{output_dir}/memory_scaling.png', dpi=150)
        print(f"✓ Saved {output_dir}/memory_scaling.png")
        plt.close()
        
        # 3. Threshold ratio impact
        scaled_df['t_ratio'] = (scaled_df['t'] / scaled_df['n']).round(2)
        fig, axes = plt.subplots(2, 3, figsize=(18, 12))
        for idx, func in enumerate(scaled_funcs):
            ax = axes[idx // 3, idx % 3]
            func_data = scaled_df[scaled_df['function'] == func]
            ratio_means = func_data.groupby('t_ratio')['wall_time_ms'].mean()
            ax.bar(range(len(ratio_means)), ratio_means.values, color='steelblue')
            ax.set_xticks(range(len(ratio_means)))
            ax.set_xticklabels([f'{r:.2f}' for r in ratio_means.index])
            ax.set_xlabel('Threshold Ratio (t/n)')
            ax.set_ylabel('Wall Time (ms)')
            ax.set_title(f'{func}')
            ax.grid(axis='y', alpha=0.3)
        plt.suptitle('Threshold Ratio Impact on Performance', fontsize=16, y=1.00)
        plt.tight_layout()
        plt.savefig(f'{output_dir}/threshold_impact.png', dpi=150)
        print(f"✓ Saved {output_dir}/threshold_impact.png")
        plt.close()
    
    # 4. ZKP comparison
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])]
    if len(zkp_df) > 0:
        fig, axes = plt.subplots(2, 2, figsize=(16, 12))
        
        proofgen = zkp_df[zkp_df['function'] == 'ProofGen']
        proofverify = zkp_df[zkp_df['function'] == 'ProofVerify']
        
        # ProofGen time
        pg_means = proofgen.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
        pg_stds = proofgen.groupby('zkp_type')['wall_time_ms'].std().reindex(pg_means.index)
        axes[0, 0].bar(range(len(pg_means)), pg_means.values, yerr=pg_stds.values, 
                       color=['#1f77b4', '#ff7f0e', '#2ca02c'], capsize=5)
        axes[0, 0].set_xticks(range(len(pg_means)))
        axes[0, 0].set_xticklabels(pg_means.index)
        axes[0, 0].set_ylabel('Wall Time (ms)')
        axes[0, 0].set_title('ProofGen: Time Comparison')
        axes[0, 0].grid(axis='y', alpha=0.3)
        
        # ProofVerify time
        pv_means = proofverify.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
        pv_stds = proofverify.groupby('zkp_type')['wall_time_ms'].std().reindex(pv_means.index)
        axes[0, 1].bar(range(len(pv_means)), pv_means.values, yerr=pv_stds.values,
                       color=['#1f77b4', '#ff7f0e', '#2ca02c'], capsize=5)
        axes[0, 1].set_xticks(range(len(pv_means)))
        axes[0, 1].set_xticklabels(pv_means.index)
        axes[0, 1].set_ylabel('Wall Time (ms)')
        axes[0, 1].set_title('ProofVerify: Time Comparison')
        axes[0, 1].grid(axis='y', alpha=0.3)
        
        # ProofGen memory
        pg_mem_means = proofgen.groupby('zkp_type')['peak_rss_mb'].mean().sort_values()
        pg_mem_stds = proofgen.groupby('zkp_type')['peak_rss_mb'].std().reindex(pg_mem_means.index)
        axes[1, 0].bar(range(len(pg_mem_means)), pg_mem_means.values, yerr=pg_mem_stds.values,
                       color=['#1f77b4', '#ff7f0e', '#2ca02c'], capsize=5)
        axes[1, 0].set_xticks(range(len(pg_mem_means)))
        axes[1, 0].set_xticklabels(pg_mem_means.index)
        axes[1, 0].set_ylabel('Peak Memory (MB)')
        axes[1, 0].set_title('ProofGen: Memory Comparison')
        axes[1, 0].grid(axis='y', alpha=0.3)
        
        # ProofVerify memory
        pv_mem_means = proofverify.groupby('zkp_type')['peak_rss_mb'].mean().sort_values()
        pv_mem_stds = proofverify.groupby('zkp_type')['peak_rss_mb'].std().reindex(pv_mem_means.index)
        axes[1, 1].bar(range(len(pv_mem_means)), pv_mem_means.values, yerr=pv_mem_stds.values,
                       color=['#1f77b4', '#ff7f0e', '#2ca02c'], capsize=5)
        axes[1, 1].set_xticks(range(len(pv_mem_means)))
        axes[1, 1].set_xticklabels(pv_mem_means.index)
        axes[1, 1].set_ylabel('Peak Memory (MB)')
        axes[1, 1].set_title('ProofVerify: Memory Comparison')
        axes[1, 1].grid(axis='y', alpha=0.3)
        
        plt.suptitle('ZKP Type Comparison (n=5, t=3)', fontsize=16, y=1.00)
        plt.tight_layout()
        plt.savefig(f'{output_dir}/zkp_comparison.png', dpi=150)
        print(f"✓ Saved {output_dir}/zkp_comparison.png")
        plt.close()
        
        # 5. ZKP energy comparison (if available)
        if 'energy_estimate_joules' in zkp_df.columns:
            energy_data = zkp_df['energy_estimate_joules'].dropna()
            if len(energy_data) > 0:
                fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
                
                pg_energy = proofgen.groupby('zkp_type')['energy_estimate_joules'].mean().sort_values()
                ax1.bar(range(len(pg_energy)), pg_energy.values, color=['#1f77b4', '#ff7f0e', '#2ca02c'])
                ax1.set_xticks(range(len(pg_energy)))
                ax1.set_xticklabels(pg_energy.index)
                ax1.set_ylabel('Energy (Joules)')
                ax1.set_title('ProofGen: Energy Consumption')
                ax1.grid(axis='y', alpha=0.3)
                
                pv_energy = proofverify.groupby('zkp_type')['energy_estimate_joules'].mean().sort_values()
                ax2.bar(range(len(pv_energy)), pv_energy.values, color=['#1f77b4', '#ff7f0e', '#2ca02c'])
                ax2.set_xticks(range(len(pv_energy)))
                ax2.set_xticklabels(pv_energy.index)
                ax2.set_ylabel('Energy (Joules)')
                ax2.set_title('ProofVerify: Energy Consumption')
                ax2.grid(axis='y', alpha=0.3)
                
                plt.suptitle('ZKP Energy Comparison (n=5, t=3)', fontsize=16, y=1.00)
                plt.tight_layout()
                plt.savefig(f'{output_dir}/zkp_energy.png', dpi=150)
                print(f"✓ Saved {output_dir}/zkp_energy.png")
                plt.close()

def export_summary_csvs(df, output_dir='.'):
    """Export summary statistics to CSV"""
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    
    # 1. Network-scaled functions
    scaled_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'AggCompute']
    scaled_df = success_df[success_df['function'].isin(scaled_funcs)]
    if len(scaled_df) > 0:
        scaled_summary = scaled_df.groupby(['function', 'n', 't']).agg({
            'wall_time_ms': ['mean', 'std', 'min', 'max'],
            'peak_rss_mb': ['mean', 'std'],
            'energy_estimate_joules': 'mean',
            'run': 'count'
        }).round(4)
        scaled_summary.to_csv(f'{output_dir}/network_scaled_summary.csv')
        print(f"✓ Exported {output_dir}/network_scaled_summary.csv")
    
    # 2. PartialVerify
    pv_df = success_df[success_df['function'] == 'PartialVerify']
    if len(pv_df) > 0:
        pv_summary = pv_df[['wall_time_ms', 'peak_rss_mb', 'energy_estimate_joules']].describe()
        pv_summary.to_csv(f'{output_dir}/partial_verify_summary.csv')
        print(f"✓ Exported {output_dir}/partial_verify_summary.csv")
    
    # 3. ZKP comparison
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])]
    if len(zkp_df) > 0:
        zkp_summary = zkp_df.groupby(['function', 'zkp_type']).agg({
            'wall_time_ms': ['mean', 'std', 'min', 'max'],
            'peak_rss_mb': ['mean', 'std'],
            'energy_estimate_joules': 'mean',
            'run': 'count'
        }).round(4)
        zkp_summary.to_csv(f'{output_dir}/zkp_comparison_summary.csv')
        print(f"✓ Exported {output_dir}/zkp_comparison_summary.csv")

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Analyze ZK-DISPHASIA test logs')
    parser.add_argument('logfile', help='Path to JSONL log file')
    parser.add_argument('--plots', default='plots', help='Output directory for plots')
    parser.add_argument('--no-plots', action='store_true', help='Skip plot generation')
    args = parser.parse_args()
    
    df = load_logs(args.logfile)
    
    # Run analyses
    basic_statistics(df)
    network_scaled_analysis(df)
    partial_verify_analysis(df)
    zkp_comparison_analysis(df)
    
    # Create visualizations
    if not args.no_plots:
        create_visualizations(df, args.plots)
    
    # Export CSVs
    export_summary_csvs(df, args.plots)
    
    print("\n" + "="*60 + "\nANALYSIS COMPLETE\n" + "="*60)

if __name__ == '__main__':
    main()