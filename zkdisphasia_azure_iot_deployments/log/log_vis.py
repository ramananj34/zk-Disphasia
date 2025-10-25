#This was made with AI Assistance

import json
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
from pathlib import Path
from scipy import stats

sns.set_theme(style="whitegrid") #Set style
plt.rcParams['figure.figsize'] = (12, 6)

def load_logs(filepath): #Load JSONL file into pandas DataFrame
    print(f"Loading logs from {filepath}...")
    data = []
    with open(filepath, 'r') as f:
        for line in f:
            try: data.append(json.loads(line))
            except json.JSONDecodeError: continue
    df = pd.DataFrame(data)
    if 'test_config' in df.columns: #Flatten nested test_config
        config_df = pd.json_normalize(df['test_config'])
        df = pd.concat([df.drop('test_config', axis=1), config_df], axis=1)
    print(f"✓ Loaded {len(df)} test results")
    return df

def basic_statistics(df): #Print basic statistics
    print("\n" + "="*60 + "\nBASIC STATISTICS\n" + "="*60)
    total_tests = len(df); successes = (df['status'] == 'SUCCESS').sum(); failures = (df['status'] == 'FAILED').sum() #Overall summary
    print(f"\nTotal tests: {total_tests}\nSuccesses: {successes} ({successes/total_tests*100:.1f}%)\nFailures: {failures} ({failures/total_tests*100:.1f}%)")
    if failures > 0: print("\nFailure reasons:\n", df[df['status'] == 'FAILED']['failure_reason'].value_counts())
    success_df = df[df['status'] == 'SUCCESS'].copy() #Filter successful tests for metrics
    print("\n" + "-"*60 + "\nTIMING METRICS (milliseconds)\n" + "-"*60) #Timing statistics
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    timing_stats = success_df['wall_time_ms'].describe()
    print(f"Wall time: min={timing_stats['min']:.2f}ms, mean={timing_stats['mean']:.2f}ms, median={timing_stats['50%']:.2f}ms, max={timing_stats['max']:.2f}ms")
    print("\n" + "-"*60 + "\nMEMORY METRICS (MB)\n" + "-"*60) #Memory statistics
    success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024; success_df['delta_rss_mb'] = success_df['delta_rss_kb'] / 1024
    mem_stats = success_df['peak_rss_mb'].describe()
    print(f"Peak RSS: min={mem_stats['min']:.2f}MB, mean={mem_stats['mean']:.2f}MB, median={mem_stats['50%']:.2f}MB, max={mem_stats['max']:.2f}MB")
    if 'energy_estimate_joules' in success_df.columns: #Energy statistics
        energy_data = success_df['energy_estimate_joules'].dropna()
        if len(energy_data) > 0:
            print("\n" + "-"*60 + "\nENERGY METRICS (Joules)\n" + "-"*60)
            energy_stats = energy_data.describe()
            print(f"Energy: min={energy_stats['min']:.4f}J, mean={energy_stats['mean']:.4f}J, median={energy_stats['50%']:.4f}J, max={energy_stats['max']:.4f}J")
        else: print("\n⚠ No energy data available")

def shared_function_analysis(df): #Analyze shared functions (DKG, Partial, Aggregate) - these are ZKP-independent
    print("\n" + "="*60 + "\nSHARED FUNCTION ANALYSIS (ZKP-Independent)\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    shared_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'PartialVerify', 'AggCompute']
    shared_df = success_df[success_df['function'].isin(shared_funcs)].copy()
    shared_df['wall_time_ms'] = shared_df['wall_time_us'] / 1000; shared_df['peak_rss_mb'] = shared_df['peak_rss_kb'] / 1024
    print("\nPerformance by function and network size (n):")
    pivot = shared_df.groupby(['function', 'n'])['wall_time_ms'].mean().unstack()
    print(pivot.round(2))
    print("\nThreshold ratio (t/n) impact:") #Show how threshold ratio affects performance
    shared_df['t_ratio'] = shared_df['t'] / shared_df['n']
    threshold_impact = shared_df.groupby(['function', 't_ratio'])['wall_time_ms'].mean().unstack()
    print(threshold_impact.round(2))
    print("\nMemory usage by function and network size:")
    mem_pivot = shared_df.groupby(['function', 'n'])['peak_rss_mb'].mean().unstack()
    print(mem_pivot.round(2))
    return shared_df

def zkp_function_analysis(df): #Analyze ZKP-specific functions (ProofGen, ProofVerify) - these vary by ZKP type
    print("\n" + "="*60 + "\nZKP-SPECIFIC FUNCTION ANALYSIS\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    zkp_funcs = ['ProofGen', 'ProofVerify']
    zkp_df = success_df[success_df['function'].isin(zkp_funcs)].copy()
    if len(zkp_df) == 0: print("No ZKP-specific tests found"); return None
    zkp_df['wall_time_ms'] = zkp_df['wall_time_us'] / 1000; zkp_df['peak_rss_mb'] = zkp_df['peak_rss_kb'] / 1024
    print("\n--- ProofGen Performance ---")
    proofgen = zkp_df[zkp_df['function'] == 'ProofGen']
    print("\nBy ZKP type (averaged across all n, t):")
    print(proofgen.groupby('zkp_type')['wall_time_ms'].agg(['mean', 'std', 'min', 'max']).round(2))
    print("\nBy ZKP type and network size:")
    pg_pivot = proofgen.groupby(['zkp_type', 'n'])['wall_time_ms'].mean().unstack()
    print(pg_pivot.round(2))
    print("\n--- ProofVerify Performance ---")
    proofverify = zkp_df[zkp_df['function'] == 'ProofVerify']
    print("\nBy ZKP type (averaged across all n, t):")
    print(proofverify.groupby('zkp_type')['wall_time_ms'].agg(['mean', 'std', 'min', 'max']).round(2))
    print("\nBy ZKP type and network size:")
    pv_pivot = proofverify.groupby(['zkp_type', 'n'])['wall_time_ms'].mean().unstack()
    print(pv_pivot.round(2))
    print("\n--- Memory Comparison ---")
    print("\nProofGen memory by ZKP type:")
    print(proofgen.groupby('zkp_type')['peak_rss_mb'].agg(['mean', 'std']).round(2))
    print("\nProofVerify memory by ZKP type:")
    print(proofverify.groupby('zkp_type')['peak_rss_mb'].agg(['mean', 'std']).round(2))
    if 'energy_estimate_joules' in zkp_df.columns and zkp_df['energy_estimate_joules'].notna().any(): #Energy comparison
        print("\n--- Energy Comparison ---")
        print("\nProofGen energy by ZKP type:")
        print(proofgen.groupby('zkp_type')['energy_estimate_joules'].agg(['mean', 'std']).round(4))
        print("\nProofVerify energy by ZKP type:")
        print(proofverify.groupby('zkp_type')['energy_estimate_joules'].agg(['mean', 'std']).round(4))
    print("\n--- ZKP Type Rankings (by mean time) ---")
    print("\nProofGen (fastest to slowest):")
    print(proofgen.groupby('zkp_type')['wall_time_ms'].mean().sort_values().round(2))
    print("\nProofVerify (fastest to slowest):")
    print(proofverify.groupby('zkp_type')['wall_time_ms'].mean().sort_values().round(2))
    return zkp_df

def scaling_analysis(df): #Detailed scaling analysis showing how each function scales with n
    print("\n" + "="*60 + "\nSCALING ANALYSIS\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    print("\n--- Shared Functions Scaling ---")
    shared_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'PartialVerify', 'AggCompute']
    for func in shared_funcs:
        func_data = success_df[success_df['function'] == func]
        scaling = func_data.groupby('n')['wall_time_ms'].mean()
        if len(scaling) > 1:
            growth_factor = scaling.iloc[-1] / scaling.iloc[0]
            print(f"\n{func}: {scaling.iloc[0]:.2f}ms (n={scaling.index[0]}) → {scaling.iloc[-1]:.2f}ms (n={scaling.index[-1]}) [×{growth_factor:.1f}]")
            print(f"  Full series: {dict(scaling.round(2))}")
    print("\n--- ZKP Functions Scaling (by type) ---")
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])]
    if len(zkp_df) > 0:
        for zkp_type in zkp_df['zkp_type'].unique():
            print(f"\n{zkp_type}:")
            for func in ['ProofGen', 'ProofVerify']:
                func_data = zkp_df[(zkp_df['zkp_type'] == zkp_type) & (zkp_df['function'] == func)]
                scaling = func_data.groupby('n')['wall_time_ms'].mean()
                if len(scaling) > 1:
                    growth_factor = scaling.iloc[-1] / scaling.iloc[0]
                    print(f"  {func}: {scaling.iloc[0]:.2f}ms (n={scaling.index[0]}) → {scaling.iloc[-1]:.2f}ms (n={scaling.index[-1]}) [×{growth_factor:.1f}]")

def threshold_analysis(df): #Analyze impact of threshold ratio on performance
    print("\n" + "="*60 + "\nTHRESHOLD RATIO ANALYSIS\n" + "="*60)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000
    success_df['t_ratio'] = (success_df['t'] / success_df['n']).round(2)
    print("\nImpact of t/n ratio on shared functions:")
    shared_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'PartialVerify', 'AggCompute']
    shared_df = success_df[success_df['function'].isin(shared_funcs)]
    for func in shared_funcs:
        func_data = shared_df[shared_df['function'] == func]
        ratio_impact = func_data.groupby('t_ratio')['wall_time_ms'].agg(['mean', 'std', 'count'])
        print(f"\n{func}:")
        print(ratio_impact.round(2))

def create_visualizations(df, output_dir='plots'): #Create visualization plots
    print("\n" + "="*60 + "\nCREATING VISUALIZATIONS\n" + "="*60)
    Path(output_dir).mkdir(exist_ok=True)
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000; success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    plt.figure(figsize=(14, 8)) #1. Shared functions - time by function and network size
    shared_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'PartialVerify', 'AggCompute']
    shared_df = success_df[success_df['function'].isin(shared_funcs)]
    for func in shared_funcs:
        func_data = shared_df[shared_df['function'] == func]
        scaling = func_data.groupby('n')['wall_time_ms'].mean()
        plt.plot(scaling.index, scaling.values, marker='o', label=func, linewidth=2, markersize=8)
    plt.xlabel('Network Size (n)', fontsize=12); plt.ylabel('Average Wall Time (ms)', fontsize=12); plt.title('Shared Functions: Scaling with Network Size', fontsize=14); plt.legend(); plt.xscale('log'); plt.yscale('log'); plt.grid(True, alpha=0.3); plt.tight_layout()
    plt.savefig(f'{output_dir}/shared_scaling.png', dpi=150); print(f"✓ Saved {output_dir}/shared_scaling.png"); plt.close()
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])] #2. ZKP ProofGen comparison
    if len(zkp_df) > 0:
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        proofgen = zkp_df[zkp_df['function'] == 'ProofGen']
        for zkp_type in proofgen['zkp_type'].unique():
            type_data = proofgen[proofgen['zkp_type'] == zkp_type]
            scaling = type_data.groupby('n')['wall_time_ms'].mean()
            ax1.plot(scaling.index, scaling.values, marker='o', label=zkp_type, linewidth=2, markersize=8)
        ax1.set_xlabel('Network Size (n)', fontsize=12); ax1.set_ylabel('Average Wall Time (ms)', fontsize=12); ax1.set_title('ProofGen: ZKP Type Comparison', fontsize=14); ax1.legend(); ax1.set_xscale('log'); ax1.set_yscale('log'); ax1.grid(True, alpha=0.3)
        proofverify = zkp_df[zkp_df['function'] == 'ProofVerify'] #3. ZKP ProofVerify comparison
        for zkp_type in proofverify['zkp_type'].unique():
            type_data = proofverify[proofverify['zkp_type'] == zkp_type]
            scaling = type_data.groupby('n')['wall_time_ms'].mean()
            ax2.plot(scaling.index, scaling.values, marker='o', label=zkp_type, linewidth=2, markersize=8)
        ax2.set_xlabel('Network Size (n)', fontsize=12); ax2.set_ylabel('Average Wall Time (ms)', fontsize=12); ax2.set_title('ProofVerify: ZKP Type Comparison', fontsize=14); ax2.legend(); ax2.set_xscale('log'); ax2.set_yscale('log'); ax2.grid(True, alpha=0.3)
        plt.tight_layout(); plt.savefig(f'{output_dir}/zkp_comparison.png', dpi=150); print(f"✓ Saved {output_dir}/zkp_comparison.png"); plt.close()
    fig, axes = plt.subplots(2, 3, figsize=(18, 12)) #4. Shared functions - individual boxplots
    for idx, func in enumerate(shared_funcs):
        ax = axes[idx // 3, idx % 3]
        func_data = shared_df[shared_df['function'] == func]
        func_data.boxplot(column='wall_time_ms', by='n', ax=ax)
        ax.set_xlabel('Network Size (n)'); ax.set_ylabel('Wall Time (ms)'); ax.set_title(func); ax.get_figure().suptitle('')
    plt.tight_layout(); plt.savefig(f'{output_dir}/shared_boxplots.png', dpi=150); print(f"✓ Saved {output_dir}/shared_boxplots.png"); plt.close()
    if len(zkp_df) > 0: #5. ZKP type bar chart comparison
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        pg_means = proofgen.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
        ax1.bar(range(len(pg_means)), pg_means.values); ax1.set_xticks(range(len(pg_means))); ax1.set_xticklabels(pg_means.index); ax1.set_ylabel('Average Wall Time (ms)'); ax1.set_title('ProofGen: ZKP Type Performance'); ax1.grid(axis='y', alpha=0.3)
        pv_means = proofverify.groupby('zkp_type')['wall_time_ms'].mean().sort_values()
        ax2.bar(range(len(pv_means)), pv_means.values); ax2.set_xticks(range(len(pv_means))); ax2.set_xticklabels(pv_means.index); ax2.set_ylabel('Average Wall Time (ms)'); ax2.set_title('ProofVerify: ZKP Type Performance'); ax2.grid(axis='y', alpha=0.3)
        plt.tight_layout(); plt.savefig(f'{output_dir}/zkp_bars.png', dpi=150); print(f"✓ Saved {output_dir}/zkp_bars.png"); plt.close()
    plt.figure(figsize=(14, 8)) #6. Memory usage comparison
    for func in shared_funcs:
        func_data = shared_df[shared_df['function'] == func]
        mem_scaling = func_data.groupby('n')['peak_rss_mb'].mean()
        plt.plot(mem_scaling.index, mem_scaling.values, marker='o', label=func, linewidth=2, markersize=8)
    plt.xlabel('Network Size (n)', fontsize=12); plt.ylabel('Peak Memory (MB)', fontsize=12); plt.title('Shared Functions: Memory Usage', fontsize=14); plt.legend(); plt.xscale('log'); plt.grid(True, alpha=0.3); plt.tight_layout()
    plt.savefig(f'{output_dir}/memory_scaling.png', dpi=150); print(f"✓ Saved {output_dir}/memory_scaling.png"); plt.close()
    if 'energy_estimate_joules' in zkp_df.columns and zkp_df['energy_estimate_joules'].notna().any(): #7. Energy comparison for ZKP types
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        pg_energy = proofgen.groupby('zkp_type')['energy_estimate_joules'].mean().sort_values()
        ax1.bar(range(len(pg_energy)), pg_energy.values); ax1.set_xticks(range(len(pg_energy))); ax1.set_xticklabels(pg_energy.index); ax1.set_ylabel('Average Energy (Joules)'); ax1.set_title('ProofGen: Energy Consumption by ZKP Type'); ax1.grid(axis='y', alpha=0.3)
        pv_energy = proofverify.groupby('zkp_type')['energy_estimate_joules'].mean().sort_values()
        ax2.bar(range(len(pv_energy)), pv_energy.values); ax2.set_xticks(range(len(pv_energy))); ax2.set_xticklabels(pv_energy.index); ax2.set_ylabel('Average Energy (Joules)'); ax2.set_title('ProofVerify: Energy Consumption by ZKP Type'); ax2.grid(axis='y', alpha=0.3)
        plt.tight_layout(); plt.savefig(f'{output_dir}/energy_comparison.png', dpi=150); print(f"✓ Saved {output_dir}/energy_comparison.png"); plt.close()
    success_df['t_ratio'] = (success_df['t'] / success_df['n']).round(2) #8. Threshold ratio impact
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    for idx, func in enumerate(shared_funcs):
        ax = axes[idx // 3, idx % 3]
        func_data = shared_df[shared_df['function'] == func]
        func_data['t_ratio'] = (func_data['t'] / func_data['n']).round(2)
        ratio_means = func_data.groupby('t_ratio')['wall_time_ms'].mean()
        ax.bar(range(len(ratio_means)), ratio_means.values); ax.set_xticks(range(len(ratio_means))); ax.set_xticklabels(ratio_means.index); ax.set_ylabel('Wall Time (ms)'); ax.set_title(f'{func}: Threshold Ratio Impact'); ax.grid(axis='y', alpha=0.3)
    plt.tight_layout(); plt.savefig(f'{output_dir}/threshold_impact.png', dpi=150); print(f"✓ Saved {output_dir}/threshold_impact.png"); plt.close()

def export_detailed_csv(df, output_dir='.'): #Export detailed statistics to multiple CSV files
    success_df = df[df['status'] == 'SUCCESS'].copy()
    success_df['wall_time_ms'] = success_df['wall_time_us'] / 1000; success_df['peak_rss_mb'] = success_df['peak_rss_kb'] / 1024
    shared_funcs = ['DKG1', 'DKG2', 'DKG3', 'PartialGen', 'PartialVerify', 'AggCompute'] #1. Shared functions summary
    shared_df = success_df[success_df['function'].isin(shared_funcs)]
    shared_summary = shared_df.groupby(['function', 'n', 't']).agg({'wall_time_ms': ['mean', 'std', 'min', 'max'], 'peak_rss_mb': ['mean', 'std'], 'energy_estimate_joules': 'mean', 'run': 'count'}).round(4)
    shared_summary.to_csv(f'{output_dir}/shared_functions.csv'); print(f"✓ Exported {output_dir}/shared_functions.csv")
    zkp_df = success_df[success_df['function'].isin(['ProofGen', 'ProofVerify'])] #2. ZKP functions summary
    if len(zkp_df) > 0:
        zkp_summary = zkp_df.groupby(['zkp_type', 'function', 'n', 't']).agg({'wall_time_ms': ['mean', 'std', 'min', 'max'], 'peak_rss_mb': ['mean', 'std'], 'energy_estimate_joules': 'mean', 'run': 'count'}).round(4)
        zkp_summary.to_csv(f'{output_dir}/zkp_functions.csv'); print(f"✓ Exported {output_dir}/zkp_functions.csv")
    scaling_data = [] #3. Scaling factors
    for func in shared_funcs:
        func_data = shared_df[shared_df['function'] == func]
        scaling = func_data.groupby('n')['wall_time_ms'].mean()
        if len(scaling) > 1:
            for i in range(1, len(scaling)):
                scaling_data.append({'function': func, 'from_n': scaling.index[i-1], 'to_n': scaling.index[i], 'time_from': scaling.iloc[i-1], 'time_to': scaling.iloc[i], 'growth_factor': scaling.iloc[i] / scaling.iloc[i-1]})
    if scaling_data:
        scaling_df = pd.DataFrame(scaling_data)
        scaling_df.to_csv(f'{output_dir}/scaling_factors.csv', index=False); print(f"✓ Exported {output_dir}/scaling_factors.csv")

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Analyze ZK-DISPHASIA test logs')
    parser.add_argument('logfile', help='Path to JSONL log file')
    parser.add_argument('--plots', default='plots', help='Output directory for plots')
    parser.add_argument('--no-plots', action='store_true', help='Skip plot generation')
    args = parser.parse_args()
    df = load_logs(args.logfile) #Load data
    basic_statistics(df) #Run analyses
    shared_function_analysis(df)
    zkp_function_analysis(df)
    scaling_analysis(df)
    threshold_analysis(df)
    if not args.no_plots: create_visualizations(df, args.plots) #Create visualizations
    export_detailed_csv(df, args.plots) #Export detailed CSVs
    print("\n" + "="*60 + "\nANALYSIS COMPLETE\n" + "="*60)

if __name__ == '__main__': main()