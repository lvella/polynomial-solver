#!/usr/bin/env python3

# Benchmarks to run from ZoKrates files:
zokrates_benchmarks = ['u8_different_from_zero.zok_bin']

# Benchmarks to run based from Maple-like files:
maple_like_benchmarks = [('benchmark.txt', 20)]

import os
import subprocess
import datetime

def main():
    out_dir = f'run_{datetime.datetime.utcnow()}'
    os.mkdir(out_dir)

    # Run ZoKrates benchmarks
    for f in zokrates_benchmarks:
        print(f'Running ZoKrates benchmark "{f}"...')
        stdout = open(f'{out_dir}/{f}.out', 'wb')
        stderr = open(f'{out_dir}/{f}.err', 'wb')

        subprocess.run(['../target/release/polysolver', '-z', f, '-v', f'{out_dir}/{f}.verification.cocoa5'], stdout=stdout, stderr=stderr)

    # Run Maple-like benchmarks
    for (f, count) in maple_like_benchmarks:
        for idx in range(count):
            print(f'Running Maple-like benchmark {idx} from "{f}"...')
            stdout = open(f'{out_dir}/{f}.{idx}.out', 'wb')
            stderr = open(f'{out_dir}/{f}.{idx}.err', 'wb')

            subprocess.run(['../target/release/polysolver', '-m', f, '-i', str(idx), '-v', f'{out_dir}/{f}.{idx}.verification.cocoa5'], stdout=stdout, stderr=stderr)

if __name__ == '__main__':
    main()
