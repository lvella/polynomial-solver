#!/usr/bin/env python3

# Benchmarks to run from ZoKrates files:
import datetime
import subprocess
import os
zokrates_benchmarks = ['u8_different_from_zero.zok_bin']

# Benchmarks to run based from Maple-like files:
maple_like_benchmarks = [('benchmark.txt', 20)]


timeout = 60*5  # 5 minutes


def gb_run(particular_args, output_file):
    stdout = open(f'{output_file}.out', 'wb')
    stderr = open(f'{output_file}.err', 'wb')

    cmd = ['../target/release/grobner-basis', '-v',
           f'{output_file}.verification.cocoa5'] + particular_args
    sub = subprocess.Popen(cmd, stdout=stdout, stderr=stderr)

    try:
        sub.wait(timeout)
        print('finished!')
    except subprocess.TimeoutExpired:
        sub.kill()
        print('timed out!')


def main():
    out_dir = f'{datetime.datetime.utcnow()}-run'
    os.mkdir(out_dir)

    # Run ZoKrates benchmarks
    for f in zokrates_benchmarks:
        print(f'Running ZoKrates benchmark "{f}"...')
        gb_run(['-z', f'inputs/{f}'], f'{out_dir}/{f}')

    # Run Maple-like benchmarks
    for (f, count) in maple_like_benchmarks:
        for idx in range(count):
            print(f'Running Maple-like benchmark {idx} from "{f}"...')
            gb_run(['-m', f'inputs/{f}', '-i', str(idx)],
                   f'{out_dir}/{f}.{idx}')


if __name__ == '__main__':
    main()
