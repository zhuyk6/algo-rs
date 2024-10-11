use criterion::{criterion_group, criterion_main, Criterion};

use algo_rs::segment_tree::{SegmentTree, SegmentTreeBuilder};
use rand::{self, Rng};

fn generate_input(left: isize, right: isize, num_ops: i32) -> Vec<Vec<Vec<isize>>> {
    let mut ops = vec![vec![]; 4];

    println!("Generate Ops begin!");

    let mut rng = rand::thread_rng();
    for ty in [0, 1, 2, 3] {
        for _ in 0..num_ops {
            match ty {
                0 => {
                    // modify point
                    let pos = rng.gen_range(left..=right);
                    let delta = rng.gen_range(-100..100);

                    ops[ty].push(vec![pos, delta]);
                }
                1 => {
                    // add segment
                    let mid = (left + right) >> 1;
                    let v = rng.gen_range(left..=right);
                    let (l_bound, r_bound) = match v.cmp(&mid) {
                        std::cmp::Ordering::Less => (v, v + mid),
                        _ => (v - mid, v),
                    };
                    let delta = rng.gen_range(-100..100);

                    ops[ty].push(vec![l_bound, r_bound, delta]);
                }
                2 => {
                    // set segment
                    let mid = (left + right) >> 1;
                    let v = rng.gen_range(left..=right);
                    let (l_bound, r_bound) = match v.cmp(&mid) {
                        std::cmp::Ordering::Less => (v, v + mid),
                        _ => (v - mid, v),
                    };
                    let set_val = rng.gen_range(-100..100);

                    ops[ty].push(vec![l_bound, r_bound, set_val]);
                }
                3 => {
                    // query
                    let mid = (left + right) >> 1;
                    let v = rng.gen_range(left..=right);
                    let (l_bound, r_bound) = match v.cmp(&mid) {
                        std::cmp::Ordering::Less => (v, v + mid),
                        _ => (v - mid, v),
                    };
                    ops[ty].push(vec![l_bound, r_bound]);
                }
                _ => panic!("Err!"),
            }
        }
    }

    println!("Generate Ops over!");
    ops
}

fn force(arr: &mut [i32], ty: usize, ops: &[Vec<isize>]) {
    for op in ops {
        match ty {
            0 => {
                // modify point
                let pos = op[0];
                let delta = op[1] as i32;

                // force
                arr[pos as usize] += delta;
            }
            1 => {
                // add segment
                let l_bound = op[0];
                let r_bound = op[1];
                let delta = op[2] as i32;

                // force
                for v in &mut arr[l_bound as usize..=r_bound as usize] {
                    *v += delta;
                }
            }
            2 => {
                // set segment
                let l_bound = op[0];
                let r_bound = op[1];
                let set_val = op[2] as i32;

                // force
                for v in &mut arr[l_bound as usize..=r_bound as usize] {
                    *v = set_val;
                }
            }
            3 => {
                // query
                let l_bound = op[0];
                let r_bound = op[1];

                // force
                let _sum_force: i32 = arr[l_bound as usize..=r_bound as usize].iter().sum();
            }
            _ => panic!("Err!"),
        }
    }
}

fn segment_tree(tree: &mut SegmentTree, ty: usize, ops: &[Vec<isize>]) {
    for op in ops {
        match ty {
            0 => {
                // modify point
                let pos = op[0];
                let delta = op[1] as i32;

                // force
                tree.modify_point(pos, |v| v + delta);
            }
            1 => {
                // add segment
                let l_bound = op[0];
                let r_bound = op[1];
                let delta = op[2] as i32;

                tree.add_segment(l_bound, r_bound, delta);
            }
            2 => {
                // set segment
                let l_bound = op[0];
                let r_bound = op[1];
                let set_val = op[2] as i32;

                tree.set_segment(l_bound, r_bound, set_val);
            }
            3 => {
                // query
                let l_bound = op[0];
                let r_bound = op[1];

                let _ = tree.query_sum(l_bound, r_bound);
            }
            _ => panic!("Err!"),
        }
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    let left = 0;
    let right = 20000;
    let num_ops = 1000;

    let ops = generate_input(left, right, num_ops);

    let mut arr = vec![0; right as usize + 1];
    let mut tree = SegmentTreeBuilder::new()
        .interval(left, right)
        .fill(0)
        .build()
        .unwrap();

    let mut bench_group = |name: String, ty: usize| {
        let mut group = c.benchmark_group(name);
        group.bench_function("Force", |b| b.iter(|| force(&mut arr, ty, &ops[ty])));
        group.bench_function("Tree", |b| b.iter(|| segment_tree(&mut tree, ty, &ops[ty])));
        group.finish();
    };

    bench_group(format!("Modify point {num_ops} times"), 0);
    bench_group(format!("Add segment {num_ops} times"), 1);
    bench_group(format!("Set segment {num_ops} times"), 2);
    bench_group(format!("Query segment {num_ops} times"), 3);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
