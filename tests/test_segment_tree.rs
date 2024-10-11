use algo_rs::segment_tree::SegmentTreeBuilder;
use rand::{self, Rng};

#[test]
fn test_comparing_with_force() {
    let left = 0;
    let right = 1000;
    let num_ops = 5000;

    let mut arr = vec![0; right as usize + 1];
    let mut tree = SegmentTreeBuilder::new()
        .interval(left, right)
        .fill(0)
        .build()
        .unwrap();

    let mut rng = rand::thread_rng();
    for _ in 0..num_ops {
        let ty: u32 = rng.gen_range(0..=3);
        match ty {
            0 => {
                // modify point
                let pos = rng.gen_range(left..=right);
                let delta = rng.gen_range(-100..100);

                // force
                arr[pos as usize] += delta;
                // tree
                tree.modify_point(pos, |v| v + delta);
            }
            1 => {
                // add segment
                let _l_bound = rng.gen_range(left..=right);
                let _r_bound = rng.gen_range(left..=right);
                let l_bound = _l_bound.min(_r_bound);
                let r_bound = _l_bound.max(_r_bound);
                let delta = rng.gen_range(-100..100);

                // force
                for v in &mut arr[l_bound as usize..=r_bound as usize] {
                    *v += delta;
                }
                // tree
                tree.add_segment(l_bound, r_bound, delta);
            }
            2 => {
                // set segment
                let _l_bound = rng.gen_range(left..=right);
                let _r_bound = rng.gen_range(left..=right);
                let l_bound = _l_bound.min(_r_bound);
                let r_bound = _l_bound.max(_r_bound);
                let set_val = rng.gen_range(-100..100);

                // force
                for v in &mut arr[l_bound as usize..=r_bound as usize] {
                    *v = set_val;
                }
                // tree
                tree.set_segment(l_bound, r_bound, set_val);
            }
            3 => {
                // query
                let _l_bound = rng.gen_range(left..=right);
                let _r_bound = rng.gen_range(left..=right);
                let l_bound = _l_bound.min(_r_bound);
                let r_bound = _l_bound.max(_r_bound);

                // force
                let sum_force: i32 = arr[l_bound as usize..=r_bound as usize].iter().sum();
                let max_force: i32 = *arr[l_bound as usize..=r_bound as usize]
                    .iter()
                    .max()
                    .unwrap();

                // tree
                let sum_tree = tree.query_sum(l_bound, r_bound);
                let max_tree = tree.query_max(l_bound, r_bound);

                assert_eq!(sum_force, sum_tree);
                assert_eq!(max_force, max_tree);
            }
            _ => panic!("Err!"),
        }
    }
}
