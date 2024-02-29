/// Find the root of the tree, used in JoinSet.
fn find_parent(parent: &mut Vec<usize>, x: usize) -> usize {
    if parent[x] != x {
        parent[x] = find_parent(parent, parent[x]);
    }
    parent[x]
}

/// Tarjan algorithm for the LCA problem.
struct Tarjan<'a> {
    graph: &'a Vec<Vec<usize>>,
    query_about: Vec<Vec<(usize, usize)>>,
    vis: Vec<bool>,
    parent: Vec<usize>,
    answer: Vec<usize>,
}

impl<'a> Tarjan<'a> {
    #[allow(dead_code)]
    /// Return a LCA solver.
    ///
    /// # Arguments
    ///
    /// * `graph` - The linked list representation for the tree.
    /// * `queries` - LCA queries, represented as array of pair.
    fn new(graph: &'a Vec<Vec<usize>>, queries: &[(usize, usize)]) -> Self {
        let n = graph.len();
        let m = queries.len();
        let mut query_about: Vec<Vec<(usize, usize)>> = vec![vec![]; n];
        for (id, &(x, y)) in queries.iter().enumerate() {
            query_about[x].push((y, id));
            query_about[y].push((x, id));
        }
        Tarjan {
            graph,
            query_about,
            vis: vec![false; n],
            parent: (0..n).collect(),
            answer: vec![usize::MAX; m],
        }
    }

    #[allow(dead_code)]
    fn dfs(&mut self, x: usize) {
        self.vis[x] = true;
        for &y in &self.graph[x] {
            if !self.vis[y] {
                self.dfs(y);
                self.parent[y] = x;
            }
        }
        for &(y, id) in &self.query_about[x] {
            if self.vis[y] {
                let z = find_parent(&mut self.parent, y);
                self.answer[id] = z;
            }
        }
    }
}

#[test]
fn test1() {
    let n = 8;
    let edges = [(0, 1), (0, 2), (1, 3), (1, 4), (3, 5), (4, 6), (6, 7)];
    let mut graph: Vec<Vec<usize>> = vec![vec![]; n];
    for (x, y) in edges.into_iter() {
        graph[x].push(y);
        graph[y].push(x);
    }
    let queries = vec![(5, 1), (3, 7), (2, 6), (1, 7)];
    let answers = vec![1, 1, 0, 1];

    let mut sol = Tarjan::new(&graph, &queries);
    sol.dfs(0);
    for (id, &(x, y)) in queries.iter().enumerate() {
        println!("x = {x}, y = {y}, lca = {z}", z = sol.answer[id]);
    }

    assert_eq!(sol.answer, answers);
}
