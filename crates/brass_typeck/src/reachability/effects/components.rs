//! Deterministic Tarjan ordering: callees precede callers, cycles stay together.

/// Partition a catalog-indexed graph into bottom-up strongly connected components.
pub(super) fn bottom_up(graph: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct Search<'a> {
        graph: &'a [Vec<usize>],
        next: usize,
        numbers: Vec<Option<usize>>,
        low: Vec<usize>,
        stack: Vec<usize>,
        active: Vec<bool>,
        result: Vec<Vec<usize>>,
    }
    impl Search<'_> {
        fn visit(&mut self, node: usize) {
            let number = self.next;
            self.next += 1;
            self.numbers[node] = Some(number);
            self.low[node] = number;
            self.stack.push(node);
            self.active[node] = true;
            for &callee in &self.graph[node] {
                if self.numbers[callee].is_none() {
                    self.visit(callee);
                    self.low[node] = self.low[node].min(self.low[callee]);
                } else if self.active[callee] {
                    self.low[node] = self.low[node].min(self.numbers[callee].unwrap());
                }
            }
            if self.low[node] == number {
                let mut component = Vec::new();
                loop {
                    let member = self.stack.pop().unwrap();
                    self.active[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                component.sort_unstable();
                self.result.push(component);
            }
        }
    }
    let mut search = Search {
        graph,
        next: 0,
        numbers: vec![None; graph.len()],
        low: vec![0; graph.len()],
        stack: Vec::new(),
        active: vec![false; graph.len()],
        result: Vec::new(),
    };
    for node in 0..graph.len() {
        if search.numbers[node].is_none() {
            search.visit(node);
        }
    }
    search.result
}
