use core::fmt::Debug;
use std::cmp::Ordering;
use std::{collections::HashMap, hash::Hash};

use priority_queue::PriorityQueue;

use crate::{
    visit::{EdgeRef, IntoEdges, IntoEdgesDirected, IntoNodeIdentifiers, Visitable},
    EdgeDirection,
};

use super::FloatMeasure;

struct DStarLight<G, H, K>
where
    G: IntoEdges<EdgeWeight = K> + Visitable,
    G::NodeId: Eq + Hash,
    H: FnMut(G::NodeId, G::NodeId) -> K,
    K: FloatMeasure,
{
    graph: G,
    s_id: G::NodeId,
    t_id: G::NodeId,
    k_m: K,
    h: H,
    queue: PriorityQueue<G::NodeId, Key<K>>,
    nodes: HashMap<G::NodeId, DStarLightNode<K, G::NodeId>>,
}

#[derive(Clone, Debug)]
pub struct DStarLightNode<K, I> {
    g: K,
    rhs: K,
    id: I,
}

#[derive(Debug, PartialEq, Clone)]
struct Key<K>([K; 2]);

impl<K: FloatMeasure> Eq for Key<K> {
    fn assert_receiver_is_total_eq(&self) {}
}

impl<K: FloatMeasure> PartialOrd for Key<K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<K: FloatMeasure> Ord for Key<K> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Less)
    }
}

impl<G, H, K> DStarLight<G, H, K>
where
    G: IntoEdgesDirected<EdgeWeight = K> + Visitable + IntoNodeIdentifiers,
    G::NodeId: Eq + Hash + Debug,
    G::EdgeWeight: FloatMeasure,
    H: FnMut(G::NodeId, G::NodeId) -> K,
    K: FloatMeasure,
{
    pub fn new(graph: G, s_start: G::NodeId, s_goal: G::NodeId, mut h: H) -> Self {
        let mut nodes = HashMap::new();
        for node_id in graph.node_identifiers() {
            if node_id == s_goal {
                nodes.insert(
                    node_id,
                    DStarLightNode {
                        g: K::infinite(),
                        rhs: K::zero(),
                        id: node_id,
                    },
                );
            } else {
                nodes.insert(node_id, DStarLightNode::new(node_id));
            }
        }
        let mut u = PriorityQueue::new();
        u.push(s_goal, Key([h(s_start, s_goal), K::zero()]));
        Self {
            graph,
            s_id: s_start,
            t_id: s_goal,
            k_m: K::zero(),
            h,
            queue: u,
            nodes,
        }
    }

    fn calculate_key(&mut self, s: &DStarLightNode<K, G::NodeId>) -> Key<K> {
        let h = (self.h)(self.s_id, s.id);
        let min_g_rhs = min(s.g, s.rhs);
        Key([min_g_rhs + h + self.k_m, min_g_rhs])
    }

    fn update_vertex(&mut self, u: &DStarLightNode<K, G::NodeId>) {
        let in_queue = self.queue.get(&u.id).is_some();
        if in_queue {
            if u.rhs == u.g {
                self.queue.remove(&u.id);
            } else {
                let key = self.calculate_key(u);
                self.queue.change_priority(&u.id, key);
            }
        } else {
            let key = self.calculate_key(u);
            self.queue.push(u.id, key);
        }
    }

    fn compute_shortest_path(&mut self) {
        while !self.queue.is_empty() {
            let (u_id, u_key) = self.queue.peek().unwrap();
            let u_id = *u_id;
            let key = u_key.clone();

            let mut u = self.nodes.get(&u_id).unwrap().clone();

            let s = self.nodes.get(&self.s_id).unwrap().clone();
            if !(key < self.calculate_key(&s)) && s.rhs <= s.g {
                break;
            }

            let k_new = self.calculate_key(&u);

            if key < k_new {
                self.queue.change_priority(&u_id, k_new);
            } else if u.g > u.rhs {
                u.g = u.rhs;
                self.queue.remove(&u_id);
                for edge in self.graph.edges_directed(u_id, EdgeDirection::Incoming) {
                    let s_id = edge.target();
                    let mut s = self.nodes.get_mut(&s_id).unwrap();
                    if self.t_id != s_id {
                        s.rhs = min(s.rhs, *edge.weight() + u.g);
                    }
                    let s = s.clone();
                    self.update_vertex(&s);
                }
                self.nodes.insert(u_id, u);
            } else {
                let g_old = u.g;
                u.g = K::infinite();

                if u.rhs == g_old && u.id != self.t_id {
                    u.rhs = K::infinite();
                    for edge in self.graph.edges_directed(u_id, EdgeDirection::Outgoing) {
                        let to = self.nodes.get(&edge.target()).unwrap().clone();
                        u.rhs = min(u.rhs, *edge.weight() + to.g);
                    }
                    self.update_vertex(&u);
                    self.nodes.insert(u_id, u);
                }

                for edge in self.graph.edges_directed(u_id, EdgeDirection::Incoming) {
                    let s_id = edge.target();
                    let mut s = self.nodes.get_mut(&s_id).unwrap().clone();
                    if s.rhs == *edge.weight() + g_old && s.id != self.t_id {
                        s.rhs = K::infinite();
                        for edge in self.graph.edges_directed(s_id, EdgeDirection::Outgoing) {
                            let to = self.nodes.get(&edge.target()).unwrap().clone();
                            s.rhs = min(s.rhs, *edge.weight() + to.g);
                        }
                    }
                    self.update_vertex(&s);
                }
            }
        }
        dbg!(&self.nodes);
    }

    pub fn path(&self) -> Option<(K, Vec<G::NodeId>)> {
        let u_id = self.s_id;
        let mut p = Vec::new();
        let mut weight = K::zero();
        while u_id != self.t_id {
            let u = self.nodes.get(&u_id).unwrap();
            if u.rhs == K::infinite() {
                return None;
            }

            let mut rhs_min = K::infinite();
            let mut minimum = K::infinite();
            let mut cost = K::zero();
            let mut next_id = None;

            for edge in self.graph.edges_directed(u_id, EdgeDirection::Outgoing) {
                let v_id = edge.target();
                let v = self.nodes.get(&v_id).unwrap();
                let rhs = *edge.weight() + v.g;
                if rhs < minimum || (rhs == minimum && v.rhs < rhs_min) {
                    next_id = Some(v_id);
                    minimum = rhs;
                    rhs_min = v.rhs;
                    cost = weight;
                }
            }

            let u_id = next_id?;
            weight = weight + cost;
            p.push(u_id);
        }
        Some((weight, p))
    }
}

impl<K: FloatMeasure, I> DStarLightNode<K, I> {
    fn new(id: I) -> Self {
        Self {
            g: K::infinite(),
            rhs: K::infinite(),
            id,
        }
    }
}

pub fn min<T: PartialOrd>(a: T, b: T) -> T {
    if a < b {
        a
    } else {
        b
    }
}

#[cfg(test)]
mod tests {
    use crate::Graph;

    use super::*;

    #[test]
    fn test_basic() {
        let mut g = Graph::new();
        let a = g.add_node((0., 0.));
        let b = g.add_node((2., 0.));
        // let c = g.add_node((1., 1.));
        // let d = g.add_node((0., 2.));
        // let e = g.add_node((3., 3.));
        // let f = g.add_node((4., 2.));
        g.extend_with_edges(&[
            (a, b, 2.),
            // (a, d, 4.),
            // (b, c, 1.),
            // (b, f, 7.),
            // (c, e, 5.),
            // (e, f, 1.),
            // (d, e, 1.),
        ]);

        let mut d_star_light = DStarLight::new(&g, a, b, |i, j| 0.0);
        d_star_light.compute_shortest_path();

        let (weight, path) = d_star_light.path().expect("should find path");
        dbg!(weight);
        dbg!(path);
        panic!("here");
    }
}
