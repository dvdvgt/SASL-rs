//! Structs and functions concerned with generating graphs with Graphviz and DOT language.

use std::fmt::{self, Display};

pub struct Graph {
    name: String,
    pub is_directed: bool,
    nodes: Vec<Node>,
    edges: Vec<Edge>
}

impl Graph {
    pub fn new(name: &str, is_directed: bool) -> Self {
        Graph {
            name: name.to_string(),
            is_directed,
            nodes: Vec::new(),
            edges: Vec::new()
        }
    }

    pub fn add_node(&mut self, node: Node) {
        self.nodes.push(node);
    }

    pub fn add_edge(&mut self, edge: Edge) {
        self.edges.push(edge);
    }

    pub fn as_dot<W: fmt::Write>(&self, writer: &mut W) -> fmt::Result {
        write!(writer, "{}", self)
    }
}

impl Display for Graph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let graph_type = if self.is_directed {
            "digraph"
        } else {
            "graph"
        };
        writeln!(f, "{} {} {{", graph_type, &self.name)?;
        for node in self.nodes.iter() {
            writeln!(f, "\t{}", node)?;
        }
        for edge in self.edges.iter() {
            writeln!(f, "\t{}", edge)?;
        }
        write!(f, "}}")
    }
}

pub struct Node {
    id: String,
    label: Option<String>,
}

impl Node {
    pub fn new(id: &str, label: Option<&str>) -> Self {
        Self {
            id: id.to_string(),
            label: label.map_or(None, |x| Some(x.to_string()))
        }
    }
}

impl Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.label {
            Some(ref l) => write!(f, "{} [ label=\"{}\" ];", self.id, l),
            None => write!(f, "{};", self.id)
        }
    }
}

/// Add new nodes to a given graph by passing a node name and an optional label.
#[macro_export]
macro_rules! add_nodes {
    ($graph:ident, $($id:literal : $label:literal),+) => {
        $(
            $graph.add_node(
                Node {id: $id.to_string(), label: Some($label.to_string())}
            );
        )+
    };
    ($graph:ident, $($id:literal),+) => {
        $($graph.add_node(Node {id: $id.to_string(), label: None});)+
    }
}

/// Add new edges to a given graph by passing a node name and an optional label.
#[macro_export]
macro_rules! add_edges {
    ($graph:ident, $($from:literal -> $to:literal),+) => {
        assert!($graph.is_directed);
        $(
            $graph.add_edge(
                Edge::new($from, $to, true)
            );
        )+
    };
    ($graph:ident, $($from:literal -- $to:literal),+) => {
        assert!(!$graph.is_directed);
        $(
            $graph.add_edge(
                Edge::new($from, $to, false)
            );
        )+
    }
}

pub struct Edge {
    from: String,
    to: String,
    is_directed: bool
}

impl Edge {
    pub fn new(from: &str, to: &str, is_directed: bool) -> Self {
        Self { from: from.to_string(), to: to.to_string(), is_directed }
    }
}

impl Display for Edge {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f, "{} {} {};", self.from, 
            if self.is_directed {
                "->".to_string()
            } else {
                "--".to_string()
            },
            self.to
        )
    }
}

#[cfg(test)]
mod test {
    use super::{Graph, Edge, Node};
    use crate::add_nodes;
    use crate::add_edges;

    #[test]
    fn test_empty_graph() {
        let empty_graph = Graph::new("empty", true);
        let mut buf = String::new();
        empty_graph.as_dot(&mut buf).unwrap();

        assert_eq!(buf, "digraph empty {\n}");
    }

    #[test]
    fn test_directed_graph() {
        let mut graph = Graph::new("g", true);
        let mut buf = String::new();
        add_nodes!(
            graph,
            "node1" : "a",
            "node2" : "b",
            "node3" : "c"
        );
        add_edges!(
            graph,
            "node1" -> "node1",
            "node1" -> "node2",
            "node3" -> "node1"
        );
        graph.as_dot(&mut buf).unwrap();
        assert_eq!(
            buf,
            "digraph g {\n\tnode1 [ label=\"a\" ];\n\tnode2 [ label=\"b\" ];\n\tnode3 [ label=\"c\" ];\
            \n\tnode1 -> node1;\n\tnode1 -> node2;\n\tnode3 -> node1;\n}"
        );
    }

    #[test]
    fn test_undirected_graph() {
        let mut graph = Graph::new("g", false);
        let mut buf = String::new();
        add_nodes!(
            graph,
            "node1" : "a",
            "node2" : "b",
            "node3" : "c"
        );
        add_edges!(
            graph,
            "node1" -- "node1",
            "node1" -- "node2",
            "node3" -- "node1"
        );
        graph.as_dot(&mut buf).unwrap();
        assert_eq!(
            buf,
            "graph g {\n\tnode1 [ label=\"a\" ];\n\tnode2 [ label=\"b\" ];\n\tnode3 [ label=\"c\" ];\
            \n\tnode1 -- node1;\n\tnode1 -- node2;\n\tnode3 -- node1;\n}"
        );
    }
}