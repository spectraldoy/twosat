use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let tc = TwoCnf::from_description(args[1].clone());
    if let Some(assignment) = tc.find_sat_assignment() {
        println!("Formula is SAT with assignment {:?}", assignment);
    } else {
        println!("Formula is not SAT");
    }
}

// name, negated
#[derive(PartialEq, Eq, Clone, Hash)]
struct Literal(String, bool);

struct TwoCnf {
    variables: HashSet<String>,
    clauses: HashSet<(Literal, Literal)>,
}

impl TwoCnf {
    /// A 2CNF is a 2-level Boolean circuit in Conjunctive Normal Form
    ///.where every clause has at most 2 literals. Thus, parentheses can
    /// e nested at most one level deep, within parentheses we only see
    /// the | operator, and between parentheses we see only the & operator
    fn is_valid_descr(description: String) -> bool {
        let valid_clause_re = Regex::new(
            r"^(\(~?[a-zA-Z][a-zA-Z0-9]*\|~?[a-zA-Z][a-zA-Z0-9]*\)|~?[a-zA-Z][a-zA-Z0-9]*)$",
        )
        .unwrap();
        // clone for correct error messaging
        let mut descr = description.clone();
        // remove whitespace
        descr.retain(|c| !c.is_whitespace());
        // split by & and assert every clause matches the regex
        descr.split('&').all(|val| valid_clause_re.is_match(val))
    }

    fn from_description(description: String) -> Self {
        // check description is valid
        assert!(
            Self::is_valid_descr(description.clone()),
            "Invalid 2CNF description: {}",
            description
        );

        // tools for extracting the variables and clauses
        let literal_re: Regex = Regex::new(r"~?[a-zA-Z][a-zA-Z0-9]*").unwrap();
        let str_to_literal = |x: &str| -> Literal {
            let negated;
            let name;
            if x.starts_with('~') {
                negated = true;
                // exclude the first char by finding the index of the first char
                let (i, _) = x.char_indices().nth(1).unwrap();
                name = &x[i..];
            } else {
                negated = false;
                name = x;
            }
            Literal(name.to_string(), negated)
        };

        // construct the clauses and collect the variables concurrently
        // note that all whitespace in the string is removed
        let mut variables = HashSet::<String>::new();
        let clauses: HashSet<(Literal, Literal)> = description
            .replace(|c: char| c.is_whitespace(), "")
            .split('&')
            .map(|clause| {
                if clause.contains('|') {
                    // in this case there are 2 literals in the clause
                    let mut captures = literal_re.captures_iter(clause);
                    let lit1 = str_to_literal(&captures.next().unwrap()[0]);
                    let lit2 = str_to_literal(&captures.next().unwrap()[0]);
                    // insert the names into the variables set
                    variables.insert(lit1.0.clone());
                    variables.insert(lit2.0.clone());
                    (lit1, lit2)
                } else {
                    // else there is only one literal in the clause
                    let lit = str_to_literal(clause);
                    // insert the name into the variabls set
                    variables.insert(lit.0.clone());
                    // duplicate the literal, x or x is equivalent to x
                    (lit.clone(), lit)
                }
            })
            .collect();

        Self { variables, clauses }
    }

    fn find_sat_assignment(&self) -> Option<HashMap<String, bool>> {
        // The strongly connected components of the implication graph of the CNF
        // allow us to determine if the instance is satisfiable
        // The instance is satisfiable iff its strongly connected components
        // do not connect any literal to its negation
        // below is the algorithm to find strongly connected components
        // Reference: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
        // We need the following information to perform SCC search through Tarjan's alg
        // (unique index for node, lowest index reachable from node, node on stack?)
        #[derive(PartialEq, Eq, Hash)]
        struct SCCNodeInfo(u32, u32, bool);

        fn find_strongly_connected_components(
            v: Literal,
            graph: &HashMap<Literal, HashSet<Literal>>,
            node_info: &mut HashMap<Literal, SCCNodeInfo>,
            stack: &mut Vec<Literal>,
            strongly_connected_components: &mut Vec<HashSet<Literal>>,
            next_index: &mut u32,
        ) {
            // push v onto the stack
            stack.push(v.clone());
            // give it the newest available index,
            // assume it is the lowest index reachable from itself
            // it is currently on the stack
            let v_info = SCCNodeInfo(*next_index, *next_index, true);
            node_info.insert(v.clone(), v_info);
            // update the next index for future or recursive calls
            *next_index += 1;

            // Consider all nodes with a directed edge from v
            for u in &graph[&v.clone()] {
                let u_info = node_info.get_mut(&u);
                match u_info {
                    Some(SCCNodeInfo(u_index, _, u_onstack)) => {
                        // if u has been processed before and it is on the stack we perform further processing
                        if *u_onstack {
                            // u is reachable by v, so update the lowest node reachable by v
                            // to the minimum of v's current "lowest link", and the index of u
                            // we use the index of u, not its "lowest link" because u is already
                            // on the stack, so it is not in the DFS subtree of v
                            // the "lowest link" takes into account only nodes in the DFS subtree of v
                            let u_index = *u_index;
                            let v_info = node_info.get_mut(&v).unwrap();
                            v_info.1 = u32::min(v_info.1, u_index);
                        }
                        // else u is not on the stack, so (v, u) is an edge to an SCC already
                        // found and should be ignored
                    }
                    // if u hasn't been processed before, recurse
                    None => {
                        // since u hadn't been processed before, we try to mark all nodes in u's subtree
                        // that are in the SCC containing u; since v can reach u and it wasn't on the stack
                        find_strongly_connected_components(
                            u.clone(),
                            graph,
                            node_info,
                            stack,
                            strongly_connected_components,
                            next_index,
                        );

                        // u is in the DFS subtree of v, and so u's SCC is the same as v's, so we update
                        // the lowest index reachable by v to the lowest node reachable by u
                        let u_lowlink = node_info.get(&u).unwrap().1;
                        let v_info = node_info.get_mut(&v).unwrap();
                        v_info.1 = u32::min(v_info.1, u_lowlink);
                    }
                }
            }

            let v_info = node_info.get_mut(&v).unwrap();
            // If v's index is the lowest index reachable by any nodes in its SCC
            // then v is a root node of an SCC in the DFS subtree for v's SCC
            // So, if v's index is it's "lowest link", pop the stack until we hit v to generate its SCC
            if v_info.0 == v_info.1 {
                // start a new strongly connected component
                let mut new_scc = HashSet::<Literal>::new();
                // Until we hit v, pop the stack to create the new strongly connected component
                loop {
                    // set each w popped to be off the stack
                    let w = stack.pop().unwrap();
                    node_info.get_mut(&w).unwrap().2 = false;
                    new_scc.insert(w.clone());
                    if w == v {
                        break;
                    }
                }
                // add the strongly connected component to the collection of
                strongly_connected_components.push(new_scc);
            }
        }

        // we now find the strongly connected components of the implication graph of the
        // current 2CNF. The graph maps literals to the literals they imply
        let mut impl_graph = HashMap::<Literal, HashSet<Literal>>::new();
        // Create a node for every literal
        for var in &self.variables {
            // positive literals
            impl_graph.insert(
                Literal(var.clone().to_string(), false),
                HashSet::<Literal>::new(),
            );
            // negative literals
            impl_graph.insert(
                Literal(var.clone().to_string(), true),
                HashSet::<Literal>::new(),
            );
        }
        // Populate the edges with the implications and contrapositives equivalent to each clause
        for (lit1, lit2) in &self.clauses {
            let Literal(var1, neg1) = lit1;
            let Literal(var2, neg2) = lit2;

            // lit1 V lit2 = !lit1 => lit2
            impl_graph
                .get_mut(&Literal(var1.clone().to_string(), !neg1))
                .unwrap()
                .insert(Literal(var2.clone().to_string(), *neg2));
            // (!lit1 => lit2) = (!lit2 => lit1)
            impl_graph
                .get_mut(&Literal(var2.clone().to_string(), !neg2))
                .unwrap()
                .insert(Literal(var1.clone().to_string(), *neg1));
        }

        // let this be the strongly connected components we find
        let mut strongly_connected_components: Vec<HashSet<Literal>> = vec![];
        // let this be the search stack used for DFS to find strongly connected components
        let mut scc_stack: Vec<Literal> = vec![];
        // let this store the information for each node required to perform the search for the SCCs
        let mut scc_node_info = HashMap::<Literal, SCCNodeInfo>::new();
        // let this store the index used to assign unique identifiers to the nodes in the graph
        let mut next_index: u32 = 0;

        // find the strongly connected components of impl_graph
        for var in &self.variables {
            // search every positive and negative literal, but only perform the DFS if these literals have not been searched before
            // which we can tell by whether or not node_info contains them
            let pos_lit = Literal(var.clone().to_string(), false);
            if !scc_node_info.contains_key(&pos_lit) {
                find_strongly_connected_components(
                    pos_lit,
                    &impl_graph,
                    &mut scc_node_info,
                    &mut scc_stack,
                    &mut strongly_connected_components,
                    &mut next_index,
                );
            }

            let neg_lit = Literal(var.clone().to_string(), true);
            if !scc_node_info.contains_key(&neg_lit) {
                find_strongly_connected_components(
                    neg_lit,
                    &impl_graph,
                    &mut scc_node_info,
                    &mut scc_stack,
                    &mut strongly_connected_components,
                    &mut next_index,
                );
            }
        }

        // Now, the instance is unSAT iff any strongly connected component contains both a literal and its negation
        // if any SCC contains a literal and its negation, then both must be true in order to satisfy the instance CNF
        // but that is a contradiction, and so the CNF is unSAT, meaning we can't find any SAT assignment for it
        for scc in &strongly_connected_components {
            for Literal(var, neg) in scc {
                if scc.contains(&Literal(var.clone().to_string(), !neg)) {
                    return None;
                }
            }
        }

        // else it is SAT, we construct a satisfying instance for the formula
        // this is easy because SCCs are generated by Tarjan's algorithm in reverse topological order
        // when we process the SCCs in reverse topological order, we can assign satisfying
        // values to the literals in the SCCs without contradicting other SCCs
        let mut assignment = HashMap::<String, bool>::new();
        for scc in &strongly_connected_components {
            for Literal(var, neg) in scc {
                // if a variable has already been assigned, skip it
                if assignment.contains_key(var) {
                    continue;
                }

                // otherwise, we want its literal to be true in this SCC
                let assign = if *neg { false } else { true };
                assignment.insert(var.clone().to_string(), assign);
            }
        }

        // Just a sanity check
        assert!(
            self.evaluate(&assignment),
            "Assignment found does not satisfy the 2CNF"
        );

        Some(assignment)
    }

    fn evaluate(&self, assignment: &HashMap<String, bool>) -> bool {
        // iterate over every clause in the instance, and ensure that it is satisfied
        for (lit1, lit2) in &self.clauses {
            let Literal(var1, neg1) = lit1;
            let Literal(var2, neg2) = lit2;

            // this will panic if the assignment does not contain all variables
            let assign1 = assignment[var1];
            let assign2 = assignment[var2];

            // values of each literal given this assignment
            let val1 = if *neg1 { !assign1 } else { assign1 };
            let val2 = if *neg2 { !assign2 } else { assign2 };

            // either val1 or val2 should be true
            if !val1 && !val2 {
                return false;
            }
        }

        // if we got here, all clauses must be satisfied
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_valid_descr() {
        // valid forms
        assert!(TwoCnf::is_valid_descr("(a|b)&(c|d)".to_string()));
        assert!(TwoCnf::is_valid_descr("(a|b)&(c|~d)".to_string()));
        assert!(TwoCnf::is_valid_descr("(a|b)&c".to_string()));
        assert!(TwoCnf::is_valid_descr("a".to_string()));
        assert!(TwoCnf::is_valid_descr(
            "(~a|~b)& (~c|d) & (a|~b)&(x1|Y)".to_string()
        ));
        assert!(TwoCnf::is_valid_descr("a&b&~c".to_string()));
        assert!(TwoCnf::is_valid_descr(
            "c23&(a|b)&(c|~a)&(~d|e)&(c23|~b)".to_string()
        ));

        // invalid forms
        assert!(!TwoCnf::is_valid_descr("(a&b)|(c&d)".to_string()));
        assert!(!TwoCnf::is_valid_descr("a&(b|c)&((c|a)&d|e)".to_string()));
        assert!(!TwoCnf::is_valid_descr("a&(b|(c|d))".to_string()));
        assert!(!TwoCnf::is_valid_descr("(a|b|c)".to_string()));
        assert!(!TwoCnf::is_valid_descr("a&b&(c|a|~b)".to_string()));
        assert!(!TwoCnf::is_valid_descr("23c&(a|b)".to_string()));
        assert!(!TwoCnf::is_valid_descr("X1|x2".to_string()));
    }

    #[test]
    fn test_init() {
        let tc = TwoCnf::from_description("(a|b)&(c|d)".to_string());
        assert!(
            tc.variables
                == HashSet::from([
                    "a".to_string(),
                    "b".to_string(),
                    "c".to_string(),
                    "d".to_string()
                ])
        );
        assert!(
            tc.clauses
                == HashSet::from([
                    (Literal("a".into(), false), Literal("b".into(), false)),
                    (Literal("c".into(), false), Literal("d".into(), false))
                ])
        );

        let tc = TwoCnf::from_description("(a|~b)&c".to_string());
        assert!(tc.variables == HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]));
        assert!(
            tc.clauses
                == HashSet::from([
                    (Literal("a".into(), false), Literal("b".into(), true)),
                    (Literal("c".into(), false), Literal("c".into(), false))
                ])
        );

        let tc = TwoCnf::from_description("hello there & (a | hello  there)".to_string());
        assert!(tc.variables == HashSet::from(["a".to_string(), "hellothere".to_string()]));
        assert!(
            tc.clauses
                == HashSet::from([
                    (
                        Literal("hellothere".into(), false),
                        Literal("hellothere".into(), false)
                    ),
                    (
                        Literal("a".into(), false),
                        Literal("hellothere".into(), false)
                    )
                ])
        );
    }

    #[should_panic]
    #[test]
    fn test_bad_init() {
        // This is a DNF
        TwoCnf::from_description("a|b".to_string());
    }

    #[test]
    fn test_find_sat_assignment() {
        // SAT
        assert!(TwoCnf::from_description(String::from("(a|~b)"))
            .find_sat_assignment()
            .is_some());
        assert!(
            TwoCnf::from_description(String::from("(a|~b)&(~a|b)&(~a|~b)"))
                .find_sat_assignment()
                .is_some()
        );
        assert!(TwoCnf::from_description(String::from(
            "(x1|x2) & (x1|~x3) & (~x1|~x2) & (x1|x4) & (~x1|~x5)"
        ))
        .find_sat_assignment()
        .is_some());
        assert!(
            TwoCnf::from_description(String::from("(a|c)&(~a|~b)&(b|~c)"))
                .find_sat_assignment()
                .is_some()
        );
        assert!(
            TwoCnf::from_description(String::from("(a|~b)&(~a|b)&(~a|~b)&(a|~c)"))
                .find_sat_assignment()
                .is_some()
        );
        assert!(TwoCnf::from_description(String::from("(~x3|x1)&(~x3|x2)"))
            .find_sat_assignment()
            .is_some());

        // UNSAT
        assert!(TwoCnf::from_description(String::from("a&~a"))
            .find_sat_assignment()
            .is_none());
        assert!(
            TwoCnf::from_description(String::from("(a|b)&(a|~b)&(~a|b)&(~a|~b)"))
                .find_sat_assignment()
                .is_none()
        );
        assert!(
            TwoCnf::from_description(String::from("(a|c)&(~a|~b)&(b|~c)&(a|~c)&(b|c)"))
                .find_sat_assignment()
                .is_none()
        );
        // Following UNSAT examples are from here: https://math.illinois.edu/system/files/2020-09/V.%20Karve-1.pdf
        assert!(TwoCnf::from_description(String::from(
            "(a|b)&(~a|c)&(~b|c)&(~c|d)&(~c|e)&(~d|~e)"
        ))
        .find_sat_assignment()
        .is_none());
        assert!(TwoCnf::from_description(String::from(
            "(a|b)&(~a|c)&(~b|c)&(~c|d)&(~d|e)&(~d|f)&(~e|~f)"
        ))
        .find_sat_assignment()
        .is_none());
        assert!(
            TwoCnf::from_description(String::from("(a|b)&(a|c)&(~a|d)&(~b|~c)&(b|~d)&(c|~d)"))
                .find_sat_assignment()
                .is_none()
        );
        assert!(TwoCnf::from_description(String::from(
            "(a|b)&(~a|d)&(b|c)&(~b|d)&(~b|e)&(~d|~c)&(~e|~d)"
        ))
        .find_sat_assignment()
        .is_none());
    }

    #[test]
    fn test_evaluate() {
        // This is UNSAT so nothing should make it true
        let tc1 = TwoCnf::from_description(String::from("(a|b)&(a|~b)&(~a|b)&(~a|~b)"));
        let assignment11 =
            HashMap::<String, bool>::from([("a".to_string(), false), ("b".to_string(), false)]);
        let assignment12 =
            HashMap::<String, bool>::from([("a".to_string(), true), ("b".to_string(), false)]);
        let assignment13 =
            HashMap::<String, bool>::from([("a".to_string(), false), ("b".to_string(), true)]);
        let assignment14 =
            HashMap::<String, bool>::from([("a".to_string(), true), ("b".to_string(), true)]);
        assert!(!tc1.evaluate(&assignment11));
        assert!(!tc1.evaluate(&assignment12));
        assert!(!tc1.evaluate(&assignment13));
        assert!(!tc1.evaluate(&assignment14));

        let tc2 = TwoCnf::from_description(String::from(
            "(x1|x2) & (x1|~x3) & (~x1|~x2) & (x1|x4) & (~x1|~x5)",
        ));
        // this should not satisfy it
        let assignment21 = HashMap::<String, bool>::from([
            ("x1".to_string(), true),
            ("x2".to_string(), false),
            ("x3".to_string(), true),
            ("x4".to_string(), false),
            ("x5".to_string(), true),
        ]);
        // this should satisfy it
        let assignment22 = HashMap::<String, bool>::from([
            ("x1".to_string(), true),
            ("x2".to_string(), false),
            ("x3".to_string(), true),
            ("x4".to_string(), true),
            ("x5".to_string(), false),
        ]);
        assert!(!tc2.evaluate(&assignment21));
        assert!(tc2.evaluate(&assignment22));
    }
}
