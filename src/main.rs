use std::collections::{HashSet, HashMap};
use regex::Regex;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut tc = TwoCnf::from_description(args[1].clone());

    println!("Formula is SAT: {}", tc.is_sat());
}

// name, negated
#[derive(PartialEq, Eq, Clone, Hash)]
struct Literal(String, bool);

struct TwoCnf {
    variables: HashSet<String>,
    clauses: HashSet<(Literal, Literal)>
}

impl TwoCnf {
    /// A 2CNF is a 2-level Boolean circuit in Conjunctive Normal Form
    ///.where every clause has at most 2 literals. Thus, parentheses can
    /// e nested at most one level deep, within parentheses we only see
    /// the | operator, and between parentheses we see only the & operator
    fn is_valid_descr(description: String) -> bool {
        let valid_clause_re = Regex::new(r"^(\(~?[a-zA-Z][a-zA-Z0-9]*\|~?[a-zA-Z][a-zA-Z0-9]*\)|~?[a-zA-Z][a-zA-Z0-9]*)$").unwrap();
        // clone for correct error messaging
        let mut descr = description.clone();
        // remove whitespace
        descr.retain(|c| !c.is_whitespace());
        // split by & and assert every clause matches the regex
        descr.split('&')
            .all(|val| valid_clause_re.is_match(val))
    }

    fn from_description(description: String) -> Self {
        // check description is valid
        assert!(Self::is_valid_descr(description.clone()), "Invalid 2CNF description: {}", description);

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
        let mut variables = HashSet::<String>::new();
        let clauses: HashSet<(Literal, Literal)> = description.split('&')
            .map(|clause| {
                if clause.contains('|') {
                    // in this case there are 2 literals in the clause
                    let mut caps = literal_re.captures_iter(clause);
                    let lit1 = str_to_literal(&caps.next().unwrap()[0]);
                    let lit2 = str_to_literal(&caps.next().unwrap()[0]);
                    // insert the names into the variables set
                    variables.insert(lit1.0.clone());
                    variables.insert(lit2.0.clone());
                    (lit1, lit2)
                }
                else {
                    // else there is only one literal in the clause
                    let lit = str_to_literal(clause);
                    // insert the name into the variabls set
                    variables.insert(lit.0.clone());
                    // duplicate the literal, x or x is equivalent to x
                    (lit.clone(), lit)
                }
            })
            .collect();

        Self {
            variables,
            clauses,
        }
    }

    fn is_sat(&mut self) -> bool {
        // The strongly connected components of the implication graph of the CNF
        // allow us to determine if the instance is satisfiable
        // The instance is satisfiable iff its strongly connected components
        // do not connect any literal to its negation

        // We have to construct the implication graph for the CNF
        // in order to do this, we utilize data structures that will help us find strongly connected components
        // index, lowlink, onstack
        #[derive(PartialEq, Eq, Hash)]
        struct SCCNodeInfo(u32, u32, bool);

        // algorithm to find strongly connected components
        // Reference: https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
        fn find_scc(
            v: Literal,
            graph: &HashMap<Literal, HashSet<Literal>>,
            node_info: &mut HashMap<Literal, SCCNodeInfo>,
            stack: &mut Vec<Literal>,
            strongly_connected_components: &mut Vec<HashSet<Literal>>,
            next_index: &mut u32
        ) {
            // set the depth index for v to the smallest unused index
            stack.push(v.clone());
            let v_info = SCCNodeInfo(*next_index, *next_index, true);
            node_info.insert(v.clone(), v_info);
            *next_index += 1;

            // Consider all edges implied by v
            for u in &graph[&v.clone()] {
                let u_info = node_info.get_mut(&u);
                match u_info {
                    // if u has been processed before, and it is on the stack we perform further processing
                    // if w is not on the stack then (v, u) is an edge to an SCC already found and should be ignored
                    Some(SCCNodeInfo(u_index, _u_lowlink, u_onstack)) => {
                        if *u_onstack {
                            // update the lowlink of v
                            let u_index = *u_index;
                            let v_info = node_info.get_mut(&v).unwrap();
                            v_info.1 = u32::min(v_info.1, u_index);
                        }
                    }
                    // if u hasn't been processed before, recurse
                    None => {
                        find_scc(u.clone(), graph, node_info, stack, strongly_connected_components, next_index);
                        // update the lowlink of v
                        let u_lowlink = node_info.get(&u).unwrap().1;
                        let v_lowlink = node_info.get(&v).unwrap().1;
                        node_info.get_mut(&v).unwrap().1 = u32::min(v_lowlink, u_lowlink);
                    }
                }
            }
            
            // If v is a root node, pop the stack to generate an SCC
            // we check the v is a root node if v.index == v.lowlink
            let v_info = node_info.get_mut(&v).unwrap();
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

                // add the strongly connected component to the input vec
                strongly_connected_components.push(new_scc);
            }
        }

        // we now find the strongly connected components of the implication graph
        // first construct the implication graph
        // map literals to the edges to which they are directed, along with infomration useful for 
        // the search for strongly connected components
        let mut impl_graph = HashMap::<Literal, HashSet<Literal>>::new();
        // Create a node for every literal
        for var in &self.variables {
            // positive literals
            impl_graph.insert(Literal(var.clone().to_string(), false), HashSet::<Literal>::new());
            // negative literals
            impl_graph.insert(Literal(var.clone().to_string(), true), HashSet::<Literal>::new());
        }
        // Populate the edges with the implications
        for (lit1, lit2) in &self.clauses {
            let Literal(var1, neg1) = lit1;
            let Literal(var2, neg2) = lit2;

            // var1 V var2 = !var1 => var2
            impl_graph.get_mut(&Literal(var1.clone().to_string(), !neg1))
                .unwrap().insert(Literal(var2.clone().to_string(), *neg2));
            // !var1 => var2 = !var2 => var1
            impl_graph.get_mut(&Literal(var2.clone().to_string(), !neg2))
                .unwrap().insert(Literal(var1.clone().to_string(), *neg1));
        }

        // let this be the strongly connected components we find
        let mut strongly_connected_components: Vec<HashSet<Literal>> = vec![];
        // let this be the search stack for strongly connected components
        let mut scc_stack: Vec<Literal> = vec![];
        // let this store the information required to perform the search for the SCCs
        let mut scc_node_info = HashMap::<Literal, SCCNodeInfo>::new();
        // let this store the index used to assign unique identifiers to roots of SCCs
        let mut next_index: u32 = 0;

        // find the strongly connected components of impl_graph
        // for each variable
        for var in &self.variables {
            // search every positive and negative literal
            // but only run the algorithm if these literals have not been searched before
            // which we can tell by whether or not node_info contains them
            let pos_lit = Literal(var.clone().to_string(), false);
            if !scc_node_info.contains_key(&pos_lit) {
                find_scc(pos_lit, &impl_graph, &mut scc_node_info, &mut scc_stack, &mut strongly_connected_components, &mut next_index);
            }

            let neg_lit = Literal(var.clone().to_string(), true);
            if !scc_node_info.contains_key(&neg_lit) {
                find_scc(neg_lit, &impl_graph, &mut scc_node_info, &mut scc_stack, &mut strongly_connected_components, &mut next_index);
            }
        }

        // Now, the instance is unSAT iff any strongly connected component contains both a literal and its negation
        for scc in &strongly_connected_components {
            for Literal(var, neg) in scc {
                if scc.contains(&Literal(var.clone().to_string(), !neg)) {
                    return false;
                }
            }
        }

        // TODO: construct a satisfying instance for the formula

        // else it is SAT
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
        assert!(TwoCnf::is_valid_descr("(~a|~b)& (~c|d) & (a|~b)&(x1|Y)".to_string()));
        assert!(TwoCnf::is_valid_descr("a&b&~c".to_string()));
        assert!(TwoCnf::is_valid_descr("c23&(a|b)&(c|~a)&(~d|e)&(c23|~b)".to_string()));

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
        assert!(tc.variables == HashSet::from(["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()]));
        assert!(tc.clauses == HashSet::from([(Literal("a".into(), false), Literal("b".into(), false)), (Literal("c".into(), false), Literal("d".into(), false))]));

        let tc = TwoCnf::from_description("(a|~b)&c".to_string());
        assert!(tc.variables == HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]));
        assert!(tc.clauses == HashSet::from([(Literal("a".into(), false), Literal("b".into(), true)), (Literal("c".into(), false), Literal("c".into(), false))]));
    }

    #[should_panic]
    #[test]
    fn test_bad_init() {
        // This is a DNF
        TwoCnf::from_description("a|b".to_string());
    }

    #[test]
    fn test_is_sat() {
        // SAT
        assert!(TwoCnf::from_description(String::from("(a|~b)")).is_sat());
        assert!(TwoCnf::from_description(String::from("(a|~b)&(~a|b)&(~a|~b)")).is_sat());
        assert!(TwoCnf::from_description(String::from("(x1|x2) & (x1|~x3) & (~x1|~x2) & (x1|x4) & (~x1|~x5)")).is_sat());
        assert!(TwoCnf::from_description(String::from("(a|c)&(~a|~b)&(b|~c)")).is_sat());
        assert!(TwoCnf::from_description(String::from("(a|~b)&(~a|b)&(~a|~b)&(a|~c)")).is_sat());
        assert!(TwoCnf::from_description(String::from("(~x3|x1)&(~x3|x2)")).is_sat());

        // UNSAT
        assert!(!TwoCnf::from_description(String::from("a&~a")).is_sat());
        assert!(!TwoCnf::from_description(String::from("(a|b)&(a|~b)&(~a|b)&(~a|~b)")).is_sat());
        assert!(!TwoCnf::from_description(String::from("(a|c)&(~a|~b)&(b|~c)&(a|~c)&(b|c)")).is_sat());
        // Following UNSAT examples are from here: https://math.illinois.edu/system/files/2020-09/V.%20Karve-1.pdf
        assert!(!TwoCnf::from_description(String::from("(a|b)&(~a|c)&(~b|c)&(~c|d)&(~c|e)&(~d|~e)")).is_sat());
        assert!(!TwoCnf::from_description(String::from("(a|b)&(~a|c)&(~b|c)&(~c|d)&(~d|e)&(~d|f)&(~e|~f)")).is_sat());
        assert!(!TwoCnf::from_description(String::from("(a|b)&(a|c)&(~a|d)&(~b|~c)&(b|~d)&(c|~d)")).is_sat());
        assert!(!TwoCnf::from_description(String::from("(a|b)&(~a|d)&(b|c)&(~b|d)&(~b|e)&(~d|~c)&(~e|~d)")).is_sat());
    }
}
