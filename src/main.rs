use std::collections::HashSet;
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

    fn prune_clauses(&mut self) {
        // Remove (a or ~a) from self.clauses
        self.clauses.retain(|clause| {
            let Literal(name1, sign1) = &clause.0;
            let Literal(name2, sign2) = &clause.1;

            // !(name1 == name2 && sign1 != sign2)
            name1 != name2 || sign1 == sign2
        });
        
        // If (a or b) in self.clauses remove (b or a)
        let mut parallel_delete_clauses = self.clauses.clone();
        self.clauses.retain(|clause| {
            let reordered_clause = (clause.1.clone(), clause.0.clone());
            
            let delete = parallel_delete_clauses.contains(&reordered_clause);
            if delete {
                parallel_delete_clauses.remove(clause);
            }
            !delete
        });
    }

    fn is_sat(&mut self) -> bool {
        // If there are no variables, it is trivially satisfiable
        if self.variables.is_empty() {
            return true;
        }

        // For each variable
        for var in &self.variables {
            let mut new_clauses = HashSet::<(Literal, Literal)>::new();
            // Resolve as many clauses as possible
            for clause1 in &self.clauses {
                for clause2 in &self.clauses {
                    // Can't resolve a clause with itself
                    if clause1 == clause2 {
                        continue;
                    }

                    // if the names are the same but the signs differ, they can be resolved
                    match (clause1, clause2) {
                        ((Literal(n1, s1), c1_other_lit), (Literal(n2, s2), c2_other_lit)) 
                        | ((Literal(n1, s1), c1_other_lit), (c2_other_lit, Literal(n2, s2)))
                        | ((c1_other_lit, Literal(n1, s1)), (Literal(n2, s2), c2_other_lit))
                        | ((c1_other_lit, Literal(n1, s1)), (c2_other_lit, Literal(n2, s2)))
                        if n1 == var && n2 == var && s1 != s2 => {
                            // Resolved clause
                            new_clauses.insert((c1_other_lit.clone(), c2_other_lit.clone()));
                        },
                        _ => continue
                    }
                }
            }

            // Insert the new clauses into the TwoCnf's clauses
            for clause in new_clauses {
                self.clauses.insert(clause);
            }
        }

        self.prune_clauses();

        // Search for (a or a) and (~a or ~a) in the clauses
        for var in &self.variables {
            let pos_clause = (Literal(var.clone(), false), Literal(var.clone(), false));
            let neg_clause = (Literal(var.clone(), true), Literal(var.clone(), true));

            // IN this case, it is not SAT
            if self.clauses.contains(&pos_clause) && self.clauses.contains(&neg_clause) {
                return false;
            }
        }

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
}
