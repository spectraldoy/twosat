use std::collections::{HashSet, HashMap};
use regex::Regex;

// name, negated
#[derive(PartialEq, Eq)]
struct Literal(String, bool);

struct TwoCnf {
    variables: HashSet<String>,
    clauses: Vec<(Literal, Literal)>
}

impl TwoCnf {
    /// A 2CNF is a 2-level Boolean circuit in Conjunctive Normal Form
    ///.where every clause has at most 2 literals. Thus, parentheses can
    /// e nested at most one level deep, within parentheses we only see
    /// the | operator, and between parentheses we see only the & operator
    fn is_valid_descr(description: &str) -> bool {
        let valid_clause_re = Regex::new(r"^(\(~?[a-zA-Z][a-zA-Z0-9]*\|~?[a-zA-Z][a-zA-Z0-9]*\)|~?[a-zA-Z][a-zA-Z0-9]*)$").unwrap();
        // clone for correct error messaging
        let mut descr = description.to_string();
        // remove whitespace
        descr.retain(|c| !c.is_whitespace());
        // split by & and assert every clause matches the regex
        descr.split('&')
            .all(|val| valid_clause_re.is_match(val))
    }

    fn from_description(description: &str) -> Self {
        // check description is valid
        assert!(Self::is_valid_descr(description), "Invalid description: {}", description);

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
        let clauses: Vec<(Literal, Literal)> = description.split('&')
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
                    // use "_" as an "empty literal", i.e., meant to indicate the value False
                    (str_to_literal(clause), Literal(String::from("_"), false))
                }
            })
            .collect();

        Self {
            variables,
            clauses,
        }
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_valid_descr() {
        // valid forms
        assert!(TwoCnf::is_valid_descr("(a|b)&(c|d)"));
        assert!(TwoCnf::is_valid_descr("(a|b)&(c|~d)"));
        assert!(TwoCnf::is_valid_descr("(a|b)&c"));
        assert!(TwoCnf::is_valid_descr("a"));
        assert!(TwoCnf::is_valid_descr("(~a|~b)& (~c|d) & (a|~b)&(x1|Y)"));
        assert!(TwoCnf::is_valid_descr("a&b&~c"));
        assert!(TwoCnf::is_valid_descr("c23&(a|b)&(c|~a)&(~d|e)&(c23|~b)"));

        // invalid forms
        assert!(!TwoCnf::is_valid_descr("(a&b)|(c&d)"));
        assert!(!TwoCnf::is_valid_descr("a&(b|c)&((c|a)&d|e)"));
        assert!(!TwoCnf::is_valid_descr("a&(b|(c|d))"));
        assert!(!TwoCnf::is_valid_descr("(a|b|c)"));
        assert!(!TwoCnf::is_valid_descr("a&b&(c|a|~b)"));
        assert!(!TwoCnf::is_valid_descr("23c&(a|b)"));
        assert!(!TwoCnf::is_valid_descr("X1|x2"));
    }

    #[test]
    fn test_init() {
        let tc = TwoCnf::from_description("(a|b)&(c|d)");
        assert!(tc.variables == HashSet::from(["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()]));
        assert!(tc.clauses == [(Literal("a".into(), false), Literal("b".into(), false)), (Literal("c".into(), false), Literal("d".into(), false))]);

        let tc = TwoCnf::from_description("(a|~b)&c");
        assert!(tc.variables == HashSet::from(["a".to_string(), "b".to_string(), "c".to_string()]));
        assert!(tc.clauses == [(Literal("a".into(), false), Literal("b".into(), true)), (Literal("c".into(), false), Literal("_".into(), false))]);
    }

    #[should_panic]
    #[test]
    fn test_bad_init() {
        // This is a DNF
        TwoCnf::from_description("a|b");
    }
}
