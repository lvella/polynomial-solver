use std::{collections::HashMap, fmt::Debug, str::FromStr};

use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use polynomial_solver::{
    field::CommutativeRing,
    polynomial::{monomial_ordering::Ordering, Polynomial, Term, VariablePower},
};

#[derive(Parser)]
#[grammar = "bin/grobner-basis/maple_like.pest"]
pub struct SystemsParser;

/// Parses a set of polynomial systems provided in a very specific limited
/// subset of Maple language. See example in "benchmark.txt".
pub fn parse_maple_like<O, C>(
    unparsed_file: &str,
) -> Result<Vec<Vec<Polynomial<O, u32, C, i32>>>, String>
where
    O: Ordering,
    C: CommutativeRing + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    let file = SystemsParser::parse(Rule::file, unparsed_file)
        .map_err(|err| format!("Parsing failed: {:#?}", err))?
        .next()
        .unwrap();

    file.into_inner()
        .filter(|x| x.as_rule() == Rule::system)
        .map(parse_system)
        .collect()
}

fn parse_system<O, C>(system: Pair<'_, Rule>) -> Result<Vec<Polynomial<O, u32, C, i32>>, String>
where
    O: Ordering,
    C: CommutativeRing + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    let mut iter = system.into_inner();

    let mut vars = Vec::new();

    loop {
        let var = iter.peek().unwrap();
        if var.as_rule() != Rule::var {
            break;
        }

        vars.push(var.as_str());
        iter.next();
    }

    let vars = vars
        .into_iter()
        .rev()
        .enumerate()
        .map(|(val, key)| (key, val as u32))
        .collect::<HashMap<_, _>>();

    iter.map(|x| {
        assert!(x.as_rule() == Rule::polynomial);
        parse_polynomial(&vars, x)
    })
    .collect()
}

fn parse_polynomial<'a, O, C>(
    var_ids: &'a HashMap<&'a str, u32>,
    polynomial: Pair<'a, Rule>,
) -> Result<Polynomial<O, u32, C, i32>, String>
where
    O: Ordering,
    C: CommutativeRing + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    polynomial
        .into_inner()
        .map(|x| parse_terms(var_ids, x))
        .collect::<Result<_, _>>()
        .map(|x| Polynomial::from_terms(x))
}
enum FactorValue<C> {
    None,
    Var(u32),
    Literal(C),
}

fn parse_terms<'a, O, C>(
    var_ids: &'a HashMap<&'a str, u32>,
    term: Pair<'a, Rule>,
) -> Result<Term<O, u32, C, i32>, String>
where
    O: Ordering,
    C: CommutativeRing + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    assert!(term.as_rule() == Rule::term);

    let mut coef = C::one();
    let mut vars = Vec::new();

    for factor in term.into_inner() {
        let mut minus = false;
        let mut value = FactorValue::<C>::None;
        let mut power = 1i32;

        for elem in factor.into_inner() {
            match elem.as_rule() {
                Rule::sign => {
                    if elem.as_str() == "-" {
                        minus = !minus;
                    }
                }
                Rule::var => {
                    value = FactorValue::Var(*var_ids.get(elem.as_str()).ok_or_else(|| {
                        format!(
                            "Variable \"{}\" not defined in the variable list.",
                            elem.as_str()
                        )
                    })?);
                }
                Rule::literal => {
                    value = FactorValue::Literal(elem.as_str().parse().unwrap());
                }
                Rule::power => {
                    power = elem.as_str().parse().unwrap();
                }
                _ => {
                    panic!("Invalid grammar!")
                }
            }
        }

        if minus {
            let tmp = std::mem::replace(&mut coef, C::zero());
            coef -= tmp;
        }

        match value {
            FactorValue::None => panic!("Invalid grammar!"),
            FactorValue::Var(id) => {
                vars.push(VariablePower::new(id, power));
            }
            FactorValue::Literal(lit) => {
                coef *= &lit.pow(power as u32);
            }
        }
    }

    Ok(Term::new_multi_vars(coef, vars))
}
