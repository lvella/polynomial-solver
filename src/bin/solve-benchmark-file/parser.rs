use std::{collections::HashMap, fmt::Debug, process::Output, str::FromStr};

use pest::{iterators::Pair, Parser};
use polynomial_solver::polynomial::{
    monomial_ordering::Ordering, Coefficient, Polynomial, Term, VariablePower,
};

#[derive(Parser)]
#[grammar = "bin/solve-benchmark-file/systems.pest"]
pub struct SystemsParser;

pub fn parse<O, C>(unparsed_file: &str) -> Vec<Vec<Polynomial<O, u32, C, u32>>>
where
    O: Ordering,
    C: Coefficient + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    let file = SystemsParser::parse(Rule::file, unparsed_file)
        .expect("parsing failed")
        .next()
        .unwrap();

    file.into_inner()
        .filter(|x| x.as_rule() == Rule::system)
        .map(parse_system)
        .collect()
}

struct VarEnumerator<'a>(HashMap<&'a str, u32>);

impl<'a> VarEnumerator<'a> {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get_id(&mut self, name: &'a str) -> u32 {
        let size = self.0.len() as u32;
        *self.0.entry(name).or_insert(size)
    }
}

fn parse_system<O, C>(system: Pair<'_, Rule>) -> Vec<Polynomial<O, u32, C, u32>>
where
    O: Ordering,
    C: Coefficient + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    let mut vars = VarEnumerator::new();

    system
        .into_inner()
        .filter(|x| x.as_rule() == Rule::polynomial)
        .map(|x| parse_polynomial(&mut vars, x))
        .collect()
}

fn parse_polynomial<'a, O, C>(
    var_ids: &mut VarEnumerator<'a>,
    polynomial: Pair<'a, Rule>,
) -> Polynomial<O, u32, C, u32>
where
    O: Ordering,
    C: Coefficient + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    Polynomial::from_terms(
        polynomial
            .into_inner()
            .map(|x| parse_terms(var_ids, x))
            .collect(),
    )
}
enum FactorValue<C> {
    None,
    Var(u32),
    Literal(C),
}

fn parse_terms<'a, O, C>(
    var_ids: &mut VarEnumerator<'a>,
    term: Pair<'a, Rule>,
) -> Term<O, u32, C, u32>
where
    O: Ordering,
    C: Coefficient + FromStr + num_traits::pow::Pow<u32, Output = C>,
    <C as FromStr>::Err: Debug,
{
    assert!(term.as_rule() == Rule::term);

    let mut coef = C::one();
    let mut vars = Vec::new();

    for factor in term.into_inner() {
        let mut minus = false;
        let mut value = FactorValue::<C>::None;
        let mut power = 1u32;

        for elem in factor.into_inner() {
            match elem.as_rule() {
                Rule::sign => {
                    if elem.as_str() == "-" {
                        minus = !minus;
                    }
                }
                Rule::var => {
                    value = FactorValue::Var(var_ids.get_id(elem.as_str()));
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
                coef *= &lit.pow(power);
            }
        }
    }

    Term::new_multi_vars(coef, vars)
}
