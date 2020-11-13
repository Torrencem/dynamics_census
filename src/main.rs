
#![allow(unused, dead_code)]

use std::str::FromStr;
use std::num::ParseIntError;
extern crate anyhow;
use anyhow::Error;
use anyhow::Context;

mod sigma_invariants;
use sigma_invariants::*;
extern crate polynomial;
extern crate num_field_quad;

use polynomial::*;
use num_field_quad::*;
use num_field_quad::mod_p::*;

use num_traits::{Zero, One};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProjectivePoint {
    Finite(u16),
    Infinite,
}

impl FromStr for ProjectivePoint {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let coords: Vec<&str> = s.trim_matches(|p| p == '(' || p == ')')
                                 .split(':')
                                 .map(|s| s.trim())
                                 .collect();

        let x = coords[0].parse::<u16>()?;
        let y = coords[1].parse::<u16>()?;

        match y {
            0 => Ok(ProjectivePoint::Infinite),
            _ => Ok(ProjectivePoint::Finite(x / y)),
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct Morphism {
    b: u16,
    c: u16,
}

impl FromStr for Morphism {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let coords: Vec<&str> = s.trim_matches(|p| p == '(' || p == ')' || p == 'M')
                                 .split('&')
                                 .map(|s| s.trim())
                                 .collect();

        let x = coords[0].parse::<u16>()?;
        let y = coords[1].parse::<u16>()?;

        Ok(Morphism {
            b: x,
            c: y,
        })
    }
}

#[derive(Clone, Copy, Debug)]
enum CriticalPointEntry {
    Single(u16),
    Double(u16, u16),
}

impl FromStr for CriticalPointEntry {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let coords: Vec<&str> = s.trim_matches(|p| p == '[' || p == ']')
                                 .split('&')
                                 .map(|s| s.trim())
                                 .collect();

        match coords.len() {
            1 => Ok(CriticalPointEntry::Single(coords[0].parse::<u16>()?)),
            _ => Ok(CriticalPointEntry::Double(
                    coords[0].parse::<u16>()?,
                    coords[1].parse::<u16>()?))
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct DBEntry {
    // The first critical point lambda_1
    l1: ProjectivePoint,
    // l1's entry
    l1_entry: CriticalPointEntry,
    // The second critical point lambda_2
    l2: ProjectivePoint,
    // l2's entry
    l2_entry: CriticalPointEntry,
}

impl FromStr for DBEntry {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let entries: Vec<&str> = s.split(",")
                                  .map(|s| s.trim())
                                  .collect();
        Ok(DBEntry {
            l1: ProjectivePoint::from_str(entries[1]).context("error parsing l1")?,
            l1_entry: CriticalPointEntry::from_str(entries[2]).context("error parsing l1_entry")?,
            l2: ProjectivePoint::from_str(entries[3]).context("error parsing l2")?,
            l2_entry: CriticalPointEntry::from_str(entries[4]).context("error parsing l2_entry")?,
        })
    }
}

use std::collections::HashMap;
extern crate regex;
use regex::Regex;

#[derive(Clone, Debug)]
struct DB {
    // A map from primes p to a 
    inner: HashMap<u16, HashMap<Morphism, DBEntry>>,
}

impl FromStr for DB {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = HashMap::new();
        let p_finder = Regex::new(r"p=(\d+)").unwrap();
        for prime_unit in s.split("--- ") {
            if prime_unit.len() == 0 {
                continue;
            }
            // prime_unit is of the form "p={} ---\n..."
            let prime_match = p_finder.captures(prime_unit).unwrap();
            let prime = u16::from_str(&prime_match[1]).context("error parsing prime value")?;
            let mut entries_for_prime = HashMap::new();
            // Populate entries_for_prime
            for line in prime_unit.split('\n').skip(1) {
                if line.len() == 0 {
                    continue;
                }
                let entry = DBEntry::from_str(line)?;
                let morphism_string = line.split(',').nth(0).unwrap().trim();
                let morphism = Morphism::from_str(morphism_string).context("error parsing morphism")?;
                entries_for_prime.insert(morphism, entry);
            }
            result.insert(prime, entries_for_prime);
        }

        Ok(DB { inner: result })
    }
}

// From paper: Subroutine 2A
fn check_rational_periods(numer: Polynomial<ZiElement<i64>>, denom: Polynomial<ZiElement<i64>>, res: ZiElement<i64>, primes: &[u16], db: &DB, crit_pt_a: QFElement<i64>, crit_pt_b: QFElement<i64>) -> bool {
    // NOTE! This function has not been tested yet.
    use std::collections::HashSet;

    assert!(crit_pt_a.is_rational());
    assert!(crit_pt_b.is_rational());
    // let crit_pts = critical_points(numer.clone(), denom.clone());

    let mut poss_period_1 = HashSet::new();
    let mut poss_period_2 = HashSet::new();

    assert!(crit_pt_a.field.c == -1 && crit_pt_b.field.c == -1);

    for p in primes.iter() {
        // Reduce crit_pt_a and crit_pt_b into F_p
        let crit_1 = ProjectivePoint::Finite((
                ZiElement { 
                    inner: QFElement { a: crit_pt_a.a, b: crit_pt_a.b, field: crit_pt_a.field, d: 1 
                    } 
                }.reduce_mod(*p as u32) * 
                ModPElt { 
                    val: mod_inverse(crit_pt_a.d, *p as i64), p: *p as u32
                }
            ).val as u16);
        let crit_2 = ProjectivePoint::Finite((
                ZiElement { 
                    inner: QFElement { a: crit_pt_b.a, b: crit_pt_b.b, field: crit_pt_b.field, d: 1 
                    } 
                }.reduce_mod(*p as u32) * 
                ModPElt { 
                    val: mod_inverse(crit_pt_b.d, *p as i64), p: *p as u32
                }
            ).val as u16);

        if res.reduce_mod(*p as u32) == Zero::zero() {
            continue;
        }

        // reduce phi mod p
        let reduced_numer = Polynomial::new(
            {
                let mut res = vec![];
                for entry in numer.data() {
                    res.push((*entry).reduce_mod(*p as u32));
                }
                res
            }
        );
        let reduced_denom = Polynomial::new(
            {
                let mut res = vec![];
                for entry in denom.data() {
                    res.push((*entry).reduce_mod(*p as u32));
                }
                res
            }
        );
        let map = FiniteQuadraticMap {
            numer: reduced_numer,
            denom: reduced_denom,
        };
        let [s1, s2, s3] = map.sigma_invariants();
        let morphism: Morphism = Morphism {
            b: s1.val as u16,
            c: s2.val as u16,
        };

        // Look up psi in the database
        let dbentry = db.inner.get(p).unwrap().get(&morphism).unwrap();
        
        // Let i = 1
        // Retrieve the set of possible global periods for crit_1
        let possible_periods = if dbentry.l1 == crit_1 {
            dbentry.l1_entry
        } else {
            dbentry.l2_entry
        };
        if poss_period_1.is_empty() {
            // This is the first good prime
            match possible_periods {
                CriticalPointEntry::Single(x) => {
                    poss_period_1.insert(x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_period_1.insert(x);
                    poss_period_1.insert(y);
                }
            }
        } else {
            match possible_periods {
                CriticalPointEntry::Single(x) => {
                    poss_period_1.retain(|&val| val == x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_period_1.retain(|&val| val == x || val == y);
                }
            }
        }

        if poss_period_1.is_empty() {
            return false;
        }
        
        // Let i = 2
        // Retrieve the set of possible global periods for crit_1
        let possible_periods = if dbentry.l1 == crit_2 {
            dbentry.l1_entry
        } else {
            dbentry.l2_entry
        };
        if poss_period_2.is_empty() {
            // This is the first good prime
            match possible_periods {
                CriticalPointEntry::Single(x) => {
                    poss_period_2.insert(x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_period_2.insert(x);
                    poss_period_2.insert(y);
                }
            }
        } else {
            match possible_periods {
                CriticalPointEntry::Single(x) => {
                    poss_period_2.retain(|&val| val == x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_period_2.retain(|&val| val == x || val == y);
                }
            }
        }

        if poss_period_2.is_empty() {
            return false;
        }
    }

    true
}

// From Paper: Subroutine 2B
fn check_irrational_periods(numer: Polynomial<ZiElement<i64>>, denom: Polynomial<ZiElement<i64>>, res: ZiElement<i64>, primes: &[u16], db: &DB) -> bool {
    use std::collections::HashSet;

    let mut poss_per = HashSet::new();
    
    for p in primes.iter() {
        if res.reduce_mod(*p as u32) == Zero::zero() {
            continue;
        }

        // reduce phi mod p
        let reduced_numer = Polynomial::new(
            {
                let mut res = vec![];
                for entry in numer.data() {
                    res.push((*entry).reduce_mod(*p as u32));
                }
                res
            }
        );
        let reduced_denom = Polynomial::new(
            {
                let mut res = vec![];
                for entry in denom.data() {
                    res.push((*entry).reduce_mod(*p as u32));
                }
                res
            }
        );

        // Make sure our map is degree 2 before computing any further
        if reduced_numer.degree() != 2 || reduced_denom.degree() != 2 {
            continue;
        }

        let map = FiniteQuadraticMap {
            numer: reduced_numer,
            denom: reduced_denom,
        };

        let [s1, s2, s3] = map.sigma_invariants();
        let morphism: Morphism = Morphism {
            b: s1.val as u16,
            c: s2.val as u16,
        };
        
        // Look up psi in the database
        let dbentry = db.inner
            .get(p).unwrap()
            .get(&morphism);

        if dbentry.is_none() {
            // Then our map is conjugate to one of lower degree
            // so skip it
            continue;
        }

        let dbentry = dbentry.unwrap();
        
        if poss_per.is_empty() {
            // This is the first good prime
            match dbentry.l1_entry {
                CriticalPointEntry::Single(x) => {
                    poss_per.insert(x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_per.insert(x);
                    poss_per.insert(y);
                }
            }
            match dbentry.l2_entry {
                CriticalPointEntry::Single(x) => {
                    poss_per.retain(|&val| val == x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_per.retain(|&val| val == x || val == y);
                }
            }
        } else {
            // This is not the first good prime
            match dbentry.l1_entry {
                CriticalPointEntry::Single(x) => {
                    poss_per.retain(|&val| val == x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_per.retain(|&val| val == x || val == y);
                }
            }
            match dbentry.l2_entry {
                CriticalPointEntry::Single(x) => {
                    poss_per.retain(|&val| val == x);
                },
                CriticalPointEntry::Double(x, y) => {
                    poss_per.retain(|&val| val == x || val == y);
                }
            }
        }

        if poss_per.is_empty() {
            return false;
        }
    }

    true
}

struct FindPCFMaps<'a, Iter> 
where Iter: Iterator<Item = (QFElement<i64>, QFElement<i64>)>
{
    db: DB,
    primes: Vec<u16>,
    iter: &'a mut Iter,
}

impl<'a, Iter: Iterator<Item = (QFElement<i64>, QFElement<i64>)>> Iterator for FindPCFMaps<'a, Iter> {
    type Item = (Polynomial<ZiElement<i64>>, Polynomial<ZiElement<i64>>);

    // From paper: Algorithm 2
    fn next(&mut self) -> Option<Self::Item> {

        while let Some((sig_1, sig_2)) = self.iter.next() {
            assert!(sig_1.field.c == -1 && sig_2.field.c == -1);

            // Create the rational map. Some intermediary steps to clear denominators
            let two: QFElement<i64> = QFElement::from_parts(2, 0, 1, sig_1.field);
            let b_c: QFElement<i64> = two - sig_1;
            let e: QFElement<i64> = two + sig_1;
            let f: QFElement<i64> = two - sig_1 - sig_2;

            let fac = lcm(lcm(b_c.d, e.d), f.d);

            let a: ZiElement<i64> = ZiElement::from_parts(2 * fac, 0);
            let b_c: ZiElement<i64> = ZiElement::from_parts(b_c.a * fac / b_c.d, b_c.b * fac / b_c.d);
            let d: ZiElement<i64> = ZiElement::from_parts(-fac, 0);
            let e: ZiElement<i64> = ZiElement::from_parts(e.a * fac / e.d, e.b * fac / e.d);
            let f: ZiElement<i64> = ZiElement::from_parts(f.a * fac / f.d, f.b * fac / f.d);

            let numer = Polynomial::new(vec![b_c.clone(), b_c, a]);
            let denom = Polynomial::new(vec![f, e, d]);

            let res = if numer.degree() < denom.degree() {
                resultant(denom.clone(), numer.clone())
            } else {
                resultant(numer.clone(), denom.clone())
            };

            if res == Zero::zero() {
                continue;
            }
            
            let crit_pts = critical_points(numer.clone(), denom.clone());

            let rational_crit_pts: Option<(QFElement<i64>, QFElement<i64>)> = match crit_pts {
                CriticalPoints::Two(crit_1, crit_2) => {
                    // crit_n is a QFElement<ZiElement<i64>> but we just want a QFElement<i64>
                    // but if crit_n.field.c is_square, we can take a square root and
                    // simplify to a QFElement<i64> where c == -1.
                    // TODO: This has the potential for overflow problems! I don't know how to fix
                    // them...
                    match (crit_1.field.c.square_root(), crit_2.field.c.square_root()) {
                        (Some(c1s), Some(c2s)) => {
                            Some((
                                (crit_1.a.inner + crit_1.b.inner * c1s.inner) / crit_1.d.inner,
                                (crit_2.a.inner + crit_2.b.inner * c1s.inner) / crit_2.d.inner,
                            ))
                        },
                        _ => {
                            // At least one of the critical points is irrational
                            None
                        }
                    }
                },
                _ => {
                    None
                }
            };

            // Should we use 2A or 2B?
            match rational_crit_pts {
                Some((crit_1, crit_2)) => {
                    // 2A
                    if check_rational_periods(numer.clone(), denom.clone(), res, &self.primes, &self.db, crit_1, crit_2) {
                        return Some((numer.clone(), denom.clone()));
                    }
                },
                None => {
                    // 2B
                    if check_irrational_periods(numer.clone(), denom.clone(), res, &self.primes, &self.db) {
                        return Some((numer.clone(), denom.clone()));
                    }
                }
            }
        }
        None
    }
}

use std::env::args;
use std::fs::read_to_string;
use anyhow::{Result, bail};

fn main() -> Result<()> {
    let mut args = args();
    if args.len() != 2 {
        bail!("Expected one command line argument for the database file location. Exiting!");
    }

    let dbase_filename = args.nth(1).unwrap();

    let dbase_file_data = read_to_string(dbase_filename)?;
    
    // In the outputed data, there are commas between square brackets
    // We want to change these to &'s.
    let fix_bracketed_commas_re = Regex::new(r"\[([^\]]+),([^\]]+)\]")?;

    let fix_bracketed_commas_data = fix_bracketed_commas_re.replace_all(&dbase_file_data, "[$1 & $2]");

    // Same thing for M(_, _)'s
    let fix_morphism_commas_re = Regex::new(r"\(([^\)]+), ([^\)]+)\)")?;

    let fix_morphism_commas_data = fix_morphism_commas_re.replace_all(&fix_bracketed_commas_data, "($1 & $2)");


    // The data also has blank lines, let's get rid of those
    let dbase_data: String = fix_morphism_commas_data
                        .split('\n')
                        .filter(|line| line.trim().len() != 0)
                        .collect::<Vec<&str>>()
                        .join("\n");
    
    println!("Beginning to parse database...");

    // Finally construct the database
    let mut dbase = DB::from_str(&dbase_data)?;

    // Filter out primes p such that (-1).sqrt() doesn't exist mod p
    dbase.inner.retain(|&p, _val| {
        let p_elt = ModPElt { val: (p - 1) as i64, p: p as u32 };
        !p_elt.sqrt().is_none()
    });
    
    println!("Parsing complete! Running algorithm...");

    // We want the list of primes that are in the database as well
    let mut p_list: Vec<u16> = dbase
            .inner
            .keys()
            .cloned()
            .filter(|val| {
                // 281 was not finished in the data collection
                *val != 281
            })
            .collect();

    p_list.sort();

    // TODO: Write an iterator for "fake bounded height" to give to FindPCFMaps
    // and run FindPCFMaps here

    let mut values = (-100..100)
        .into_iter()
        .map(move |a| {
            (-10..10)
                .into_iter()
                .map(move |b| {
                    (-10..10)
                    .into_iter()
                    .map(move |c| {
                        (-10..10)
                        .into_iter()
                        .map(move |d| {
                            let a = QFElement::from_parts(a, 0, b, QuadraticField::from_c(-1));
                            let b = QFElement::from_parts(c, 0, d, QuadraticField::from_c(-1));
                            (a, b)
                        })
                        .collect::<Vec<_>>()
                    })
                    .flatten()
                })
                .flatten()
        })
        .flatten();

    let pcf_maps = FindPCFMaps {
        db: dbase,
        primes: p_list,
        iter: &mut values,
    };

    for pcf_map in pcf_maps {
        dbg!(pcf_map);
    }

    Ok(())
}
