
#![allow(unused, dead_code)]

use std::str::FromStr;
use std::num::ParseIntError;
extern crate anyhow;
use anyhow::Error;
use anyhow::Context;

mod sigma_invariants;

// use num_field_quad::*;

#[derive(Clone, Copy, Debug)]
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
    
    // Finally construct the database
    let dbase = DB::from_str(&dbase_data)?;

    // We want the list of primes that are in the database as well
    let p_list: Vec<u16> = dbase
            .inner
            .keys()
            .cloned()
            .collect();

    dbg!(p_list);
    dbg!(dbase);

    Ok(())
}
