use clap::{App, Arg};
use io::Read;
use std::array;
use std::fmt;
use std::fs;
use std::io;
use std::iter::ExactSizeIterator;
use std::str::FromStr;

use super::backend_2021_spring;
use super::backend_2021_summer;
use super::CompilerError;

#[derive(Debug, Clone, Copy)]
pub enum CompilerBackend {
    Nico2021Spring,
    Nico2021Summer,
}

impl CompilerBackend {
    pub fn variants() -> impl Iterator<Item = CompilerBackend> {
        array::IntoIter::new([Self::Nico2021Spring, Self::Nico2021Summer])
    }
}

impl fmt::Display for CompilerBackend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompilerBackend::Nico2021Spring => write!(f, "2021-spring"),
            CompilerBackend::Nico2021Summer => write!(f, "2021-summer"),
        }
    }
}

impl FromStr for CompilerBackend {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::variants()
            .find(|x| x.to_string() == s)
            .ok_or_else(|| format!("Unknown backend option: `{}`", s))
    }
}

#[derive(Debug)]
pub struct CompilerOptions {
    backend: CompilerBackend,
    filepath: Option<String>,
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            backend: CompilerBackend::Nico2021Spring,
            filepath: None,
        }
    }
}

impl CompilerOptions {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(Debug, Default)]
pub struct Command {}

impl Command {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(
        &self,
        args: impl ExactSizeIterator<Item = String>,
    ) -> Result<String, CompilerError> {
        let options = parse_options(args)?;

        let src = if let Some(filepath) = options.filepath {
            read_from_file(filepath.as_str())?
        } else {
            read_from_stdin()?
        };

        match options.backend {
            CompilerBackend::Nico2021Spring => backend_2021_spring::compile(src),
            CompilerBackend::Nico2021Summer => backend_2021_summer::compile(src),
        }
    }
}

fn parse_options(
    args: impl ExactSizeIterator<Item = String>,
) -> Result<CompilerOptions, CompilerError> {
    let mut options = CompilerOptions::new();

    // TODO: remove intermediate string object
    let backend_possible_values = CompilerBackend::variants()
        .map(|b| b.to_string())
        .collect::<Vec<_>>();
    let backend_possible_values: Vec<&str> =
        backend_possible_values.iter().map(AsRef::as_ref).collect();

    let matches = App::new("nico")
        .arg(
            Arg::with_name("backend")
                .long("backend")
                .takes_value(true)
                .possible_values(&backend_possible_values),
        )
        .arg(
            Arg::with_name("INPUT")
                .help("Sets the input file to use")
                .required(false)
                .index(1),
        )
        .get_matches_from(args);

    if let Some(backend) = matches.value_of("backend") {
        options.backend = backend.parse::<CompilerBackend>()?;
    }

    if let Some(filepath) = matches.value_of("INPUT") {
        options.filepath = Some(filepath.to_string());
    }

    Ok(options)
}

fn read_from_stdin() -> Result<String, io::Error> {
    let mut content = String::new();

    io::stdin().read_to_string(&mut content)?;

    Ok(content)
}

fn read_from_file(filename: &str) -> io::Result<String> {
    fs::read_to_string(filename)
}
