use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use std::ops::Range;
use std::{env, process};

use crate::cli::Args;

pub enum Error {
    UnknownInstruction,
    InstructionNotImplemented,
    InvalidArgument(usize, String),
    InvalidNumberOfArguments(usize, usize),
    Calculation(String),
}

impl Error {
    fn code(&self) -> i32 {
        match self {
            Self::UnknownInstruction => 1,
            Self::InstructionNotImplemented => 2,
            Self::InvalidArgument(..) => 3,
            Self::InvalidNumberOfArguments(..) => 4,
            Self::Calculation(..) => 5,
        }
    }

    fn title(&self) -> String {
        match self {
            Self::UnknownInstruction => "Unknown instruction".to_string(),
            Self::InstructionNotImplemented => "Instruction not implemented".to_string(),
            Self::InvalidArgument(..) => "Invalid argument".to_string(),
            Self::InvalidNumberOfArguments(expected, actual) => format!(
                "Invalid number of arguments (expected {}, got {})",
                expected, actual
            ),
            Self::Calculation(msg) => msg.to_owned(),
        }
    }

    fn message(&self) -> String {
        match self {
            Self::UnknownInstruction => "This instruction is unknown".to_string(),
            Self::InstructionNotImplemented => "Not implemented".to_string(),
            Self::InvalidArgument(.., msg) => msg.to_string(),
            Self::InvalidNumberOfArguments(expected, actual) => {
                let diff = expected.abs_diff(*actual);

                let word_args = if diff == 1 { "argument" } else { "arguments" };

                if *actual == 0 {
                    "Add --args here".to_string()
                } else if expected > actual {
                    format!("Add {} more {} here", diff, word_args)
                } else {
                    format!("Consider removing {} extra {}", diff, word_args)
                }
            }
            Self::Calculation(..) => "".to_string(),
        }
    }

    fn needle(&self, args: &Args) -> String {
        match self {
            Self::UnknownInstruction => args.instruction.clone(),
            Self::InstructionNotImplemented => args.instruction.clone(),
            Self::InvalidArgument(index, ..) => args.args[*index].clone(),
            Self::InvalidNumberOfArguments(expected, actual) => {
                if expected > actual {
                    match args.args.last() {
                        Some(v) => v.to_string(),
                        None => "".to_string(),
                    }
                } else {
                    let expected = *expected;
                    let actual = *actual;
                    let diff = actual - expected;
                    let mut extra_args: Vec<&str> = Vec::with_capacity(diff);

                    for i in expected..actual {
                        extra_args.push(&args.args[i]);
                    }

                    extra_args.join(" ")
                }
            }
            Self::Calculation(..) => "".to_string(),
        }
    }

    fn label_range(&self, args: &Args, cli: &String) -> Range<usize> {
        if let Self::InvalidNumberOfArguments(expected, actual) = self
            && actual < expected
        {
            return cli.len()..cli.len();
        }

        let needle = self.needle(&args);
        let start_index = cli.find(&needle).unwrap();
        let end_index = start_index + needle.len();

        start_index..end_index
    }

    pub fn print(&self, args: &Args) -> ! {
        if let Self::Calculation(msg) = self {
            self.print_short(msg);
        }

        let cli_args: Vec<String> = env::args().collect();
        let cli_args = cli_args.join(" ");
        let source_name = "Command line arguments";

        Report::build(ReportKind::Error, (source_name, 0..0))
            .with_code(self.code())
            .with_message(self.title())
            .with_label(
                Label::new((source_name, self.label_range(args, &cli_args)))
                    .with_message(self.message().fg(Color::BrightRed))
                    .with_color(Color::BrightRed),
            )
            .finish()
            .print((source_name, Source::from(cli_args)))
            .unwrap();

        process::exit(self.code());
    }

    fn print_short(&self, message: &str) -> ! {
        let prefix = format!("[0{}] Error:", self.code());
        println!("{} {}", prefix.fg(Color::Red), message);
        process::exit(self.code());
    }
}
