use ariadne::{Color, Fmt, Label, Report, ReportKind, Source};
use std::ops::Range;
use std::{env, process};

use crate::cli::Args;

pub enum Error {
    UnknownInstruction,
    InstructionNotImplemented,
    InvalidArgument(usize, String),
    InvalidNumberOfArguments(usize, usize),
    Calculation(usize, String),
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
            Self::Calculation(.., msg) => msg.to_owned(),
        }
    }

    fn message(&self) -> String {
        match self {
            Self::UnknownInstruction => "This instruction is unknown".to_string(),
            Self::InstructionNotImplemented => "Not implemented".to_string(),
            Self::InvalidArgument(.., msg) => {
                let message = msg.to_string();
                let mut chars: Vec<char> = message.chars().collect();
                chars[0] = chars[0].to_uppercase().nth(0).unwrap();

                chars.into_iter().collect()
            }
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
            Self::Calculation(..) => "Caused by this argument".to_string(),
        }
    }

    fn needle(&self, args: &Args) -> String {
        match self {
            Self::UnknownInstruction => args.instruction.to_string(),
            Self::InstructionNotImplemented => args.instruction.to_string(),
            Self::InvalidArgument(index, ..) | Self::Calculation(index, ..) => {
                args.args[*index].clone()
            }
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
        }
    }

    fn label_range(&self, args: &Args, cli: &String) -> Range<usize> {
        if let Self::InvalidNumberOfArguments(expected, actual) = self {
            let chars_count = cli.chars().count();

            if actual < expected {
                return chars_count..chars_count;
            }

            let mut diff = actual - expected;
            let mut offset = diff - 1;
            let mut cli_args: Vec<String> = env::args().collect();

            while diff > 0 {
                let last_arg = match cli_args.pop() {
                    Some(v) => v,
                    None => break,
                };

                offset += last_arg.chars().count();
                diff -= 1;
            }

            return chars_count - offset..chars_count;
        }

        let needle = self.needle(&args);
        let start_index = cli.find(&needle).unwrap();
        let end_index = start_index + needle.chars().count();

        start_index..end_index
    }

    pub fn print(&self, args: &Args) -> ! {
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
}
