use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about = "astraea - Computer algebra system")]
pub struct Args {
    /// Instruction to be called.
    #[arg(short, long)]
    pub instruction: String,

    /// Parameters of the instruction.
    #[arg(short, long, num_args = 1.., allow_hyphen_values = true)]
    pub args: Vec<String>,
}
