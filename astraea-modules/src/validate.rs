use astraea::algebra::Field;
use astraea::digit::Digit;
use astraea::natural::Natural;
use astraea::polynomial::Polynomial;
use astraea::rational::Rational;
use std::{fmt::Display, str::FromStr};

#[derive(Debug)]
pub enum InstructionErrorReason {
    Instruction,
    Argument(usize),
    ArgumentsCount(usize, usize),
    Calculation(usize),
}

#[derive(Debug)]
pub struct InstructionError {
    pub message: String,
    pub reason: InstructionErrorReason,
}

impl InstructionError {
    pub fn new<S: Into<String>>(message: S, reason: InstructionErrorReason) -> Self {
        Self {
            reason,
            message: message.into(),
        }
    }

    pub fn unknown_instruction<S: Into<String>>(instruction: S) -> Self {
        Self {
            message: format!("unknown instruction: \"{}\"", instruction.into()),
            reason: InstructionErrorReason::Instruction,
        }
    }

    pub fn calculation<S: Into<String>>(caused_by_arg: usize, message: S) -> Self {
        Self {
            message: message.into(),
            reason: InstructionErrorReason::Calculation(caused_by_arg),
        }
    }

    pub fn invalid_arg<S: Into<String>>(message: S, arg_index: usize) -> Self {
        Self {
            message: message.into(),
            reason: InstructionErrorReason::Argument(arg_index),
        }
    }

    pub fn count(expected: usize, got: usize) -> Self {
        let args_word = if expected == 1 { "arg" } else { "args" };
        let message = format!("expected {} {}, got {}", expected, args_word, got);

        Self {
            message,
            reason: InstructionErrorReason::ArgumentsCount(expected, got),
        }
    }
}

impl Display for InstructionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// Ensures number of arguments provided to the instruction call.
pub fn ensure_args_count(args: &Vec<String>, expected: usize) -> Result<(), InstructionError> {
    if args.len() != expected {
        return Err(InstructionError::count(expected, args.len()));
    }

    Ok(())
}

/// Parses arguments provided to the particular instruction and ensures their validity.
pub fn ensure_args<T>(args: Vec<String>, count: usize) -> Result<Vec<T>, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    ensure_args_count(&args, count)?;

    let mut res = Vec::with_capacity(count);

    for i in 0..count {
        let arg = match T::from_str(&args[i]) {
            Ok(v) => v,
            Err(e) => {
                return Err(InstructionError::invalid_arg(e.to_string(), i));
            }
        };

        res.push(arg);
    }

    Ok(res)
}

/// Parses argument at the specified index as usize.
pub fn get_usize(args: &Vec<String>, arg_index: usize) -> Result<usize, InstructionError> {
    let v = &args[arg_index];
    usize::from_str(v).or_else(|_| {
        Err(InstructionError::invalid_arg(
            format!("cannot convert \"{}\" to usize", v),
            arg_index,
        ))
    })
}

/// Parses argument at the specified index as Digit.
pub fn get_digit(args: &Vec<String>, arg_index: usize) -> Result<Digit, InstructionError> {
    Digit::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as Natural.
pub fn get_natural(args: &Vec<String>, arg_index: usize) -> Result<Natural, InstructionError> {
    Natural::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as Rational.
pub fn get_rational(args: &Vec<String>, arg_index: usize) -> Result<Rational, InstructionError> {
    Rational::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Parses argument at the specified index as Polynomial.
pub fn get_polynomial<T: Field>(
    args: &Vec<String>,
    arg_index: usize,
) -> Result<Polynomial<T>, InstructionError> {
    Polynomial::from_str(&args[arg_index])
        .or_else(|e| Err(InstructionError::invalid_arg(e.message, arg_index)))
}

/// Ensures 1 argument was provided and parses it to the corresponding type.
pub fn one_arg<T>(args: Vec<String>) -> Result<T, InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(args, 1)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();

    Ok(first)
}

/// Ensures 2 arguments was provided and parses them to the corresponding type.
pub fn two_args<T>(args: Vec<String>) -> Result<(T, T), InstructionError>
where
    T: FromStr,
    T::Err: Display,
{
    let args = ensure_args(args, 2)?;
    let mut args_iter = args.into_iter();
    let first = args_iter.next().unwrap();
    let second = args_iter.next().unwrap();

    Ok((first, second))
}

/// Ensures that natural number can be converted into usize.
pub fn natural_can_cast_to_usize(
    n: Natural,
    arg_index: usize,
) -> Result<Natural, InstructionError> {
    match TryInto::<usize>::try_into(n) {
        Ok(v) => Ok(Natural::from(v)),
        Err(..) => Err(InstructionError::invalid_arg(
            "must not exceed usize",
            arg_index,
        )),
    }
}

#[cfg(test)]
mod tests {
    use astraea::{formatting::Pretty, integer::Integer};

    use super::*;

    #[test]
    fn test_ensure_args_count() {
        assert!(ensure_args_count(&vec!["".to_string(); 1], 1).is_ok());
        assert!(ensure_args_count(&vec!["".to_string(); 2], 2).is_ok());
        assert!(ensure_args_count(&vec!["".to_string(); 1], 2).is_err());
    }

    #[test]
    fn test_ensure_args() {
        let args = ensure_args::<Integer>(vec!["234".to_string(), "-5653".to_string()], 2).unwrap();
        assert_eq!(args[0], Integer::from(234));
        assert_eq!(args[1], Integer::from(-5653));

        assert!(ensure_args::<Integer>(vec!["234".to_string(), "aaaa".to_string()], 2).is_err());
        assert!(ensure_args::<Integer>(vec!["234".to_string(), "-5653".to_string()], 3).is_err());
    }

    #[test]
    fn test_get_usize() {
        let actual = get_usize(&vec!["34".to_string()], 0).unwrap();
        assert_eq!(actual, 34usize);
        assert!(get_usize(&vec!["34".to_string(), "a".to_string()], 1).is_err());
    }

    #[test]
    fn test_get_digit() {
        let actual = get_digit(&vec!["9".to_string()], 0).unwrap();
        assert_eq!(actual, Digit::Nine);
        assert!(get_digit(&vec!["99".to_string()], 0).is_err());
    }

    #[test]
    fn test_get_natural() {
        let actual = get_natural(&vec!["51".to_string()], 0).unwrap();
        assert_eq!(actual, Natural::from(51u8));
        assert!(get_natural(&vec!["-11".to_string()], 0).is_err());
        assert!(get_natural(&vec!["a".to_string()], 0).is_err());
    }

    #[test]
    fn test_get_rational() {
        let actual = get_rational(&vec!["7/5".to_string()], 0).unwrap();
        assert_eq!(
            actual,
            Rational::new(Integer::from(7), Natural::from(5u8)).unwrap()
        );
        assert!(get_rational(&vec!["8/0".to_string()], 0).is_err());
        assert!(get_rational(&vec!["sadkfsjafokdjh".to_string()], 0).is_err());
    }

    #[test]
    fn test_get_polynomial() {
        let actual: Polynomial<Rational> = get_polynomial(&vec!["7x+1".to_string()], 0).unwrap();
        assert_eq!(actual.prettify(), "7x + 1");
        assert!(get_rational(&vec!["x^hfjwhf".to_string()], 0).is_err());
    }

    #[test]
    fn test_one_arg() {
        let actual: Natural = one_arg(vec!["12321".into()]).unwrap();
        assert_eq!(actual, Natural::from(12321u16));
        assert!(one_arg::<Rational>(vec![]).is_err());
        assert!(one_arg::<Rational>(vec!["24".into(), "11".into()]).is_err());
    }

    #[test]
    fn test_two_args() {
        let (actual_first, actual_second) =
            two_args::<Integer>(vec!["-1234".into(), "5678".into()]).unwrap();
        assert_eq!(actual_first, Integer::from(-1234));
        assert_eq!(actual_second, Integer::from(5678));
        assert!(two_args::<Integer>(vec![]).is_err());
        assert!(two_args::<Integer>(vec!["24".into()]).is_err());
        assert!(two_args::<Integer>(vec!["24".into(), "17".into(), "-324234".into()]).is_err());
    }
}
