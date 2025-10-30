use std::cmp::Ordering;

pub trait Pretty {
    fn prettify(&self) -> String;
}

impl Pretty for bool {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl Pretty for usize {
    fn prettify(&self) -> String {
        self.to_string()
    }
}

impl Pretty for Ordering {
    fn prettify(&self) -> String {
        match self {
            Self::Less => "<",
            Self::Equal => "=",
            Self::Greater => ">",
        }
        .to_string()
    }
}
