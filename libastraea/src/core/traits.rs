pub trait Pretty {
    fn prettify(&self) -> String;
}

impl Pretty for bool {
    fn prettify(&self) -> String {
        self.to_string()
    }
}
