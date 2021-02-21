/// Generates a unique string while continuously incrementing the index internally.
/// The user can specify a prefix for the generated string.
#[derive(Debug)]
pub struct SequenceNaming {
    type_var_index: usize,
    prefix: String,
}

impl SequenceNaming {
    pub fn new(prefix: &str) -> Self {
        Self {
            type_var_index: 0,
            prefix: prefix.to_string(),
        }
    }

    pub fn next(&mut self) -> String {
        let i = self.type_var_index;
        self.type_var_index += 1;
        format!("{}{}", self.prefix, i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sequence_naming() {
        let mut naming = SequenceNaming::new("my_");

        assert_eq!(naming.next(), "my_0".to_string());
        assert_eq!(naming.next(), "my_1".to_string());
    }
}
