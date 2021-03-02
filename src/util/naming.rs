use std::collections::HashMap;

/// Generates a unique string while continuously incrementing the index internally.
/// The user can specify a prefix for the generated string.
#[derive(Debug, Default)]
pub struct SequenceNaming {
    names: HashMap<String, i32>,
}

impl SequenceNaming {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn next<S: AsRef<str>>(&mut self, name: S) -> String {
        let name = name.as_ref();
        let n = self.names.entry(name.to_string()).or_insert(0);
        let next = format!("{}.{}", name, n);

        *n += 1;
        next
    }
}

/// This struct produces a unique name while giving a sequential
/// number to the name passed to the next() method.
#[derive(Debug)]
pub struct PrefixNaming {
    type_var_index: usize,
    prefix: String,
}

impl PrefixNaming {
    pub fn new(prefix: &str) -> Self {
        Self {
            type_var_index: 0,
            prefix: prefix.to_string(),
        }
    }

    pub fn next(&mut self) -> String {
        let i = self.type_var_index;
        let next = format!("{}{}", self.prefix, i);

        self.type_var_index += 1;
        next
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_naming() {
        let mut naming = PrefixNaming::new("my_");

        assert_eq!(naming.next(), "my_0".to_string());
        assert_eq!(naming.next(), "my_1".to_string());
    }

    #[test]
    fn sequence_naming() {
        let mut naming = SequenceNaming::new();

        assert_eq!(naming.next("x"), "x.0".to_string());
        assert_eq!(naming.next("x"), "x.1".to_string());
        assert_eq!(naming.next("y"), "y.0".to_string());
    }
}
