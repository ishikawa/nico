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
        self.type_var_index += 1;
        format!("{}{}", self.prefix, i)
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
}
