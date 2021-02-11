use super::parser;
use super::sem;
use parser::Expr;

pub struct Semantic {
    functions: Vec<sem::Binding>,
    type_variable_index: i32,
}

impl Semantic {
    pub fn new() -> Semantic {
        Semantic {
            functions: vec![],
            type_variable_index: 0,
        }
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        module.name = Some("main".to_string());
        self.functions = vec![];

        if let Some(ref mut function) = module.function {
            self.analyze_function(function);
        }
        if let Some(ref mut expr) = module.expr {
            self.analyze_expr(expr);
        }
    }

    fn new_type_variable(&mut self) -> sem::Type {
        self.type_variable_index += 1;
        sem::Type::TypeVariable {
            name: format!("${}", self.type_variable_index),
            instance: None,
        }
    }

    fn function_signature(&mut self, function: &parser::Function) -> sem::Binding {
        let params = function
            .params
            .iter()
            .map(|_p| self.new_type_variable())
            .collect();

        sem::Binding {
            name: function.name.clone(),
            r#type: sem::Type::Function {
                params,
                return_type: Box::new(self.new_type_variable()),
            },
        }
    }

    fn analyze_function(&mut self, function: &mut parser::Function) {
        let f = self.function_signature(function);
        self.functions.push(f);

        self.analyze_expr(&mut function.body);
    }

    fn analyze_expr(&mut self, node: &mut parser::Node) {
        match node.expr {
            Expr::Integer(_) => {
                node.r#type = Some(sem::Type::Int32);
            }
            Expr::String(_) => {
                node.r#type = Some(sem::Type::String);
            }
            Expr::Identifier(_) => panic!("not implemented yet."),
            Expr::Invocation {
                name: _,
                arguments: _,
            } => panic!("not implemented yet."),
            // binop
            Expr::Add(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Int32);
            }
            Expr::Sub(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Int32);
            }
            Expr::Mul(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Int32);
            }
            Expr::Div(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Int32);
            }
            // relation
            Expr::LT(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::GT(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::LE(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::GE(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::EQ(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::NE(ref mut lhs, ref mut rhs) => {
                self.analyze_expr(lhs);
                self.analyze_expr(rhs);

                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::If {
                ref mut condition,
                ref mut then_body,
                ref mut else_body,
            } => {
                self.analyze_expr(condition);
                self.analyze_expr(then_body);

                expect_type(condition, sem::Type::Boolean);

                if let Some(else_body) = else_body {
                    self.analyze_expr(else_body);
                    if then_body.r#type != else_body.r#type {
                        panic!("Type mismatch between `then` and `else`")
                    }
                }

                //node.r#type = then_body.r#type;
            }
        }
    }
}

impl Default for Semantic {
    fn default() -> Self {
        Semantic::new()
    }
}

fn expect_type(node: &parser::Node, expected_type: sem::Type) {
    match &node.r#type {
        Some(ty) if *ty == expected_type => {}
        Some(ty) => panic!("Expected {:?}, but was {:?}", expected_type, ty),
        None => panic!("Type can't be inferred."),
    };
}
#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use parser;

    #[test]
    fn number_integer() {
        let mut module = parser::parse_string("42");
        let mut semantic = Semantic::new();

        semantic.analyze(&mut module);

        let node = module.expr.unwrap();
        assert_matches!(node.r#type, Some(sem::Type::Int32));
    }

    #[test]
    fn add_operation() {
        let mut module = parser::parse_string("1 + 2");
        let mut semantic = Semantic::new();

        semantic.analyze(&mut module);

        let node = module.expr.unwrap();
        assert_matches!(node.expr, Expr::Add(lhs, rhs) => {
            assert_matches!(lhs.r#type, Some(sem::Type::Int32));
            assert_matches!(rhs.r#type, Some(sem::Type::Int32));
        });
    }
}
