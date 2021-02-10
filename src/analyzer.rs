use super::parser;
use super::sem;
use parser::Expr;

pub struct Semantic {}

impl Semantic {
    pub fn new() -> Semantic {
        Semantic {}
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        module.name = Some("main".to_string());

        if let Some(ref mut expr) = module.expr {
            self.analyze_expr(expr);
        }
    }

    fn analyze_expr(&mut self, node: &mut parser::Node) {
        match &node.expr {
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
            Expr::Add(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::String);
            }
            Expr::Sub(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::String);
            }
            Expr::Mul(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::String);
            }
            Expr::Div(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::String);
            }
            // relation
            Expr::LT(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::GT(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::LE(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::GE(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::EQ(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::NE(lhs, rhs) => {
                expect_type(lhs, sem::Type::Int32);
                expect_type(rhs, sem::Type::Int32);
                node.r#type = Some(sem::Type::Boolean);
            }
            Expr::If {
                condition,
                then_body,
                else_body,
            } => {
                expect_type(condition, sem::Type::Boolean);
                match else_body {
                    Some(else_body) => {
                        if then_body.r#type != else_body.r#type {
                            panic!("Type mismatch between `then` and `else`")
                        }
                    }
                    None => {
                        node.r#type = then_body.r#type;
                    }
                }
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

/*
impl Semantic {
    pub fn new() -> Semantic {
        Semantic {
            functions: vec![],
            locals: vec![],
        }
    }

    pub fn analyze(module: parser::Module) -> Semantic {
        let mut sem = Semantic::new();

        sem.analyze_module(&module);
        sem
    }

    fn analyze_module(&mut self, module: &parser::Module) {
        if let Some(definition) = module.definition {
            self.analyze_definition(definition);
        }
    }

    fn analyze_definition(&mut self, definition: &Definition) {
        match definition {
            Definition::Function { name, params, body } => {
                // Register function definition
                let typed_params = params
                    .iter()
                    .map(|x| sem::Binding {
                        name: x.clone(),
                        r#type: sem::Type::Int32,
                    })
                    .collect();

                self.functions.push(sem::Function {
                    name: name.clone(),
                    reference_name: format!("${}", name),
                    params: typed_params,
                });

                // Initialize local variables with parameters.
                //self.locals.extend(typed_params);

                //self.locals.clear();
            }
        }
    }
}

 */
