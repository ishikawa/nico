use super::parser;

pub struct Semantic {}

impl Semantic {
    pub fn new() -> Semantic {
        Semantic {}
    }

    pub fn analyze(&mut self, module: &mut parser::Module) {
        module.name = Some("main".to_string());
    }
}

impl Default for Semantic {
    fn default() -> Self {
        Semantic::new()
    }
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
