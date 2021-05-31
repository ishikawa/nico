mod types;
use crate::syntax::NodeKind;
pub use types::*;

#[derive(Debug, Clone)]
pub struct SemanticValue<'a> {
    r#type: TypeKind<'a>,
    node: Option<NodeKind<'a>>,
}

impl<'a> SemanticValue<'a> {
    pub fn new(r#type: TypeKind<'a>, node: Option<NodeKind<'a>>) -> Self {
        Self { r#type, node }
    }

    pub fn r#type(&self) -> TypeKind<'a> {
        self.r#type
    }

    pub fn node(&self) -> Option<NodeKind<'a>> {
        self.node
    }

    pub fn is_builtin(&self) -> bool {
        self.node.is_none()
    }

    pub fn is_function_parameter(&self) -> bool {
        self.node()
            .filter(NodeKind::is_function_parameter)
            .is_some()
    }

    pub fn is_variable_pattern(&self) -> bool {
        self.node().filter(NodeKind::is_variable_pattern).is_some()
    }
}
