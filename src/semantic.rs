mod types;
use crate::syntax::NodeKind;
pub use types::*;

#[derive(Debug)]
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

    pub fn node(&self) -> Option<&NodeKind<'a>> {
        self.node.as_ref()
    }
}
