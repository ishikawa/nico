use crate::arena::BumpaloArena;
use crate::syntax::{self, CallExpression, Node, NodePath, Position, Program};
use crate::unwrap_or_return;
use lsp_types::{ParameterInformation, ParameterLabel, SignatureHelp, SignatureInformation};
use std::convert::TryFrom;

#[derive(Debug)]
pub struct SignatureHelpOperation<'a> {
    arena: &'a BumpaloArena,
    position: Position,
    result: Option<SignatureHelp>,
}

impl<'a> SignatureHelpOperation<'a> {
    pub fn new(arena: &'a BumpaloArena, position: Position) -> Self {
        Self {
            arena,
            position,
            result: None,
        }
    }

    pub fn help(&mut self, program: &'a Program<'a>) -> Option<SignatureHelp> {
        syntax::traverse(self.arena, self, program);
        self.result.take()
    }
}

impl<'a> syntax::Visitor<'a> for SignatureHelpOperation<'a> {
    fn enter_call_expression(&mut self, path: &'a NodePath<'a>, call_expr: &'a CallExpression<'a>) {
        if call_expr.range().contains(self.position) {
            path.stop();
        } else {
            return;
        }

        //fn traverse(arena: &Bump, visitor: &mut dyn Visitor, program: &Program)
        let function_type = unwrap_or_return!(call_expr.callee_type());

        // The label of this signature.
        let mut label = String::new();
        let mut param_signatures = vec![];

        label.push_str("fun ");
        label.push_str(function_type.name());
        label.push_str("(");

        let mut it = function_type.parameters().peekable();

        while let Some(param) = it.next() {
            let param_start = u32::try_from(label.len()).unwrap();

            label.push_str(&format!("{}", param));

            let param_end = u32::try_from(label.len()).unwrap();

            param_signatures.push(ParameterInformation {
                label: ParameterLabel::LabelOffsets([param_start, param_end]),
                documentation: None,
            });

            if it.peek().is_some() {
                label.push_str(", ");
            }
        }
        label.push_str(")");

        let info = SignatureInformation {
            label,
            parameters: Some(param_signatures),
            documentation: None,
            active_parameter: None,
        };

        let help = SignatureHelp {
            signatures: vec![info],
            active_signature: Some(0),
            active_parameter: Some(0),
        };

        self.result.replace(help);
    }
}
