use crate::semantic::{StructType, TypeKind};
use crate::syntax::{self, VariablePattern};
use std::fmt::Display;

pub fn code_fence<T: Display>(content: T) -> String {
    format!("```nico\n{}\n```", content)
}

fn format_type_specifier(ty: Option<TypeKind<'_>>) -> String {
    ty.map_or("{{unknown}}".to_string(), |x| x.type_specifier())
}

/// "struct A"
pub fn format_struct_type_phrase(ty: &StructType<'_>) -> String {
    format!("struct {}", ty.name())
}

pub fn format_struct_field(struct_type: &StructType<'_>, field_name: &str) -> String {
    let ty = struct_type.get_field_type(field_name);

    code_fence(format!(
        "{}.{}: {}",
        struct_type.name(),
        field_name,
        format_type_specifier(ty),
    ))
}

pub fn format_local_variable(pattern: &VariablePattern<'_>) -> String {
    format!(
        "let {}: {}",
        pattern.name(),
        format_type_specifier(Some(pattern.r#type()))
    )
}

pub fn format_function_parameter(param: &syntax::FunctionParameter<'_>) -> String {
    format!(
        "(parameter) {}: {}",
        param.name().as_str(),
        format_type_specifier(Some(param.r#type()))
    )
}

pub fn describe_type(ty: TypeKind<'_>) -> String {
    let description = match ty.terminal_type() {
        TypeKind::Int32 => "The 32-bit signed integer type.",
        TypeKind::Boolean => "The boolean type.",
        _ => "",
    };
    format!("{}\n---\n{}", code_fence(ty), description)
}
