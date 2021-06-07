use crate::semantic::{StructType, Type, TypeKind};
use crate::syntax::{self, VariablePattern};
use std::fmt::Display;

pub fn code_fence<T: Display>(content: T) -> String {
    format!("```nico\n{}\n```", content)
}

fn format_type_specifier(ty: Option<TypeKind<'_>>) -> String {
    ty.map(|ty| ty.prune())
        .map_or("{{unknown}}".to_string(), |x| x.type_specifier())
}

pub fn format_struct_field<'a>(struct_type: &'a StructType<'a>, field_name: &str) -> String {
    let ty = struct_type.get_field_type(field_name);

    code_fence(format!(
        "{}.{}: {}",
        struct_type.name(),
        field_name,
        format_type_specifier(ty),
    ))
}

pub fn format_local_variable<'a>(pattern: &'a VariablePattern<'a>) -> String {
    format!(
        "let {}: {}",
        pattern.name(),
        format_type_specifier(Some(pattern.r#type()))
    )
}

pub fn format_function_parameter<'a>(param: &'a syntax::FunctionParameter<'a>) -> String {
    format!(
        "(parameter) {}: {}",
        param.name().as_str(),
        format_type_specifier(Some(param.r#type()))
    )
}

pub fn describe_type(ty: TypeKind<'_>) -> String {
    let description = match ty {
        TypeKind::Int32 => "The 32-bit signed integer type.",
        TypeKind::Boolean => "The boolean type.",
        _ => "",
    };
    format!("{}\n---\n{}", code_fence(ty), description)
}
