use crate::semantic::{StructType, TypeKind};
use std::fmt::Display;

pub fn code_fence<T: Display>(content: T) -> String {
    format!("```nico\n{}\n```", content)
}

pub fn format_type<T: Display>(ty: Option<T>) -> String {
    ty.map_or("{{unknown}}".to_string(), |x| x.to_string())
}

pub fn describe_type(ty: TypeKind<'_>) -> String {
    let description = match ty {
        TypeKind::Int32 => "The 32-bit signed integer type.",
        TypeKind::Boolean => "The boolean type.",
        _ => "",
    };
    format!("{}\n---\n{}", code_fence(ty), description)
}

pub fn describe_struct_field<'a>(struct_type: &'a StructType<'a>, field_name: &str) -> String {
    let ty = struct_type.get_field_type(field_name);

    code_fence(format!(
        "{}.{}: {}",
        struct_type.name(),
        field_name,
        format_type(ty),
    ))
}
