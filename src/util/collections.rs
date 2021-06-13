use crate::arena::BumpaloVec;
use std::cell::Ref;

#[derive(Debug)]
pub struct RefVecIter<'r, 'arena, T> {
    vec: Ref<'r, BumpaloVec<'arena, T>>,
}

impl<'r, 'arena, T> RefVecIter<'r, 'arena, T> {
    pub fn new(vec: Ref<'r, BumpaloVec<'arena, T>>) -> Self {
        Self { vec }
    }
}

impl<'a: 'r, 'r, 'arena, T> IntoIterator for &'a RefVecIter<'r, 'arena, T> {
    type IntoIter = std::slice::Iter<'r, T>;
    type Item = &'r T;

    fn into_iter(self) -> Self::IntoIter {
        self.vec.iter()
    }
}
