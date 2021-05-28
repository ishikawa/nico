use super::{EffectiveRange, MissingTokenKind, Node, NodeKind, SyntaxToken, Token};
use crate::arena::{BumpaloArena, BumpaloVec};
use std::{collections::VecDeque, slice};

#[derive(Debug)]
pub struct Code<'a> {
    code: BumpaloVec<'a, CodeKind<'a>>,
}

impl<'a> Code<'a> {
    pub fn new(code: BumpaloVec<'a, CodeKind<'a>>) -> Self {
        Self { code }
    }

    pub fn iter(&self) -> CodeKindIter<'_, 'a> {
        CodeKindIter::from(self.code.iter())
    }
}

#[derive(Debug)]
pub enum CodeKind<'a> {
    Node(NodeKind<'a>),
    SyntaxToken(SyntaxToken),
}

impl CodeKind<'_> {
    pub fn range(&self) -> EffectiveRange {
        match self {
            CodeKind::Node(kind) => kind.range(),
            CodeKind::SyntaxToken(token) => token.range(),
        }
    }

    pub fn interpreted(token: Token) -> Self {
        CodeKind::SyntaxToken(SyntaxToken::Interpreted(token))
    }
}

#[derive(Debug, Default)]
pub struct CodeBuilder<'code> {
    buffer: VecDeque<CodeKind<'code>>,
}

impl<'code> CodeBuilder<'code> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn node(&mut self, node: NodeKind<'code>) -> &mut Self {
        self.buffer.push_back(CodeKind::Node(node));
        self
    }

    pub fn interpret(&mut self, token: Token) -> &mut Self {
        self.buffer.push_back(CodeKind::interpreted(token));
        self
    }

    pub fn missing(&mut self, range: EffectiveRange, item: MissingTokenKind) -> &mut Self {
        self.buffer
            .push_back(CodeKind::SyntaxToken(SyntaxToken::Missing { range, item }));
        self
    }

    pub fn skip(&mut self, token: Token, expected: MissingTokenKind) -> &mut Self {
        self.buffer
            .push_back(CodeKind::SyntaxToken(SyntaxToken::Skipped {
                token,
                expected,
            }));
        self
    }

    pub fn build(&mut self, arena: &'code BumpaloArena) -> Code<'code> {
        let mut vec = BumpaloVec::with_capacity_in(self.buffer.len(), arena);

        while let Some(kind) = self.buffer.pop_front() {
            vec.push(kind);
        }

        Code::new(vec)
    }
}

#[derive(Debug)]
pub struct CodeKindIter<'a, 'code> {
    inner: CodeKindIterInner<'a, 'code>,
}

#[derive(Debug)]
enum CodeKindIterInner<'a, 'code> {
    Once(Option<&'a CodeKind<'code>>),
    Slice(slice::Iter<'a, CodeKind<'code>>),
}

impl CodeKindIter<'_, '_> {
    // Move this into ExactSizeIterator, when its is_empty()
    // coming in stable version.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a, 'code> From<&'a CodeKind<'code>> for CodeKindIter<'a, 'code> {
    fn from(kind: &'a CodeKind<'code>) -> Self {
        Self {
            inner: CodeKindIterInner::Once(Some(kind)),
        }
    }
}

impl<'a, 'code> From<slice::Iter<'a, CodeKind<'code>>> for CodeKindIter<'a, 'code> {
    fn from(iter: slice::Iter<'a, CodeKind<'code>>) -> Self {
        Self {
            inner: CodeKindIterInner::Slice(iter),
        }
    }
}

impl<'a, 'code> Iterator for CodeKindIter<'a, 'code> {
    type Item = &'a CodeKind<'code>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            CodeKindIterInner::Once(kind) => kind.take(),
            CodeKindIterInner::Slice(it) => it.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            CodeKindIterInner::Once(kind) => {
                if kind.is_some() {
                    (1, Some(1))
                } else {
                    (0, Some(0))
                }
            }
            CodeKindIterInner::Slice(it) => it.size_hint(),
        }
    }
}

impl<'a, 'code> ExactSizeIterator for CodeKindIter<'a, 'code> {}

impl<'a, 'code> DoubleEndedIterator for CodeKindIter<'a, 'code> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            CodeKindIterInner::Once(_) => self.next(),
            CodeKindIterInner::Slice(it) => it.next_back(),
        }
    }
}
