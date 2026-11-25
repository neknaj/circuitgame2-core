//! 十進リテラル、組み込みの算術と明示変換、型注釈からなる整数式を扱う。

use core::ops::Range;
use alloc::vec::Vec;
use crate::syntax::{self, AtomKind, Form};
use super::forms::{is_spelling, source_word, subtree_end};
#[cfg(verus_only)]
use super::forms::{spelling, subtree_limit};
use super::integers::{
    IntegerLiteralError, IntegerOperation, IntegerType, IntegerValue,
    evaluate_int, evaluate_nat, int_to_nat, nat_to_int, read_integer_literal,
};
#[cfg(verus_only)]
use crate::syntax::{form_span, form_spans_valid, sexpr_form_model, strict_syntax_rejection, well_formed_sexpr};
#[cfg(verus_only)]
use super::integers::{
    arithmetic_value, int_result_matches, integer_literal_matches, nat_result_matches,
};
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {

/// 整数式の検査を通過できなかった理由。
#[derive(Debug, Eq, PartialEq)]
pub enum IntegerCheckError {
    /// 共通の字句または S 式解析の違反。
    Syntax(syntax::Error),
    /// この入口で検査する単一の整数式の形に該当しない。
    UnsupportedExpression(Range<usize>),
    /// 式の型が期待型に合わない。範囲は原因の式を指す。
    TypeMismatch {
        /// 元ソース上の半開バイト範囲。
        span: Range<usize>,
        /// 式に要求された整数型。
        expected: IntegerType,
        /// 式に書かれている整数型。
        actual: IntegerType,
    },
    /// リテラルの値が指定された型に収まらない。
    LiteralOutOfRange {
        /// 元ソース上のリテラルの半開バイト範囲。
        span: Range<usize>,
        /// リテラルの整数型。
        ty: IntegerType,
    },
}

/// 検査済みの式を評価した結果が整数型の範囲を越えたことを表す。
#[derive(Debug, Eq, PartialEq)]
pub struct IntegerEvaluationError {
    /// 元ソース上の式全体の半開バイト範囲。
    pub span: Range<usize>,
    /// 演算または変換の結果の型。
    pub ty: IntegerType,
}

#[derive(Clone, Copy)]
struct Literal {
    index: usize,
    negative: bool,
}

#[derive(Clone, Copy)]
enum Builtin {
    Arithmetic(IntegerOperation),
    Convert(IntegerType),
    Annotate,
}

#[derive(Clone, Copy)]
enum Node {
    Literal(Literal),
    Arithmetic(IntegerOperation, usize, usize),
    Convert(IntegerType, usize),
    Annotate(IntegerType, usize),
}

#[derive(Clone, Copy)]
enum PreparedNode {
    Unsupported,
    Supported { node: Node, first_constraint: Option<IntegerType> },
}

#[derive(Clone, Copy, Debug)]
enum PlannedOperation {
    Value(IntegerValue),
    Arithmetic(IntegerType, IntegerOperation, usize, usize),
    Convert(IntegerType, usize),
    Annotate(IntegerType, usize),
}

#[derive(Debug)]
struct PlannedRow {
    span: Range<usize>,
    nat: Result<PlannedOperation, IntegerCheckError>,
    signed: Result<PlannedOperation, IntegerCheckError>,
}

type Evaluation = Result<IntegerValue, IntegerEvaluationError>;

struct EvaluationRow {
    nat: Option<Evaluation>,
    signed: Option<Evaluation>,
}

type Meaning = (IntegerType, int, Range<usize>);
type RowMeaning = (Option<Meaning>, Option<Meaning>);

/// 検査済みの整数式と、元ソース上のその範囲。
#[derive(Debug)]
pub struct CheckedIntegerExpression {
    rows: Vec<PlannedRow>,
    ty: IntegerType,
}

spec fn literal_model(form: Form, index: usize) -> Option<Literal> {
    match form {
        Form::Atom { kind: AtomKind::Natural, .. } => Some(Literal { index, negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => Some(Literal { index, negative: true }),
        _ => None,
    }
}

spec fn builtin_model(word: Seq<u8>) -> Option<Builtin> {
    if word == "add".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Add)) }
    else if word == "sub".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Sub)) }
    else if word == "mul".spec_bytes() { Some(Builtin::Arithmetic(IntegerOperation::Mul)) }
    else if word == "int-to-nat".spec_bytes() { Some(Builtin::Convert(IntegerType::Nat)) }
    else if word == "nat-to-int".spec_bytes() { Some(Builtin::Convert(IntegerType::Int)) }
    else if word == "as-type".spec_bytes() { Some(Builtin::Annotate) }
    else { None }
}

spec fn type_model(word: Seq<u8>) -> Option<IntegerType> {
    if word == "Nat".spec_bytes() { Some(IntegerType::Nat) }
    else if word == "Int".spec_bytes() { Some(IntegerType::Int) }
    else { None }
}

fn literal(form: &Form, index: usize) -> (result: Option<Literal>)
    ensures result == literal_model(*form, index),
{
    match form {
        Form::Atom { kind: AtomKind::Natural, .. } => Some(Literal { index, negative: false }),
        Form::Atom { kind: AtomKind::NegativeInteger, .. } => Some(Literal { index, negative: true }),
        _ => None,
    }
}

fn builtin(word: &str) -> (head: Option<Builtin>)
    ensures head == builtin_model(word.spec_bytes()),
{
    if is_spelling(word, "add") { Some(Builtin::Arithmetic(IntegerOperation::Add)) }
    else if is_spelling(word, "sub") { Some(Builtin::Arithmetic(IntegerOperation::Sub)) }
    else if is_spelling(word, "mul") { Some(Builtin::Arithmetic(IntegerOperation::Mul)) }
    else if is_spelling(word, "int-to-nat") { Some(Builtin::Convert(IntegerType::Nat)) }
    else if is_spelling(word, "nat-to-int") { Some(Builtin::Convert(IntegerType::Int)) }
    else if is_spelling(word, "as-type") { Some(Builtin::Annotate) }
    else { None }
}

fn integer_type(word: &str) -> (ty: Option<IntegerType>)
    ensures ty == type_model(word.spec_bytes()),
{
    if is_spelling(word, "Nat") { Some(IntegerType::Nat) }
    else if is_spelling(word, "Int") { Some(IntegerType::Int) }
    else { None }
}

spec fn direct_node_model(source: &str, forms: Seq<Form>, at: usize) -> Option<Node>
    recommends at < forms.len(),
{
    if literal_model(forms[at as int], at).is_some() {
        Some(Node::Literal(literal_model(forms[at as int], at)->Some_0))
    } else if forms[at as int] is List {
        let end = subtree_limit(forms, at);
        if at + 3 <= end <= forms.len()
            && (forms[at + 1] matches Form::Atom { kind: AtomKind::Name, .. })
        {
            let first = (at + 2) as usize;
            let after_first = subtree_limit(forms, first);
            match builtin_model(spelling(source, forms[at + 1])) {
                Some(Builtin::Arithmetic(op)) if first < after_first < end
                    && subtree_limit(forms, after_first) == end =>
                    Some(Node::Arithmetic(op, first, after_first)),
                Some(Builtin::Convert(ty)) if after_first == end =>
                    Some(Node::Convert(ty, first)),
                Some(Builtin::Annotate) if first + 1 < end
                    && (forms[first as int] matches Form::Atom { kind: AtomKind::Name, .. })
                    && subtree_limit(forms, (first + 1) as usize) == end =>
                    match type_model(spelling(source, forms[first as int])) {
                        Some(ty) => Some(Node::Annotate(ty, (first + 1) as usize)),
                        None => None,
                    },
                _ => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// リストの直下にある引数の部分木を、平坦な構文木の添字で求める。
fn direct_node(source: &str, forms: &[Form], at: usize) -> (result: Option<Node>)
    requires at < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures result == direct_node_model(source, forms@, at),
{
    if let Some(leaf) = literal(&forms[at], at) {
        return Some(Node::Literal(leaf));
    }
    let Form::List { end: limit, .. } = &forms[at] else { return None; };
    let end = *limit;
    if end > forms.len() || end < at || end - at < 3 {
        return None;
    }
    if !matches!(forms[at + 1], Form::Atom { kind: AtomKind::Name, .. }) {
        return None;
    }
    let first = at + 2;
    let after_first = subtree_end(forms, first);
    match builtin(source_word(source, forms, at + 1)) {
        Some(Builtin::Arithmetic(op)) if first < after_first && after_first < end
            && subtree_end(forms, after_first) == end =>
            Some(Node::Arithmetic(op, first, after_first)),
        Some(Builtin::Convert(ty)) if after_first == end => Some(Node::Convert(ty, first)),
        Some(Builtin::Annotate) if first + 1 < end
            && matches!(forms[first], Form::Atom { kind: AtomKind::Name, .. })
            && subtree_end(forms, first + 1) == end =>
            match integer_type(source_word(source, forms, first)) {
                Some(ty) => Some(Node::Annotate(ty, first + 1)),
                None => None,
            },
        _ => None,
    }
}

spec fn node_edges_ordered(node: Node, at: usize, len: nat) -> bool {
    match node {
        Node::Literal(leaf) => leaf.index == at,
        Node::Arithmetic(_, left, right) => at < left < right < len,
        Node::Convert(_, child) | Node::Annotate(_, child) => at < child < len,
    }
}

proof fn direct_edges_are_ordered(source: &str, forms: Seq<Form>, at: usize, node: Node)
    requires at < forms.len(), direct_node_model(source, forms, at) == Some(node),
    ensures node_edges_ordered(node, at, forms.len()),
{
}

spec fn describe_node(node: Option<Node>, len: nat, suffix: Seq<PreparedNode>) -> PreparedNode {
    match node {
        Some(Node::Literal(leaf)) => PreparedNode::Supported {
            node: Node::Literal(leaf),
            first_constraint: if leaf.negative { Some(IntegerType::Int) } else { None },
        },
        Some(Node::Arithmetic(op, left, right)) => match (suffix[len - 1 - left], suffix[len - 1 - right]) {
            (
                PreparedNode::Supported { first_constraint: a, .. },
                PreparedNode::Supported { first_constraint: b, .. },
            ) => PreparedNode::Supported {
                node: Node::Arithmetic(op, left, right),
                first_constraint: if a.is_some() { a } else { b },
            },
            _ => PreparedNode::Unsupported,
        },
        Some(Node::Convert(ty, child)) => if suffix[len - 1 - child] is Supported {
            PreparedNode::Supported { node: Node::Convert(ty, child), first_constraint: Some(ty) }
        } else {
            PreparedNode::Unsupported
        },
        Some(Node::Annotate(ty, child)) => if suffix[len - 1 - child] is Supported {
            PreparedNode::Supported { node: Node::Annotate(ty, child), first_constraint: Some(ty) }
        } else {
            PreparedNode::Unsupported
        },
        None => PreparedNode::Unsupported,
    }
}

spec fn described_suffix(source: &str, forms: Seq<Form>, from: nat) -> Seq<PreparedNode>
    recommends from <= forms.len(),
    decreases forms.len() - from,
{
    if from >= forms.len() {
        Seq::empty()
    } else {
        let suffix = described_suffix(source, forms, from + 1);
        suffix.push(describe_node(direct_node_model(source, forms, from as usize), forms.len(), suffix))
    }
}

fn describe(source: &str, forms: &[Form], at: usize, suffix: &[PreparedNode]) -> (row: PreparedNode)
    requires
        at < forms@.len(), suffix@.len() == forms@.len() - 1 - at,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures row == describe_node(direct_node_model(source, forms@, at), forms@.len(), suffix@),
{
    let Some(node) = direct_node(source, forms, at) else { return PreparedNode::Unsupported; };
    proof { direct_edges_are_ordered(source, forms@, at, node); }
    let last = forms.len() - 1;
    let first_constraint = match node {
        Node::Literal(leaf) => if leaf.negative { Some(IntegerType::Int) } else { None },
        Node::Arithmetic(_, left, right) => match (suffix[last - left], suffix[last - right]) {
            (
                PreparedNode::Supported { first_constraint: a, .. },
                PreparedNode::Supported { first_constraint: b, .. },
            ) => if a.is_some() { a } else { b },
            _ => return PreparedNode::Unsupported,
        },
        Node::Convert(ty, child) | Node::Annotate(ty, child) => {
            if matches!(suffix[last - child], PreparedNode::Unsupported) {
                return PreparedNode::Unsupported;
            }
            Some(ty)
        }
    };
    PreparedNode::Supported { node, first_constraint }
}

/// 子を先に調べ、各部分式の結果型を決める最初の制約を保持する。
fn describe_nodes(source: &str, forms: &[Form]) -> (rows: Vec<PreparedNode>)
    requires form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures rows@ == described_suffix(source, forms@, 0), rows@.len() == forms@.len(),
{
    let mut rows = Vec::new();
    let mut from = forms.len();
    while from > 0
        invariant
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            from <= forms@.len(),
            rows@.len() == forms@.len() - from,
            rows@ == described_suffix(source, forms@, from as nat),
        decreases from,
    {
        let at = from - 1;
        let row = describe(source, forms, at, rows.as_slice());
        proof { reveal_with_fuel(described_suffix, 2); }
        rows.push(row);
        from = at;
    }
    rows
}

spec fn prepared_row_sound(source: &str, forms: Seq<Form>, rows: Seq<PreparedNode>) -> bool {
    &&& rows.len() == forms.len()
    &&& forall|at: int| 0 <= at < forms.len() ==> {
        let row = #[trigger] rows[forms.len() - 1 - at];
        row == describe_node(direct_node_model(source, forms, at as usize), forms.len(),
            rows.take(forms.len() - 1 - at))
    }
}

proof fn describe_corresponds(
    source: &str, forms: Seq<Form>, from: nat, at: nat, reverse: Seq<PreparedNode>,
)
    requires
        from <= at < forms.len(),
        reverse == described_suffix(source, forms, from),
        reverse.len() == forms.len() - from,
    ensures
        reverse[forms.len() - 1 - at] == describe_node(direct_node_model(source, forms, at as usize),
            forms.len(), reverse.take(forms.len() - 1 - at)),
    decreases at - from,
{
    reveal_with_fuel(described_suffix, 2);
    let tail = described_suffix(source, forms, from + 1);
    if from == at {
        assert(reverse.take(forms.len() - 1 - at) =~= tail);
    } else {
        describe_corresponds(source, forms, from + 1, at, tail);
        assert(reverse.take(forms.len() - 1 - at) =~= tail.take(forms.len() - 1 - at));
    }
}

proof fn all_description_rows_sound(source: &str, forms: Seq<Form>, rows: Seq<PreparedNode>)
    requires rows == described_suffix(source, forms, 0), rows.len() == forms.len(),
    ensures prepared_row_sound(source, forms, rows),
{
    assert forall|at: int| 0 <= at < forms.len() implies {
        let row = #[trigger] rows[forms.len() - 1 - at];
        row == describe_node(direct_node_model(source, forms, at as usize), forms.len(),
            rows.take(forms.len() - 1 - at))
    } by {
        describe_corresponds(source, forms, 0, at as nat, rows);
    };
}

proof fn supported_node_is_direct(source: &str, forms: Seq<Form>, rows: Seq<PreparedNode>, at: usize, node: Node)
    requires
        prepared_row_sound(source, forms, rows), at < forms.len(),
        rows[forms.len() - 1 - at] matches PreparedNode::Supported { node: n, .. } && node == n,
    ensures
        direct_node_model(source, forms, at) == Some(node),
        node_edges_ordered(node, at, forms.len()),
{
    let row = rows[forms.len() - 1 - at];
    assert(row == describe_node(direct_node_model(source, forms, at), forms.len(), rows.take(forms.len() - 1 - at)));
    assert(direct_node_model(source, forms, at) == Some(node));
    direct_edges_are_ordered(source, forms, at, node);
}

spec fn first_constraint_at(rows: Seq<PreparedNode>, len: nat, at: usize) -> Option<IntegerType> {
    match rows[len - 1 - at] {
        PreparedNode::Supported { first_constraint, .. } => first_constraint,
        PreparedNode::Unsupported => None,
    }
}

spec fn supported_at(rows: Seq<PreparedNode>, len: nat, at: usize) -> bool {
    at < len && len - 1 - at < rows.len() && rows[len - 1 - at] is Supported
}

proof fn children_are_supported(source: &str, forms: Seq<Form>, rows: Seq<PreparedNode>, at: usize, node: Node)
    requires
        prepared_row_sound(source, forms, rows),
        supported_at(rows, forms.len(), at),
        rows[forms.len() - 1 - at]->Supported_node == node,
    ensures
        match node {
            Node::Literal(_) => true,
            Node::Arithmetic(_, left, right) => {
                &&& supported_at(rows, forms.len(), left)
                &&& supported_at(rows, forms.len(), right)
                &&& first_constraint_at(rows, forms.len(), at)
                    == if first_constraint_at(rows, forms.len(), left).is_some() {
                        first_constraint_at(rows, forms.len(), left)
                    } else {
                        first_constraint_at(rows, forms.len(), right)
                    }
            },
            Node::Convert(_, child) | Node::Annotate(_, child) => supported_at(rows, forms.len(), child),
        },
{
    supported_node_is_direct(source, forms, rows, at, node);
    let row = rows[forms.len() - 1 - at];
    let prefix = rows.take(forms.len() - 1 - at);
    assert(row == describe_node(Some(node), forms.len(), prefix));
    match node {
        Node::Literal(_) => {},
        Node::Arithmetic(_, left, right) => {
            assert(prefix[forms.len() - 1 - left] == rows[forms.len() - 1 - left]);
            assert(prefix[forms.len() - 1 - right] == rows[forms.len() - 1 - right]);
        }
        Node::Convert(_, child) | Node::Annotate(_, child) => {
            assert(prefix[forms.len() - 1 - child] == rows[forms.len() - 1 - child]);
        }
    }
}

spec fn planned_for(row: PlannedRow, ty: IntegerType) -> Result<PlannedOperation, IntegerCheckError> {
    match ty {
        IntegerType::Nat => row.nat,
        IntegerType::Int => row.signed,
    }
}

spec fn dependency_ready(suffix: Seq<PlannedRow>, len: nat, at: int, dependency: usize, ty: IntegerType) -> bool {
    &&& at < dependency < len
    &&& len - 1 - dependency < suffix.len()
    &&& planned_for(suffix[len - 1 - dependency], ty).is_ok()
}

spec fn operation_ready(result: Result<PlannedOperation, IntegerCheckError>, ty: IntegerType,
    at: int, len: nat, suffix: Seq<PlannedRow>,
) -> bool {
    match result {
        Err(_) => true,
        Ok(PlannedOperation::Value(value)) => value_has_type(value, ty),
        Ok(PlannedOperation::Arithmetic(at_ty, _, left, right)) => at_ty == ty
            && dependency_ready(suffix, len, at, left, ty) && dependency_ready(suffix, len, at, right, ty),
        Ok(PlannedOperation::Convert(target, child)) => target == ty
            && dependency_ready(suffix, len, at, child, opposite(target)),
        Ok(PlannedOperation::Annotate(target, child)) => target == ty
            && dependency_ready(suffix, len, at, child, target),
    }
}

spec fn plans_ready(rows: Seq<PlannedRow>, len: nat) -> bool {
    &&& rows.len() <= len
    &&& forall|row: int| 0 <= row < rows.len() ==> {
        let entry = #[trigger] rows[row];
        let at = len - 1 - row;
        &&& operation_ready(entry.nat, IntegerType::Nat, at, len, rows.take(row))
        &&& operation_ready(entry.signed, IntegerType::Int, at, len, rows.take(row))
    }
}

fn error_copy(error: &IntegerCheckError) -> (out: IntegerCheckError)
    ensures out == *error,
{
    match error {
        IntegerCheckError::Syntax(error) => IntegerCheckError::Syntax(syntax::Error {
            kind: error.kind, span: error.span.start..error.span.end,
        }),
        IntegerCheckError::UnsupportedExpression(span) =>
            IntegerCheckError::UnsupportedExpression(span.start..span.end),
        IntegerCheckError::TypeMismatch { span, expected, actual } => IntegerCheckError::TypeMismatch {
            span: span.start..span.end, expected: *expected, actual: *actual,
        },
        IntegerCheckError::LiteralOutOfRange { span, ty } => IntegerCheckError::LiteralOutOfRange {
            span: span.start..span.end, ty: *ty,
        },
    }
}

fn planned_result(row: &PlannedRow, ty: IntegerType) -> (result: Result<PlannedOperation, IntegerCheckError>)
    ensures result == planned_for(*row, ty),
{
    let result = match ty {
        IntegerType::Nat => &row.nat,
        IntegerType::Int => &row.signed,
    };
    match result {
        Ok(operation) => Ok(*operation),
        Err(error) => Err(error_copy(error)),
    }
}

spec fn prefer_child(span: Range<usize>, actual: IntegerType, expected: IntegerType,
    child: usize, child_ty: IntegerType, suffix: Seq<PlannedRow>, len: nat, convert: bool,
) -> Result<PlannedOperation, IntegerCheckError> {
    if actual != expected {
        Err(IntegerCheckError::TypeMismatch { span, expected, actual })
    } else {
        match planned_for(suffix[len - 1 - child], child_ty) {
            Err(error) => Err(error),
            Ok(_) => if convert { Ok(PlannedOperation::Convert(actual, child)) }
                else { Ok(PlannedOperation::Annotate(actual, child)) },
        }
    }
}

spec fn plan_one_model(
    source: &str, forms: Seq<Form>, at: usize, node: PreparedNode,
    ty: IntegerType, suffix: Seq<PlannedRow>,
) -> Result<PlannedOperation, IntegerCheckError> {
    match node {
        PreparedNode::Unsupported => Err(IntegerCheckError::UnsupportedExpression(0..source.spec_bytes().len() as usize)),
        PreparedNode::Supported { node, .. } => match node {
            Node::Literal(leaf) => match checked_literal(source, forms[leaf.index as int], ty) {
                Err(error) => Err(error),
                Ok(value) => Ok(PlannedOperation::Value(value)),
            },
            Node::Arithmetic(op, left, right) => {
                match planned_for(suffix[forms.len() - 1 - left], ty) {
                    Err(error) => Err(error),
                    Ok(_) => match planned_for(suffix[forms.len() - 1 - right], ty) {
                        Err(error) => Err(error),
                        Ok(_) => Ok(PlannedOperation::Arithmetic(ty, op, left, right)),
                    },
                }
            },
            Node::Convert(actual, child) => prefer_child(form_span(forms[at as int]), actual, ty, child,
                opposite(actual), suffix, forms.len(), true),
            Node::Annotate(actual, child) => prefer_child(form_span(forms[at as int]), actual, ty, child,
                actual, suffix, forms.len(), false),
        },
    }
}

fn plan_one(
    source: &str, forms: &[Form], at: usize, prepared: &[PreparedNode],
    ty: IntegerType, suffix: &[PlannedRow],
) -> (result: Result<PlannedOperation, IntegerCheckError>)
    requires
        at < forms@.len(), prepared_row_sound(source, forms@, prepared@),
        suffix@.len() == forms@.len() - 1 - at,
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result == plan_one_model(source, forms@, at, prepared@[forms@.len() - 1 - at], ty, suffix@),
        operation_ready(result, ty, at as int, forms@.len(), suffix@),
{
    let last = forms.len() - 1;
    let PreparedNode::Supported { node: expression, .. } = prepared[last - at] else {
        return Err(IntegerCheckError::UnsupportedExpression(0..source.as_bytes().len()));
    };
    proof { supported_node_is_direct(source, forms@, prepared@, at, expression); }
    match expression {
        Node::Literal(leaf) => {
            let value = check_operand(source, forms, leaf.index, ty)?;
            Ok(PlannedOperation::Value(value))
        }
        Node::Arithmetic(op, left, right) => {
            planned_result(&suffix[last - left], ty)?;
            planned_result(&suffix[last - right], ty)?;
            Ok(PlannedOperation::Arithmetic(ty, op, left, right))
        }
        Node::Convert(actual, child) | Node::Annotate(actual, child) => {
            if matches!((actual, ty), (IntegerType::Nat, IntegerType::Int) | (IntegerType::Int, IntegerType::Nat)) {
                return Err(IntegerCheckError::TypeMismatch { span: copy_span(&forms[at]), expected: ty, actual });
            }
            if matches!(expression, Node::Convert(_, _)) {
                planned_result(&suffix[last - child], other_type(actual))?;
                Ok(PlannedOperation::Convert(actual, child))
            } else {
                planned_result(&suffix[last - child], actual)?;
                Ok(PlannedOperation::Annotate(actual, child))
            }
        }
    }
}

spec fn planned_suffix(source: &str, forms: Seq<Form>, prepared: Seq<PreparedNode>, from: nat)
    -> Seq<PlannedRow>
    recommends from <= forms.len(),
    decreases forms.len() - from,
{
    if from >= forms.len() {
        Seq::empty()
    } else {
        let suffix = planned_suffix(source, forms, prepared, from + 1);
        let node = prepared[forms.len() - 1 - from];
        suffix.push(PlannedRow {
            span: form_span(forms[from as int]),
            nat: plan_one_model(source, forms, from as usize, node, IntegerType::Nat, suffix),
            signed: plan_one_model(source, forms, from as usize, node, IntegerType::Int, suffix),
        })
    }
}

/// 検査結果を期待型ごとに保持する。診断を引き継ぐときは左の部分式を優先する。
fn plan_nodes(source: &str, forms: &[Form], prepared: &[PreparedNode]) -> (rows: Vec<PlannedRow>)
    requires
        prepared_row_sound(source, forms@, prepared@),
        form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        rows@ == planned_suffix(source, forms@, prepared@, 0),
        rows@.len() == forms@.len(),
        plans_ready(rows@, forms@.len()),
{
    let mut rows = Vec::new();
    let mut from = forms.len();
    while from > 0
        invariant
            prepared_row_sound(source, forms@, prepared@),
            form_spans_valid(source, forms@, source.spec_bytes().len() as int),
            from <= forms@.len(),
            rows@.len() == forms@.len() - from,
            rows@ == planned_suffix(source, forms@, prepared@, from as nat),
            plans_ready(rows@, forms@.len()),
        decreases from,
    {
        let at = from - 1;
        let natural = plan_one(source, forms, at, prepared, IntegerType::Nat, rows.as_slice());
        let signed = plan_one(source, forms, at, prepared, IntegerType::Int, rows.as_slice());
        let ghost before = rows@;
        proof { reveal_with_fuel(planned_suffix, 2); }
        rows.push(PlannedRow { span: copy_span(&forms[at]), nat: natural, signed });
        proof {
            assert forall|i: int| 0 <= i < rows@.len() implies {
                let entry = #[trigger] rows@[i];
                let node = forms@.len() - 1 - i;
                &&& operation_ready(entry.nat, IntegerType::Nat, node, forms@.len(), rows@.take(i))
                &&& operation_ready(entry.signed, IntegerType::Int, node, forms@.len(), rows@.take(i))
            } by {
                if i == before.len() {
                    assert(rows@.take(i) =~= before);
                } else {
                    assert(rows@.take(i) =~= before.take(i));
                    assert(rows@[i] == before[i]);
                }
            };
        }
        from = at;
    }
    rows
}

spec fn event_fits(event: Meaning) -> bool {
    match event.0 {
        IntegerType::Nat => 0 <= event.1 <= u64::MAX,
        IntegerType::Int => i64::MIN <= event.1 <= i64::MAX,
    }
}

spec fn expected_meaning(row: RowMeaning, ty: IntegerType) -> Option<Meaning> {
    match ty { IntegerType::Nat => row.0, IntegerType::Int => row.1 }
}

spec fn child_meaning(events: Seq<RowMeaning>, len: nat, index: usize, ty: IntegerType)
    -> Option<Meaning>
{
    expected_meaning(events[len - 1 - index], ty)
}

spec fn unary_meaning(span: Range<usize>, ty: IntegerType, arg: Option<Meaning>) -> Option<Meaning> {
    match arg {
        None => None,
        Some(event) => if !event_fits(event) {
            Some(event)
        } else {
            Some((ty, event.1, span))
        },
    }
}

spec fn eval_plan_model(
    planned: Result<PlannedOperation, IntegerCheckError>, span: Range<usize>,
    len: nat, events: Seq<RowMeaning>,
) -> Option<Meaning> {
    match planned {
        Err(_) => None,
        Ok(PlannedOperation::Value(IntegerValue::Nat(n))) => Some((IntegerType::Nat, n as int, span)),
        Ok(PlannedOperation::Value(IntegerValue::Int(n))) => Some((IntegerType::Int, n as int, span)),
        Ok(PlannedOperation::Arithmetic(ty, operation, left, right)) => {
            match child_meaning(events, len, left, ty) {
                None => None,
                Some(a) => if !event_fits(a) { Some(a) } else {
                    match child_meaning(events, len, right, ty) {
                        None => None,
                        Some(b) => if !event_fits(b) { Some(b) } else {
                            Some((ty, arithmetic_value(operation, a.1, b.1), span))
                        },
                    }
                },
            }
        }
        Ok(PlannedOperation::Convert(ty, child)) =>
            unary_meaning(span, ty, child_meaning(events, len, child, opposite(ty))),
        Ok(PlannedOperation::Annotate(ty, child)) =>
            unary_meaning(span, ty, child_meaning(events, len, child, ty)),
    }
}

spec fn meaning_prefix(rows: Seq<PlannedRow>, size: nat) -> Seq<RowMeaning>
    recommends size <= rows.len(),
    decreases size,
{
    if size == 0 {
        Seq::empty()
    } else {
        let prefix = meaning_prefix(rows, (size - 1) as nat);
        let row = rows[size - 1];
        prefix.push((
            eval_plan_model(row.nat, row.span, rows.len(), prefix),
            eval_plan_model(row.signed, row.span, rows.len(), prefix),
        ))
    }
}

spec fn evaluation_event_matches(result: Option<Evaluation>, event: Option<Meaning>) -> bool {
    match event {
        None => result.is_none(),
        Some(event) => result matches Some(evaluation)
            && integer_evaluation_matches(event.0, event.1, event.2, evaluation),
    }
}

spec fn evaluated_for(row: EvaluationRow, ty: IntegerType) -> Option<Evaluation> {
    match ty { IntegerType::Nat => row.nat, IntegerType::Int => row.signed }
}

spec fn evaluation_ready(
    plans: Seq<PlannedRow>, results: Seq<EvaluationRow>, meanings: Seq<RowMeaning>,
) -> bool {
    &&& results.len() == meanings.len() <= plans.len()
    &&& forall|i: int| 0 <= i < results.len() ==> {
        let row = #[trigger] results[i];
        let plan = plans[i];
        let meaning = meanings[i];
        &&& row.nat.is_some() == plan.nat.is_ok()
        &&& row.signed.is_some() == plan.signed.is_ok()
        &&& evaluation_event_matches(row.nat, meaning.0)
        &&& evaluation_event_matches(row.signed, meaning.1)
        &&& (row.nat matches Some(Ok(value)) ==> value_has_type(value, IntegerType::Nat))
        &&& (row.signed matches Some(Ok(value)) ==> value_has_type(value, IntegerType::Int))
    }
}

fn copy_evaluation(row: &EvaluationRow, ty: IntegerType) -> (result: Option<Evaluation>)
    ensures result == evaluated_for(*row, ty),
{
    let slot = match ty { IntegerType::Nat => &row.nat, IntegerType::Int => &row.signed };
    match slot {
        None => None,
        Some(Ok(value)) => Some(Ok(*value)),
        Some(Err(error)) => Some(Err(IntegerEvaluationError {
            span: error.span.start..error.span.end, ty: error.ty,
        })),
    }
}

proof fn child_result_ready(
    plans: Seq<PlannedRow>, results: Seq<EvaluationRow>, meanings: Seq<RowMeaning>,
    at: int, index: usize, ty: IntegerType,
)
    requires
        evaluation_ready(plans, results, meanings), dependency_ready(plans.take(results.len() as int), plans.len(), at, index, ty),
    ensures
        plans.len() - 1 - index < results.len(),
        evaluated_for(results[plans.len() - 1 - index], ty).is_some(),
        evaluation_event_matches(evaluated_for(results[plans.len() - 1 - index], ty),
            child_meaning(meanings, plans.len(), index, ty)),
        evaluated_for(results[plans.len() - 1 - index], ty) matches Some(Ok(value)) ==> value_has_type(value, ty),
{
    let position = plans.len() - 1 - index;
    assert(plans.take(results.len() as int)[position] == plans[position]);
    assert(results[position] == results[position]);
}

fn eval_one(
    plans: &[PlannedRow], prefix: &[EvaluationRow], row: usize, ty: IntegerType,
    Ghost(events): Ghost<Seq<RowMeaning>>,
) -> (result: Option<Evaluation>)
    requires
        row < plans@.len(), prefix@.len() == row,
        evaluation_ready(plans@, prefix@, events),
        operation_ready(planned_for(plans@[row as int], ty), ty,
            plans@.len() - 1 - row, plans@.len(), plans@.take(row as int)),
    ensures
        result.is_some() == planned_for(plans@[row as int], ty).is_ok(),
        evaluation_event_matches(result, eval_plan_model(planned_for(plans@[row as int], ty),
            plans@[row as int].span, plans@.len(), events)),
        result matches Some(Ok(value)) ==> value_has_type(value, ty),
{
    let entry = &plans[row];
    let Ok(plan) = planned_result(entry, ty) else { return None; };
    let span = entry.span.start..entry.span.end;
    let last = plans.len() - 1;
    let ghost at = plans@.len() - 1 - row;
    match plan {
        PlannedOperation::Value(value) => Some(Ok(value)),
        PlannedOperation::Arithmetic(ty, operation, left, right) => {
            proof { child_result_ready(plans@, prefix@, events, at, left, ty); }
            let lhs = match copy_evaluation(&prefix[last - left], ty)? {
                Ok(value) => value,
                Err(error) => return Some(Err(error)),
            };
            proof { child_result_ready(plans@, prefix@, events, at, right, ty); }
            let rhs = match copy_evaluation(&prefix[last - right], ty)? {
                Ok(value) => value,
                Err(error) => return Some(Err(error)),
            };
            match (lhs, rhs) {
                (IntegerValue::Nat(a), IntegerValue::Nat(b)) => Some(pack_nat(evaluate_nat(operation, a, b), span)),
                (IntegerValue::Int(a), IntegerValue::Int(b)) => Some(pack_int(evaluate_int(operation, a, b), span)),
                _ => unreachable!(),
            }
        }
        PlannedOperation::Convert(target, child) => {
            let input = other_type(target);
            proof { child_result_ready(plans@, prefix@, events, at, child, input); }
            match copy_evaluation(&prefix[last - child], input)? {
                Ok(IntegerValue::Nat(n)) => Some(pack_int(nat_to_int(n), span)),
                Ok(IntegerValue::Int(n)) => Some(pack_nat(int_to_nat(n), span)),
                Err(error) => Some(Err(error)),
            }
        }
        PlannedOperation::Annotate(target, child) => {
            proof { child_result_ready(plans@, prefix@, events, at, child, target); }
            copy_evaluation(&prefix[last - child], target)
        }
    }
}

fn eval_rows(plans: &[PlannedRow]) -> (results: Vec<EvaluationRow>)
    requires plans_ready(plans@, plans@.len()),
    ensures
        results@.len() == plans@.len(),
        evaluation_ready(plans@, results@, meaning_prefix(plans@, plans@.len())),
{
    let mut results = Vec::new();
    let mut row = 0;
    while row < plans.len()
        invariant
            plans_ready(plans@, plans@.len()),
            row <= plans@.len(),
            results@.len() == row,
            evaluation_ready(plans@, results@, meaning_prefix(plans@, row as nat)),
        decreases plans@.len() - row,
    {
        let ghost before = results@;
        let ghost events = meaning_prefix(plans@, row as nat);
        let natural = eval_one(plans, results.as_slice(), row, IntegerType::Nat, Ghost(events));
        let signed = eval_one(plans, results.as_slice(), row, IntegerType::Int, Ghost(events));
        results.push(EvaluationRow { nat: natural, signed });
        proof {
            reveal_with_fuel(meaning_prefix, 2);
            let next = meaning_prefix(plans@, (row + 1) as nat);
            assert forall|i: int| 0 <= i < results@.len() implies {
                let evaluated = #[trigger] results@[i];
                let plan = plans@[i];
                let event = next[i];
                &&& evaluated.nat.is_some() == plan.nat.is_ok()
                &&& evaluated.signed.is_some() == plan.signed.is_ok()
                &&& evaluation_event_matches(evaluated.nat, event.0)
                &&& evaluation_event_matches(evaluated.signed, event.1)
                &&& (evaluated.nat matches Some(Ok(value)) ==> value_has_type(value, IntegerType::Nat))
                &&& (evaluated.signed matches Some(Ok(value)) ==> value_has_type(value, IntegerType::Int))
            } by {
                if i < row {
                    assert(results@[i] == before[i]);
                    assert(next[i] == events[i]);
                }
            };
        }
        row += 1;
    }
    results
}

fn copy_span(form: &Form) -> (span: Range<usize>)
    ensures span == form_span(*form),
{
    match form {
        Form::Atom { span, .. } | Form::List { span, .. } => span.start..span.end,
    }
}

proof fn literal_results_agree(
    bytes: Seq<u8>, expected: IntegerType, a: Result<IntegerValue, IntegerLiteralError>,
    b: Result<IntegerValue, IntegerLiteralError>,
)
    requires
        integer_literal_matches(bytes, Some(expected), a),
        integer_literal_matches(bytes, Some(expected), b),
    ensures a == b,
{
}

spec fn checked_literal(
    source: &str, form: Form, ty: IntegerType,
) -> Result<IntegerValue, IntegerCheckError> {
    let bytes = spelling(source, form);
    let span = form_span(form);
    let parsed = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(bytes, Some(ty), r);
    match parsed {
        Ok(v) => Ok(v),
        Err(IntegerLiteralError::OutOfRange(range_ty)) =>
            Err(IntegerCheckError::LiteralOutOfRange { span, ty: range_ty }),
        Err(IntegerLiteralError::NegativeLiteralForNat) =>
            Err(IntegerCheckError::TypeMismatch { span, expected: IntegerType::Nat, actual: IntegerType::Int }),
        Err(IntegerLiteralError::InvalidDigits) => Err(IntegerCheckError::UnsupportedExpression(span)),
    }
}

spec fn value_has_type(value: IntegerValue, ty: IntegerType) -> bool {
    match (value, ty) {
        (IntegerValue::Nat(_), IntegerType::Nat) | (IntegerValue::Int(_), IntegerType::Int) => true,
        _ => false,
    }
}

fn check_operand(source: &str, forms: &[Form], at: usize, ty: IntegerType)
    -> (result: Result<IntegerValue, IntegerCheckError>)
    requires at < forms@.len(), form_spans_valid(source, forms@, source.spec_bytes().len() as int),
    ensures
        result == checked_literal(source, forms@[at as int], ty),
        result matches Ok(value) ==> value_has_type(value, ty),
{
    let word = source_word(source, forms, at);
    let read = read_integer_literal(word, Some(ty));
    proof {
        let bytes = spelling(source, forms@[at as int]);
        let model = choose|r: Result<IntegerValue, IntegerLiteralError>| integer_literal_matches(bytes, Some(ty), r);
        literal_results_agree(bytes, ty, read, model);
    }
    match read {
        Ok(value) => Ok(value),
        Err(IntegerLiteralError::OutOfRange(ty)) =>
            Err(IntegerCheckError::LiteralOutOfRange { span: copy_span(&forms[at]), ty }),
        Err(IntegerLiteralError::NegativeLiteralForNat) => Err(IntegerCheckError::TypeMismatch {
            span: copy_span(&forms[at]), expected: IntegerType::Nat, actual: IntegerType::Int,
        }),
        Err(IntegerLiteralError::InvalidDigits) =>
            Err(IntegerCheckError::UnsupportedExpression(copy_span(&forms[at]))),
    }
}

spec fn opposite(ty: IntegerType) -> IntegerType {
    match ty { IntegerType::Nat => IntegerType::Int, IntegerType::Int => IntegerType::Nat }
}

fn other_type(ty: IntegerType) -> (other: IntegerType)
    ensures other == opposite(ty),
{
    match ty { IntegerType::Nat => IntegerType::Int, IntegerType::Int => IntegerType::Nat }
}

spec fn pick_type(expected: Option<IntegerType>, constraint: Option<IntegerType>) -> IntegerType {
    match expected {
        Some(explicit) => explicit,
        None => match constraint { Some(actual) => actual, None => IntegerType::Nat },
    }
}

fn integer_signature(expected: Option<IntegerType>, constraint: Option<IntegerType>) -> (ty: IntegerType)
    ensures ty == pick_type(expected, constraint),
{
    match expected {
        Some(explicit) => explicit,
        None => match constraint { Some(actual) => actual, None => IntegerType::Nat },
    }
}

spec fn program_model(source: &str, forms: Seq<Form>, expected: Option<IntegerType>)
    -> Result<(Seq<PlannedRow>, IntegerType), IntegerCheckError>
{
    let rejection = Err(IntegerCheckError::UnsupportedExpression(0..source.spec_bytes().len() as usize));
    if forms.len() == 0 || subtree_limit(forms, 0) != forms.len() {
        rejection
    } else {
        let prepared = described_suffix(source, forms, 0);
        match prepared[forms.len() - 1] {
            PreparedNode::Unsupported => rejection,
            PreparedNode::Supported { first_constraint, .. } => {
                let ty = pick_type(expected, first_constraint);
                let rows = planned_suffix(source, forms, prepared, 0);
                match planned_for(rows[forms.len() - 1], ty) {
                    Ok(_) => Ok((rows, ty)),
                    Err(error) => Err(error),
                }
            }
        }
    }
}

/// 共通の構文規則と整数式の型検査に対応する結果を表す。
pub closed spec fn integer_check_matches(
    source: &str, expected: Option<IntegerType>, result: Result<CheckedIntegerExpression, IntegerCheckError>,
) -> bool {
    if well_formed_sexpr(source) {
        sexpr_form_model(source) matches Some(forms) && match program_model(source, forms, expected) {
            Ok((rows, ty)) => result matches Ok(checked) && checked.rows@ == rows && checked.ty == ty,
            Err(error) => result == Err(error),
        }
    } else {
        result matches Err(IntegerCheckError::Syntax(error)) && strict_syntax_rejection(source, error)
    }
}

/// 単一の整数式を構文と型に照らして検査する。
///
/// 利用者による名前の束縛がない環境を対象とする。
/// 十進リテラル、`add`、`sub`、`mul`、`int-to-nat`、`nat-to-int`、`as-type` を受理する。
/// 各引数には、同じ範囲の整数式を入れ子にして書ける。
/// 期待型のない算術では、引数の結果に関わる型の制約を左から調べる。
/// 制約がなければ `Nat` を選び、違う型の制約が重なれば型エラーを返す。
///
/// # Errors
///
/// 共通の字句・構文、対応する式の形、式全体の期待型を順に検査する。
/// 引数の型やリテラルの検査に失敗した場合は、左の引数を優先してその位置を返す。
pub fn check_integer_expression(source: &str, expected: Option<IntegerType>)
    -> (result: Result<CheckedIntegerExpression, IntegerCheckError>)
    ensures integer_check_matches(source, expected, result),
{
    let forms = match syntax::parse(source) {
        Ok(forms) => forms,
        Err(error) => return Err(IntegerCheckError::Syntax(error)),
    };
    let len = forms.len();
    if len == 0 || subtree_end(forms.as_slice(), 0) != len {
        return Err(IntegerCheckError::UnsupportedExpression(0..source.as_bytes().len()));
    }
    let prepared = describe_nodes(source, forms.as_slice());
    let PreparedNode::Supported { first_constraint: constraint, .. } = prepared[len - 1] else {
        return Err(IntegerCheckError::UnsupportedExpression(0..source.as_bytes().len()));
    };
    let ty = integer_signature(expected, constraint);
    proof { all_description_rows_sound(source, forms@, prepared@); }
    let rows = plan_nodes(source, forms.as_slice(), prepared.as_slice());
    planned_result(&rows[len - 1], ty)?;
    Ok(CheckedIntegerExpression { rows, ty })
}

spec fn root_meaning(rows: Seq<PlannedRow>, ty: IntegerType) -> Option<Meaning>
    recommends rows.len() > 0,
{
    expected_meaning(meaning_prefix(rows, rows.len())[rows.len() - 1], ty)
}

// 型制約は構文木上で決める。型注釈と明示変換の内側は外側の選択に影響しない。
spec fn source_constraint(source: &str, forms: Seq<Form>, at: usize) -> Option<IntegerType>
    decreases forms.len() - at,
{
    if at >= forms.len() || direct_node_model(source, forms, at).is_none() {
        None
    } else {
        let node = direct_node_model(source, forms, at)->Some_0;
        if !node_edges_ordered(node, at, forms.len()) {
            None
        } else {
            match node {
                Node::Literal(leaf) => if leaf.negative { Some(IntegerType::Int) } else { None },
                Node::Convert(ty, _) | Node::Annotate(ty, _) => Some(ty),
                Node::Arithmetic(_, left, right) => {
                    let before = source_constraint(source, forms, left);
                    if before.is_some() { before } else { source_constraint(source, forms, right) }
                }
            }
        }
    }
}

// 型が選ばれた後、部分式が全てその型制約を満たすことを求める。
spec fn source_typeable(source: &str, forms: Seq<Form>, at: usize, ty: IntegerType) -> bool
    decreases forms.len() - at,
{
    if at >= forms.len() || direct_node_model(source, forms, at).is_none() {
        false
    } else {
        let node = direct_node_model(source, forms, at)->Some_0;
        if !node_edges_ordered(node, at, forms.len()) {
            false
        } else {
            match node {
                Node::Literal(_) => checked_literal(source, forms[at as int], ty).is_ok(),
                Node::Arithmetic(_, left, right) =>
                    source_typeable(source, forms, left, ty) && source_typeable(source, forms, right, ty),
                Node::Convert(target, child) => target == ty && source_typeable(source, forms, child, opposite(target)),
                Node::Annotate(target, child) => target == ty && source_typeable(source, forms, child, target),
            }
        }
    }
}

// 参照評価では、左の引数が範囲エラーならその位置を返し、右の参照評価へ進まない。
spec fn source_event(source: &str, forms: Seq<Form>, at: usize, ty: IntegerType) -> Option<Meaning>
    decreases forms.len() - at,
{
    if at >= forms.len() || direct_node_model(source, forms, at).is_none() {
        None
    } else {
        let node = direct_node_model(source, forms, at)->Some_0;
        let span = form_span(forms[at as int]);
        if !node_edges_ordered(node, at, forms.len()) {
            None
        } else {
            match node {
                Node::Literal(_) => match checked_literal(source, forms[at as int], ty) {
                    Ok(IntegerValue::Nat(n)) => Some((IntegerType::Nat, n as int, span)),
                    Ok(IntegerValue::Int(n)) => Some((IntegerType::Int, n as int, span)),
                    Err(_) => None,
                },
                Node::Arithmetic(op, left, right) => match source_event(source, forms, left, ty) {
                    None => None,
                    Some(a) => if !event_fits(a) { Some(a) } else {
                        match source_event(source, forms, right, ty) {
                            None => None,
                            Some(b) => if !event_fits(b) { Some(b) } else {
                                Some((ty, arithmetic_value(op, a.1, b.1), span))
                            },
                        }
                    },
                },
                Node::Convert(target, child) =>
                    unary_meaning(span, target, source_event(source, forms, child, opposite(target))),
                Node::Annotate(target, child) =>
                    unary_meaning(span, target, source_event(source, forms, child, target)),
            }
        }
    }
}

proof fn source_constraint_agrees(source: &str, forms: Seq<Form>, prepared: Seq<PreparedNode>, at: usize)
    requires prepared_row_sound(source, forms, prepared), supported_at(prepared, forms.len(), at),
    ensures source_constraint(source, forms, at) == first_constraint_at(prepared, forms.len(), at),
    decreases forms.len() - at,
{
    let row = prepared[forms.len() - 1 - at];
    let node = row->Supported_node;
    supported_node_is_direct(source, forms, prepared, at, node);
    reveal_with_fuel(source_constraint, 2);
    assert(row == describe_node(Some(node), forms.len(), prepared.take(forms.len() - 1 - at)));
    if let Node::Arithmetic(_, left, right) = node {
        children_are_supported(source, forms, prepared, at, node);
        source_constraint_agrees(source, forms, prepared, left);
        source_constraint_agrees(source, forms, prepared, right);
    }
}

proof fn planned_row_is_model(
    source: &str, forms: Seq<Form>, prepared: Seq<PreparedNode>,
    from: nat, at: nat, rows: Seq<PlannedRow>, ty: IntegerType,
)
    requires
        from <= at < forms.len(),
        rows == planned_suffix(source, forms, prepared, from),
        rows.len() == forms.len() - from,
    ensures
        rows[forms.len() - 1 - at].span == form_span(forms[at as int]),
        planned_for(rows[forms.len() - 1 - at], ty) == plan_one_model(
            source, forms, at as usize, prepared[forms.len() - 1 - at], ty, rows.take(forms.len() - 1 - at),
        ),
    decreases at - from,
{
    reveal_with_fuel(planned_suffix, 2);
    let tail = planned_suffix(source, forms, prepared, from + 1);
    if from == at {
        assert(rows.take(forms.len() - 1 - at) =~= tail);
    } else {
        planned_row_is_model(source, forms, prepared, from + 1, at, tail, ty);
        assert(rows.take(forms.len() - 1 - at) =~= tail.take(forms.len() - 1 - at));
    }
}

proof fn meaning_prefix_size(rows: Seq<PlannedRow>, size: nat)
    requires size <= rows.len(),
    ensures meaning_prefix(rows, size).len() == size,
    decreases size,
{
    if size > 0 {
        meaning_prefix_size(rows, (size - 1) as nat);
        reveal_with_fuel(meaning_prefix, 2);
    }
}

proof fn meaning_prefix_agrees(rows: Seq<PlannedRow>, before: nat, after: nat, index: int)
    requires 0 <= index < before <= after <= rows.len(),
    ensures meaning_prefix(rows, before)[index] == meaning_prefix(rows, after)[index],
    decreases after - before,
{
    if before < after {
        reveal_with_fuel(meaning_prefix, 2);
        let previous = (after - 1) as nat;
        meaning_prefix_agrees(rows, before, previous, index);
        meaning_prefix_size(rows, previous);
        assert(meaning_prefix(rows, previous)[index] == meaning_prefix(rows, after)[index]);
    }
}

proof fn math_row_is_model(rows: Seq<PlannedRow>, index: int, ty: IntegerType)
    requires 0 <= index < rows.len(),
    ensures expected_meaning(meaning_prefix(rows, rows.len())[index], ty) == eval_plan_model(
        planned_for(rows[index], ty), rows[index].span, rows.len(), meaning_prefix(rows, index as nat),
    ),
{
    let prefix = meaning_prefix(rows, index as nat);
    let row = rows[index];
    meaning_prefix_agrees(rows, (index + 1) as nat, rows.len(), index);
    meaning_prefix_size(rows, index as nat);
    reveal_with_fuel(meaning_prefix, 2);
    assert(meaning_prefix(rows, (index + 1) as nat)[index] == (
        eval_plan_model(row.nat, row.span, rows.len(), prefix),
        eval_plan_model(row.signed, row.span, rows.len(), prefix),
    ));
}

proof fn row_counts(source: &str, forms: Seq<Form>, prepared: Seq<PreparedNode>, from: nat)
    requires from <= forms.len(),
    ensures
        described_suffix(source, forms, from).len() == forms.len() - from,
        planned_suffix(source, forms, prepared, from).len() == forms.len() - from,
    decreases forms.len() - from,
{
    reveal_with_fuel(described_suffix, 2);
    reveal_with_fuel(planned_suffix, 2);
    if from < forms.len() {
        row_counts(source, forms, prepared, from + 1);
    }
}

proof fn program_agrees_with_source(
    source: &str, forms: Seq<Form>, prepared: Seq<PreparedNode>, rows: Seq<PlannedRow>,
    at: usize, ty: IntegerType,
)
    requires
        supported_at(prepared, forms.len(), at),
        prepared_row_sound(source, forms, prepared),
        rows == planned_suffix(source, forms, prepared, 0),
        rows.len() == forms.len(),
        planned_for(rows[rows.len() - 1 - at], ty).is_ok(),
    ensures
        source_typeable(source, forms, at, ty),
        source_event(source, forms, at, ty) == child_meaning(meaning_prefix(rows, rows.len()), rows.len(), at, ty),
    decreases forms.len() - at,
{
    let slot = forms.len() - 1 - at;
    let prior = rows.take(slot);
    let node = prepared[slot]->Supported_node;
    supported_node_is_direct(source, forms, prepared, at, node);
    children_are_supported(source, forms, prepared, at, node);
    planned_row_is_model(source, forms, prepared, 0, at as nat, rows, ty);
    math_row_is_model(rows, slot, ty);
    match node {
        Node::Literal(_) => {},
        Node::Arithmetic(_, left, right) => {
            let a = forms.len() - 1 - left;
            let b = forms.len() - 1 - right;
            assert(prior[a] == rows[a] && prior[b] == rows[b]);
            program_agrees_with_source(source, forms, prepared, rows, left, ty);
            program_agrees_with_source(source, forms, prepared, rows, right, ty);
            meaning_prefix_agrees(rows, slot as nat, rows.len(), a);
            meaning_prefix_agrees(rows, slot as nat, rows.len(), b);
        }
        Node::Convert(target, child) | Node::Annotate(target, child) => {
            let index = forms.len() - 1 - child;
            let input_ty = if node is Convert { opposite(target) } else { target };
            assert(prior[index] == rows[index]);
            program_agrees_with_source(source, forms, prepared, rows, child, input_ty);
            meaning_prefix_agrees(rows, slot as nat, rows.len(), index);
        }
    }
}

/// ソース上の結果の型、数学上の値、半開バイト範囲をこの順に返す。
///
/// 範囲エラーになる部分式があれば、左の引数を優先して最初のエラーの値と位置を返す。
/// 構文・型・リテラルの検査に失敗した場合は `None` とする。
pub closed spec fn integer_expression_meaning(source: &str, expected: Option<IntegerType>)
    -> Option<(IntegerType, int, Range<usize>)>
{
    if !well_formed_sexpr(source) {
        None
    } else {
        match sexpr_form_model(source) {
            Some(forms) if forms.len() > 0 && subtree_limit(forms, 0) == forms.len() => {
                let ty = pick_type(expected, source_constraint(source, forms, 0));
                if source_typeable(source, forms, 0, ty) { source_event(source, forms, 0, ty) } else { None }
            }
            _ => None,
        }
    }
}

/// 数学上の値から、型に収まる値または式の範囲付きの評価エラーを定める。
pub open spec fn integer_evaluation_matches(
    ty: IntegerType, value: int, span: Range<usize>, result: Result<IntegerValue, IntegerEvaluationError>,
) -> bool {
    match ty {
        IntegerType::Nat => if 0 <= value <= u64::MAX {
            result matches Ok(IntegerValue::Nat(number)) && number as int == value
        } else {
            result == Err(IntegerEvaluationError { span, ty })
        },
        IntegerType::Int => if i64::MIN <= value <= i64::MAX {
            result matches Ok(IntegerValue::Int(number)) && number as int == value
        } else {
            result == Err(IntegerEvaluationError { span, ty })
        },
    }
}

/// 検査と評価の公開契約をつなぎ、元ソースの数学上の値と評価結果を対応付ける。
pub proof fn integer_check_and_evaluation_agree(
    source: &str, expected: Option<IntegerType>, checked: &CheckedIntegerExpression,
    result: Result<IntegerValue, IntegerEvaluationError>,
)
    requires integer_check_matches(source, expected, Ok(*checked)), checked.evaluation_matches(result),
    ensures integer_expression_meaning(source, expected) matches Some((ty, value, span))
        && integer_evaluation_matches(ty, value, span, result),
{
    let forms = sexpr_form_model(source)->Some_0;
    let prepared = described_suffix(source, forms, 0);
    let rows = checked.rows@;
    let ty = checked.ty;
    assert(program_model(source, forms, expected) == Ok((rows, ty)));
    row_counts(source, forms, prepared, 0);
    all_description_rows_sound(source, forms, prepared);
    source_constraint_agrees(source, forms, prepared, 0);
    program_agrees_with_source(source, forms, prepared, rows, 0, ty);
}

impl CheckedIntegerExpression {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& self.rows@.len() > 0
        &&& plans_ready(self.rows@, self.rows@.len())
        &&& planned_for(self.rows@[self.rows@.len() - 1], self.ty).is_ok()
    }

    /// 組み込みの数学上の値または範囲エラーと、評価結果が対応することを表す。
    pub closed spec fn evaluation_matches(&self, result: Result<IntegerValue, IntegerEvaluationError>) -> bool {
        root_meaning(self.rows@, self.ty) matches Some((ty, value, span))
            && integer_evaluation_matches(ty, value, span, result)
    }

    /// 検査済みの式の値を求める。
    ///
    /// # Errors
    ///
    /// 複数の引数で範囲エラーが起きる場合は左を優先し、失敗した部分式の範囲と型を返す。
    ///
    /// # Examples
    ///
    /// ```
    /// use circuitgame2_core::ncg2m::integer_expression::check_integer_expression;
    /// use circuitgame2_core::ncg2m::integers::{IntegerType, IntegerValue};
    ///
    /// let expr = check_integer_expression("(add 1 -2)", None).unwrap();
    /// assert_eq!(expr.evaluate().unwrap(), IntegerValue::Int(-1));
    /// let expr = check_integer_expression("(sub 0 1)", None).unwrap();
    /// let error = expr.evaluate().unwrap_err();
    /// assert_eq!(error.span, 0..9);
    /// assert_eq!(error.ty, IntegerType::Nat);
    /// let expr = check_integer_expression("(add (sub 0 1) (sub 0 2))", None).unwrap();
    /// assert_eq!(expr.evaluate().unwrap_err().span, 5..14);
    /// ```
    pub fn evaluate(&self) -> (result: Result<IntegerValue, IntegerEvaluationError>)
        ensures self.evaluation_matches(result),
    {
        proof { use_type_invariant(self); }
        let results = eval_rows(self.rows.as_slice());
        let last = self.rows.len() - 1;
        let result = copy_evaluation(&results[last], self.ty);
        assert(result.is_some());
        assert(evaluation_event_matches(result, root_meaning(self.rows@, self.ty)));
        let Some(outcome) = result else { unreachable!() };
        outcome
    }
}

fn pack_nat(read: Result<u64, super::integers::IntegerOutOfRange>, span: Range<usize>)
    -> (result: Result<IntegerValue, IntegerEvaluationError>)
    ensures forall|value: int| #[trigger] nat_result_matches(value, read)
        ==> integer_evaluation_matches(IntegerType::Nat, value, span, result),
{
    match read {
        Ok(value) => Ok(IntegerValue::Nat(value)),
        Err(_) => Err(IntegerEvaluationError { span, ty: IntegerType::Nat }),
    }
}

fn pack_int(read: Result<i64, super::integers::IntegerOutOfRange>, span: Range<usize>)
    -> (result: Result<IntegerValue, IntegerEvaluationError>)
    ensures forall|value: int| #[trigger] int_result_matches(value, read)
        ==> integer_evaluation_matches(IntegerType::Int, value, span, result),
{
    match read {
        Ok(value) => Ok(IntegerValue::Int(value)),
        Err(_) => Err(IntegerEvaluationError { span, ty: IntegerType::Int }),
    }
}

} // verus!
