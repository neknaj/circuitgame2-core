//! 評価途中の引数と、補助関数の本体へ渡す値列を扱う。

use alloc::vec::Vec;
use crate::project::{DefnCallEdge, DefnPosition, ProjectSource};
use crate::syntax::Form;
use super::data_types::DefnSignature;
use vstd::prelude::*;

pub mod macro_binding;
pub mod scalar;

verus! {

/// 計画に含まれる補助関数の本体を、元の文書版と構文木から参照する。
pub struct DefnEvaluationBody<'p, 'a> {
    /// 宣言を書いたソースと文書版。
    pub source: &'p ProjectSource<'a>,
    /// プロジェクトの解析時に保持した、宣言を含む構文木。
    pub forms: &'p [Form],
    /// 本体の根の添字。
    pub at: usize,
    /// 仮引数の順序と、各引数および戻り値の型。
    pub signature: DefnSignature<'a>,
}

/// 引数を元の環境で評価した結果列の先頭から、成功した値を取り出したことを表す。
pub open spec fn evaluated_argument_prefix<Value, Error>(
    results: Seq<Result<Value, Error>>, values: Seq<Value>,
) -> bool {
    &&& values.len() <= results.len()
    &&& forall|i: int| 0 <= i < values.len() ==> (#[trigger] results[i]) == Ok(values[i])
}

/// 指定した引数で失敗し、それより左の引数はすべて成功することを表す。
pub open spec fn first_argument_error<Value, Error>(
    results: Seq<Result<Value, Error>>, slot: int, error: Error,
) -> bool {
    &&& 0 <= slot < results.len()
    &&& results[slot] == Err(error)
    &&& forall|i: int| 0 <= i < slot ==> (#[trigger] results[i]).is_ok()
}

/// 呼び出し先に渡す値を、引数ごとに左から受け取る。
pub struct CallArguments<'call, 'p, 'a, Value> {
    edge: &'call DefnCallEdge<'p, 'a>,
    values: Vec<Value>,
}

/// 直下の式をさらに一つ評価するか、得た値を補助関数の本体へ渡す。
pub enum CallArgumentStep<'call, 'p, 'a, Value> {
    /// 次に評価する引数。
    Evaluate(PendingCallArgument<'call, 'p, 'a, Value>),
    /// 引数がすべて評価され、呼び出し先へ渡せる値列。
    Invoke {
        /// これから本体を評価する補助関数。
        callee: DefnPosition,
        /// 署名の引数と同じ位置順の値。
        values: Vec<Value>,
    },
}

/// 評価位置を確定した一つの引数。
pub struct PendingCallArgument<'call, 'p, 'a, Value> {
    waiting: CallArguments<'call, 'p, 'a, Value>,
}

impl<'call, 'p, 'a, Value> CallArguments<'call, 'p, 'a, Value> {
    /// 型検査で記録した呼び出しと、受け取った値の列を表す。
    pub closed spec fn model(&self) -> (&'call DefnCallEdge<'p, 'a>, Seq<Value>) {
        (self.edge, self.values@)
    }

    #[verifier::type_invariant]
    spec fn fits(&self) -> bool {
        self.values@.len() <= self.edge.arguments@.len()
    }

    pub(crate) fn start(edge: &'call DefnCallEdge<'p, 'a>) -> (waiting: Self)
        ensures waiting.model() == (edge, Seq::empty()),
    {
        Self { edge, values: Vec::new() }
    }

    /// 次の引数を選ぶ。値がそろっていれば、呼び出し先に渡す値列を返す。
    pub fn next(self) -> (step: CallArgumentStep<'call, 'p, 'a, Value>)
        ensures match step {
            CallArgumentStep::Evaluate(pending) => {
                &&& pending.model() == self.model()
                &&& self.model().1.len() < self.model().0.arguments@.len()
            }
            CallArgumentStep::Invoke { callee, values } => {
                &&& callee == self.model().0.to
                &&& values@ == self.model().1
                &&& values@.len() == self.model().0.arguments@.len()
            }
        },
    {
        proof { use_type_invariant(&self); }
        if self.values.len() < self.edge.arguments.len() {
            CallArgumentStep::Evaluate(PendingCallArgument { waiting: self })
        } else {
            CallArgumentStep::Invoke { callee: self.edge.to, values: self.values }
        }
    }
}

impl<'call, 'p, 'a, Value> PendingCallArgument<'call, 'p, 'a, Value> {
    /// 呼び出しと、今回の引数より前に受け取った値を表す。
    pub closed spec fn model(&self) -> (&'call DefnCallEdge<'p, 'a>, Seq<Value>) {
        self.waiting.model()
    }

    #[verifier::type_invariant]
    spec fn has_pending(&self) -> bool {
        self.waiting.values@.len() < self.waiting.edge.arguments@.len()
    }

    fn slot(&self) -> (slot: usize)
        ensures slot == self.model().1.len(),
    {
        self.waiting.values.len()
    }

    /// 呼び出し元の保持構文木における、次の引数の添字を返す。
    pub fn expression(&self) -> (at: usize)
        ensures
            self.model().1.len() < self.model().0.arguments@.len(),
            at == self.model().0.arguments@[self.model().1.len() as int],
    {
        proof { use_type_invariant(self); }
        self.waiting.edge.arguments[self.waiting.values.len()]
    }

    /// 引数の添字が指す、呼び出し元のソースと文書版を返す。
    pub fn source(&self) -> (source: &'p ProjectSource<'a>)
        ensures source == self.model().0.call.source,
    {
        self.waiting.edge.call.source
    }

    /// 次の結果を受け取ったとき、成功列が一つ進むか、最初の失敗になることを示す。
    pub proof fn resume_obeys_argument_order<Error>(&self, results: Seq<Result<Value, Error>>)
        requires
            self.model().0.arguments@.len() == results.len(),
            self.model().1.len() < results.len(),
            evaluated_argument_prefix(results, self.model().1),
        ensures {
            let values = self.model().1;
            let slot = values.len() as int;
            match results[slot] {
                Ok(value) => evaluated_argument_prefix(results, values.push(value)),
                Err(error) => first_argument_error(results, slot, error),
            }
        },
    {
        let values = self.model().1;
        let slot = values.len() as int;
        if let Ok(value) = results[slot] {
            let next = values.push(value);
            assert forall|i: int| 0 <= i < next.len() implies (#[trigger] results[i]) == Ok(next[i]) by {
                if i < slot { assert(next[i] == values[i]); }
                else { assert(i == slot && next[i] == value); }
            };
        } else {
            assert forall|i: int| 0 <= i < slot implies (#[trigger] results[i]).is_ok() by {
                assert(results[i] == Ok(values[i]));
            };
        }
    }

    /// 一つの引数の結果を受け取る。失敗は元の診断を保って呼び出し元へ返す。
    pub fn resume<Error>(self, outcome: Result<Value, Error>)
        -> (result: Result<CallArguments<'call, 'p, 'a, Value>, Error>)
        ensures match outcome {
            Ok(value) => result matches Ok(waiting)
                && waiting.model() == (self.model().0, self.model().1.push(value)),
            Err(error) => result == Err(error),
        },
    {
        proof { use_type_invariant(&self); }
        let value = outcome?;
        let CallArguments { edge, mut values } = self.waiting;
        values.push(value);
        Ok(CallArguments { edge, values })
    }
}

}
