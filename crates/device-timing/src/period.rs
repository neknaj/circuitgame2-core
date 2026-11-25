//! 有理数で指定した周期を、マイクロ秒単位のタイマーへ渡す。

#[cfg(not(verus_only))]
use verus_builtin_macros::verus;
#[cfg(verus_only)]
use vstd::prelude::*;

verus! {

/// 正の有理数ナノ秒を、丸めずにマイクロ秒へ変換する。
///
/// 分子または分母が0の場合や、正の整数マイクロ秒で表せない場合は `None` を返す。
pub fn exact_microseconds(numerator: u64, denominator: u64) -> (result: Option<u64>)
    ensures
        result.is_some() <==> numerator > 0 && denominator > 0
            && numerator as int % (denominator as int * 1_000) == 0,
        result matches Some(micros) ==>
            micros > 0 && micros as int * (denominator as int * 1_000) == numerator as int,
{
    if numerator == 0 || denominator == 0 {
        return None;
    }
    // u64 の分母に 1,000 を掛けても u128 に収まる。
    let unit = u128::from(denominator) * 1_000;
    let n = u128::from(numerator);
    let remainder = n % unit;
    if remainder != 0 {
        return None;
    }
    let micros = n / unit;
    proof {
        let u = unit as int;
        let q = micros as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, u);
        vstd::arithmetic::mul::lemma_mul_is_commutative(u, q);
        assert(n as int == q * u + remainder as int);
        assert(remainder == 0);
        assert(0 < q <= n as int) by (nonlinear_arith)
            requires n as int > 0, q >= 0, u >= 1, q * u == n as int;
    }
    Some(micros as u64)
}

} // verus!
