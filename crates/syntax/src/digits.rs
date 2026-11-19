use vstd::prelude::*;

verus! {

pub(crate) enum Radix {
    Binary,
    Decimal,
    Hexadecimal,
}

pub(crate) open spec fn digit(radix: Radix, byte: u8) -> bool {
    match radix {
        Radix::Binary => byte == 48 || byte == 49,
        Radix::Decimal => 48 <= byte <= 57,
        Radix::Hexadecimal => 48 <= byte <= 57 || 65 <= byte <= 70 || 97 <= byte <= 102,
    }
}

/// 数値アトムの数字部分に、指定した基数で有効な桁が1つ以上並ぶかを判定する。
pub(crate) fn matches_digits(bytes: &[u8], radix: Radix) -> (result: bool)
    ensures
        result <==> (
            bytes@.len() > 0
            && forall|i: int| 0 <= i < bytes@.len() ==> digit(radix, #[trigger] bytes@[i])
        ),
{
    if bytes.len() == 0 {
        return false;
    }
    let mut i = 0;
    while i < bytes.len()
        invariant
            0 <= i <= bytes@.len(),
            bytes@.len() > 0,
            forall|j: int| 0 <= j < i ==> digit(radix, #[trigger] bytes@[j]),
        decreases bytes@.len() - i,
    {
        let byte = bytes[i];
        let valid = match radix {
            Radix::Binary => byte == b'0' || byte == b'1',
            Radix::Decimal => b'0' <= byte && byte <= b'9',
            Radix::Hexadecimal => {
                (b'0' <= byte && byte <= b'9')
                    || (b'A' <= byte && byte <= b'F')
                    || (b'a' <= byte && byte <= b'f')
            }
        };
        assert(valid == digit(radix, bytes@[i as int]));
        if !valid {
            assert(!(forall|j: int| 0 <= j < bytes@.len() ==> digit(radix, #[trigger] bytes@[j])));
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
