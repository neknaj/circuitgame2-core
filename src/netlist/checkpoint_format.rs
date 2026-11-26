//! スナップショットのバージョンと論理時刻を共通のファイル形式で扱う。

use alloc::vec::Vec;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// 先頭8バイトに識別子と形式バージョンを格納する。
pub const MAGIC: [u8; 8] = *b"NCG2SNP\x01";

/// 識別子・バージョンと、4個の64ビット整数を格納する固定部分の長さ。
pub const CHECKPOINT_HEADER_BYTES: usize = 40;

/// スナップショットの固定部分と配線表のエラー。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CheckpointFileError {
    /// 固定部分が短すぎる。
    ShortHeader,
    /// 識別子またはバージョンが異なる。
    Format,
    /// 周期の分子と分母が規定外である。
    Period,
    /// 保存データが必要な長さと異なる。
    Length,
    /// 展開済みの配線表が復元先と異なる。
    Layout,
    /// 保存データの領域を確保できない。
    Allocation,
}

/// 回路状態と一緒に保存する論理時刻。周期なしは分子・分母ともに0で表す。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckpointHeader {
    /// 最後に確定した reset 世代。
    pub generation: u64,
    /// その世代で最後に確定した tick。
    pub tick: u64,
    /// 1 tick のナノ秒数を表す分子。
    pub period_numerator: u64,
    /// 1 tick のナノ秒数を表す分母。
    pub period_denominator: u64,
}

impl CheckpointHeader {
    /// 周期を省略した状態か、設定で指定できる周期であることを表す。
    pub open spec fn valid(self) -> bool {
        (self.period_numerator == 0 && self.period_denominator == 0)
        || (0 < self.period_numerator <= i64::MAX as u64
            && 0 < self.period_denominator <= i64::MAX as u64)
    }
}

/// バイト列をリトルエンディアンの64ビット値として読む。
pub open spec fn word_at(bytes: Seq<u8>, index: int) -> u64
    recommends 0 <= index && index + 8 <= bytes.len(),
{
    (bytes[index] as u64)
        | ((bytes[index + 1] as u64) << 8)
        | ((bytes[index + 2] as u64) << 16)
        | ((bytes[index + 3] as u64) << 24)
        | ((bytes[index + 4] as u64) << 32)
        | ((bytes[index + 5] as u64) << 40)
        | ((bytes[index + 6] as u64) << 48)
        | ((bytes[index + 7] as u64) << 56)
}

/// 現行形式の識別子と、復号した4個の整数が一致することを表す。
pub open spec fn checkpoint_header_matches(bytes: Seq<u8>, header: CheckpointHeader) -> bool {
    &&& bytes.len() >= CHECKPOINT_HEADER_BYTES
    &&& bytes.take(8) == MAGIC@
    &&& header.generation == word_at(bytes, 8)
    &&& header.tick == word_at(bytes, 16)
    &&& header.period_numerator == word_at(bytes, 24)
    &&& header.period_denominator == word_at(bytes, 32)
    &&& header.valid()
}

fn header_period_is_valid(header: CheckpointHeader) -> (valid: bool)
    ensures valid == header.valid(),
{
    (header.period_numerator == 0 && header.period_denominator == 0)
        || (header.period_numerator > 0 && header.period_denominator > 0
            && header.period_numerator <= i64::MAX as u64
            && header.period_denominator <= i64::MAX as u64)
}

fn read_word(bytes: &[u8], index: usize) -> (word: u64)
    requires index + 8 <= bytes@.len(),
    ensures word == word_at(bytes@, index as int),
{
    (bytes[index] as u64)
        | ((bytes[index + 1] as u64) << 8)
        | ((bytes[index + 2] as u64) << 16)
        | ((bytes[index + 3] as u64) << 24)
        | ((bytes[index + 4] as u64) << 32)
        | ((bytes[index + 5] as u64) << 40)
        | ((bytes[index + 6] as u64) << 48)
        | ((bytes[index + 7] as u64) << 56)
}

/// スナップショットファイルの固定部分を調べる。
///
/// # Errors
///
/// 固定部分の欠落、形式の不一致、不正な周期を区別して返す。
pub fn read_checkpoint_header(bytes: &[u8]) -> (result: Result<CheckpointHeader, CheckpointFileError>)
    ensures
        result matches Ok(header) ==> checkpoint_header_matches(bytes@, header),
        result is Err ==> !(exists|header: CheckpointHeader| #[trigger] checkpoint_header_matches(bytes@, header)),
        (result matches Err(CheckpointFileError::ShortHeader)) <==> bytes@.len() < CHECKPOINT_HEADER_BYTES,
        (result matches Err(CheckpointFileError::Format)) <==>
            bytes@.len() >= CHECKPOINT_HEADER_BYTES && bytes@.take(8) != MAGIC@,
{
    if bytes.len() < CHECKPOINT_HEADER_BYTES {
        return Err(CheckpointFileError::ShortHeader);
    }
    let mut i = 0;
    while i < 8
        invariant
            i <= 8,
            bytes@.len() >= CHECKPOINT_HEADER_BYTES,
            forall|j: int| 0 <= j < i ==> #[trigger] bytes@[j] == MAGIC@[j],
        decreases 8 - i,
    {
        if bytes[i] != MAGIC[i] {
            return Err(CheckpointFileError::Format);
        }
        i += 1;
    }
    assert(bytes@.take(8) =~= MAGIC@);
    let header = CheckpointHeader {
        generation: read_word(bytes, 8),
        tick: read_word(bytes, 16),
        period_numerator: read_word(bytes, 24),
        period_denominator: read_word(bytes, 32),
    };
    if !header_period_is_valid(header) {
        return Err(CheckpointFileError::Period);
    }
    Ok(header)
}

/// ヘッダーの後ろにある配線表が、復元先から作った配線表とバイト単位で一致することを調べる。
///
/// 状態部の長さは復元先から求めた値を渡す。ファイル側の長さに従った確保はしない。
pub fn checkpoint_state<'a>(file: &'a [u8], layout: &[u8], state_len: usize) -> (state: Result<&'a [u8], CheckpointFileError>)
    ensures
        state is Ok <==> file@.len() == CHECKPOINT_HEADER_BYTES + layout@.len() + state_len
            && file@.subrange(CHECKPOINT_HEADER_BYTES as int, CHECKPOINT_HEADER_BYTES + layout@.len()) == layout@,
        state matches Ok(bytes) ==> bytes@ == file@.skip(CHECKPOINT_HEADER_BYTES + layout@.len()),
        (state matches Err(CheckpointFileError::Length)) <==>
            file@.len() != CHECKPOINT_HEADER_BYTES + layout@.len() + state_len,
        (state matches Err(CheckpointFileError::Layout)) <==>
            file@.len() == CHECKPOINT_HEADER_BYTES + layout@.len() + state_len
            && file@.subrange(CHECKPOINT_HEADER_BYTES as int, CHECKPOINT_HEADER_BYTES + layout@.len()) != layout@,
{
    if file.len() < CHECKPOINT_HEADER_BYTES || layout.len() > file.len() - CHECKPOINT_HEADER_BYTES {
        return Err(CheckpointFileError::Length);
    }
    let payload_start = CHECKPOINT_HEADER_BYTES + layout.len();
    if file.len() - payload_start != state_len {
        return Err(CheckpointFileError::Length);
    }
    let mut i = 0;
    while i < layout.len()
        invariant
            i <= layout@.len(),
            file@.len() == CHECKPOINT_HEADER_BYTES + layout@.len() + state_len,
            forall|j: int| 0 <= j < i ==> #[trigger] file@[CHECKPOINT_HEADER_BYTES + j] == layout@[j],
        decreases layout.len() - i,
    {
        if file[CHECKPOINT_HEADER_BYTES + i] != layout[i] {
            return Err(CheckpointFileError::Layout);
        }
        i += 1;
    }
    assert forall|j: int| 0 <= j < layout@.len() implies
        file@.subrange(CHECKPOINT_HEADER_BYTES as int, payload_start as int)[j] == #[trigger] layout@[j] by {
        assert(file@[CHECKPOINT_HEADER_BYTES + j] == layout@[j]);
    }
    assert(file@.subrange(CHECKPOINT_HEADER_BYTES as int, payload_start as int) =~= layout@);
    Ok(slice_subrange(file, payload_start, file.len()))
}


/// 固定部分に使う整数をリトルエンディアンで書く。
pub(super) fn write_word(value: u64) -> (bytes: [u8; 8])
    ensures word_at(bytes@, 0) == value,
{
    proof {
        assert(((value >> 0) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 8) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 16) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 24) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 32) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 40) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 48) & 255u64) <= 255) by (bit_vector);
        assert(((value >> 56) & 255u64) <= 255) by (bit_vector);
    }
    let bytes = [
        ((value >> 0) & 255u64) as u8,
        ((value >> 8) & 255u64) as u8,
        ((value >> 16) & 255u64) as u8,
        ((value >> 24) & 255u64) as u8,
        ((value >> 32) & 255u64) as u8,
        ((value >> 40) & 255u64) as u8,
        ((value >> 48) & 255u64) as u8,
        ((value >> 56) & 255u64) as u8,
    ];
    proof {
        assert(bytes@[0] == ((value >> 0) & 255u64) as u8);
        assert(bytes@[1] == ((value >> 8) & 255u64) as u8);
        assert(bytes@[2] == ((value >> 16) & 255u64) as u8);
        assert(bytes@[3] == ((value >> 24) & 255u64) as u8);
        assert(bytes@[4] == ((value >> 32) & 255u64) as u8);
        assert(bytes@[5] == ((value >> 40) & 255u64) as u8);
        assert(bytes@[6] == ((value >> 48) & 255u64) as u8);
        assert(bytes@[7] == ((value >> 56) & 255u64) as u8);
        assert(bytes@[0] as u64 == (value >> 0) & 255u64);
        assert(bytes@[1] as u64 == (value >> 8) & 255u64);
        assert(bytes@[2] as u64 == (value >> 16) & 255u64);
        assert(bytes@[3] as u64 == (value >> 24) & 255u64);
        assert(bytes@[4] as u64 == (value >> 32) & 255u64);
        assert(bytes@[5] as u64 == (value >> 40) & 255u64);
        assert(bytes@[6] as u64 == (value >> 48) & 255u64);
        assert(bytes@[7] as u64 == (value >> 56) & 255u64);
        assert(word_at(bytes@, 0) == (((value >> 0) & 255u64)
            | ((((value >> 8) & 255u64)) << 8)
            | ((((value >> 16) & 255u64)) << 16)
            | ((((value >> 24) & 255u64)) << 24)
            | ((((value >> 32) & 255u64)) << 32)
            | ((((value >> 40) & 255u64)) << 40)
            | ((((value >> 48) & 255u64)) << 48)
            | ((((value >> 56) & 255u64)) << 56)));
        assert((((value >> 0) & 255u64)
            | ((((value >> 8) & 255u64)) << 8)
            | ((((value >> 16) & 255u64)) << 16)
            | ((((value >> 24) & 255u64)) << 24)
            | ((((value >> 32) & 255u64)) << 32)
            | ((((value >> 40) & 255u64)) << 40)
            | ((((value >> 48) & 255u64)) << 48)
            | ((((value >> 56) & 255u64)) << 56)) == value) by (bit_vector);
    }
    bytes
}

/// 識別子、バージョン、時刻と周期を書き出す。
///
/// 周期が規定外の場合は `None` を返す。
pub fn write_checkpoint_header(header: CheckpointHeader) -> (result: Option<[u8; 40]>)
    ensures result is Some <==> header.valid(),
        result matches Some(bytes) ==> checkpoint_header_matches(bytes@, header),
{
    if !header_period_is_valid(header) {
        return None;
    }
    let generation = write_word(header.generation);
    let tick = write_word(header.tick);
    let period_numerator = write_word(header.period_numerator);
    let period_denominator = write_word(header.period_denominator);
    let bytes = [
        MAGIC[0], MAGIC[1], MAGIC[2], MAGIC[3], MAGIC[4], MAGIC[5], MAGIC[6], MAGIC[7],
        generation[0], generation[1], generation[2], generation[3], generation[4], generation[5], generation[6], generation[7],
        tick[0], tick[1], tick[2], tick[3], tick[4], tick[5], tick[6], tick[7],
        period_numerator[0], period_numerator[1], period_numerator[2], period_numerator[3], period_numerator[4], period_numerator[5], period_numerator[6], period_numerator[7],
        period_denominator[0], period_denominator[1], period_denominator[2], period_denominator[3], period_denominator[4], period_denominator[5], period_denominator[6], period_denominator[7],
    ];
    assert(word_at(bytes@, 8) == header.generation);
    assert(word_at(bytes@, 16) == header.tick);
    assert(word_at(bytes@, 24) == header.period_numerator);
    assert(word_at(bytes@, 32) == header.period_denominator);
    assert(bytes@.take(8) =~= MAGIC@);
    Some(bytes)
}


/// 同じ固定幅の内容を読むと、時刻と周期の復号結果は一意になる。
pub proof fn checkpoint_headers_agree(first: CheckpointHeader, second: CheckpointHeader, bytes: Seq<u8>)
    requires checkpoint_header_matches(bytes, first), checkpoint_header_matches(bytes, second),
    ensures first == second,
{
}

pub(super) fn append_bytes(target: &mut Vec<u8>, source: &[u8])
    requires old(target)@.len() + source@.len() <= isize::MAX,
    ensures final(target)@ == old(target)@ + source@,
{
    let mut i = 0;
    while i < source.len()
        invariant
            i <= source@.len(),
            target@ == old(target)@ + source@.take(i as int),
            old(target)@.len() + source@.len() <= isize::MAX,
        decreases source.len() - i,
    {
        target.push(source[i]);
        assert(source@.take((i + 1) as int) =~= source@.take(i as int).push(source@[i as int]));
        i += 1;
    }
    assert(source@.take(i as int) =~= source@);
}

/// 固定部分、配線表、状態部をこの順で並べる。
///
/// # Errors
///
/// 周期が規定外の場合と保存領域を確保できない場合を区別して返す。
pub fn write_checkpoint_file(header: CheckpointHeader, layout: &[u8], state: &[u8]) -> (result: Result<Vec<u8>, CheckpointFileError>)
    ensures
        result matches Ok(file) ==> checkpoint_header_matches(file@, header)
            && file@.len() == CHECKPOINT_HEADER_BYTES + layout@.len() + state@.len()
            && file@.subrange(CHECKPOINT_HEADER_BYTES as int, CHECKPOINT_HEADER_BYTES + layout@.len()) == layout@
            && file@.skip(CHECKPOINT_HEADER_BYTES + layout@.len()) == state@,
        (result matches Err(CheckpointFileError::Period)) <==> !header.valid(),
{
    let Some(encoded) = write_checkpoint_header(header) else {
        return Err(CheckpointFileError::Period);
    };
    let cap = isize::MAX as usize;
    if layout.len() > cap - CHECKPOINT_HEADER_BYTES
        || state.len() > cap - CHECKPOINT_HEADER_BYTES - layout.len()
    {
        return Err(CheckpointFileError::Allocation);
    }
    let total = CHECKPOINT_HEADER_BYTES + layout.len() + state.len();
    let mut file = Vec::new();
    if file.try_reserve_exact(total).is_err() {
        return Err(CheckpointFileError::Allocation);
    }
    append_bytes(&mut file, encoded.as_slice());
    append_bytes(&mut file, layout);
    append_bytes(&mut file, state);
    assert(file@ == encoded@ + layout@ + state@);
    assert(file@.take(CHECKPOINT_HEADER_BYTES as int) =~= encoded@);
    assert(file@.take(8) =~= MAGIC@);
    assert(word_at(file@, 8) == word_at(encoded@, 8));
    assert(word_at(file@, 16) == word_at(encoded@, 16));
    assert(word_at(file@, 24) == word_at(encoded@, 24));
    assert(word_at(file@, 32) == word_at(encoded@, 32));
    assert(file@.subrange(CHECKPOINT_HEADER_BYTES as int, CHECKPOINT_HEADER_BYTES + layout@.len()) =~= layout@);
    assert(file@.skip(CHECKPOINT_HEADER_BYTES + layout@.len()) =~= state@);
    Ok(file)
}

} // verus!
