//! 一つのフィールドの範囲と、先行フィールドとの衝突を検査する。

use super::StructureLayoutField;
use core::ops::Range;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

pub(super) enum FieldConflict {
    Name(usize),
    Overlap(usize),
    Outside,
}

pub(super) open spec fn overlaps(a: Range<u64>, b: Range<u64>) -> bool {
    a.start < b.end && b.start < a.end
}

pub(super) open spec fn field_range_matches(offset: u64, width: u64, range: Range<u64>) -> bool {
    range.start == offset && range.end == offset + width
}

pub(super) open spec fn conflicts(a: StructureLayoutField, name: &str, range: Range<u64>) -> bool {
    a.name.spec_bytes() == name.spec_bytes() || overlaps(a.range, range)
}

pub(super) open spec fn placement_matches(
    total: u64, prior: Seq<StructureLayoutField>, name: &str, offset: u64, width: u64,
    result: Result<Range<u64>, FieldConflict>,
) -> bool {
    if offset + width > total {
        result matches Err(FieldConflict::Outside)
    } else {
        match result {
            Err(FieldConflict::Outside) => false,
            Ok(range) => field_range_matches(offset, width, range)
                && forall|i: int| 0 <= i < prior.len() ==> !conflicts(#[trigger] prior[i], name, range),
            Err(error) => {
                let range = offset..((offset + width) as u64);
                let i = if error is Name { error->Name_0 } else { error->Overlap_0 } as int;
                &&& 0 <= i < prior.len()
                &&& match error {
                    FieldConflict::Name(_) => prior[i].name.spec_bytes() == name.spec_bytes(),
                    FieldConflict::Overlap(_) => prior[i].name.spec_bytes() != name.spec_bytes()
                        && overlaps(prior[i].range, range),
                    _ => false,
                }
                &&& forall|j: int| 0 <= j < i ==> !conflicts(#[trigger] prior[j], name, range)
            },
        }
    }
}

pub(super) fn check_field_placement(
    total: u64, prior: &[StructureLayoutField], name: &str, offset: u64, width: u64,
) -> (result: Result<Range<u64>, FieldConflict>)
    requires 0 < width,
    ensures
        placement_matches(total, prior@, name, offset, width, result),
        result matches Ok(range) ==> range.start < range.end <= total,
        result matches Err(FieldConflict::Name(i) | FieldConflict::Overlap(i)) ==> i < prior@.len(),
{
    if offset > total || width > total - offset {
        return Err(FieldConflict::Outside);
    }
    let range = offset..offset + width;
    let mut i = 0;
    while i < prior.len()
        invariant
            offset + width <= total,
            field_range_matches(offset, width, range),
            i <= prior@.len(),
            forall|j: int| 0 <= j < i ==> !conflicts(#[trigger] prior@[j], name, range),
        decreases prior@.len() - i,
    {
        let field = &prior[i];
        proof { encode_utf8_decode_utf8(field.name@); encode_utf8_decode_utf8(name@); }
        if field.name == name {
            return Err(FieldConflict::Name(i));
        }
        if field.range.start < range.end && range.start < field.range.end {
            return Err(FieldConflict::Overlap(i));
        }
        i += 1;
    }
    Ok(range)
}

// 総幅が u64 の最大値でも、末端の有効なビットとその次の位置を区別できる。
proof fn placement_at_upper_bound() {
    let empty = Seq::<StructureLayoutField>::empty();
    let start = (u64::MAX - 1) as u64;
    assert(placement_matches(u64::MAX, empty, "last", start, 1, Ok(start..u64::MAX)));
    assert(placement_matches(u64::MAX, empty, "outside", u64::MAX, 1, Err(FieldConflict::Outside)));
}

} // verus!
