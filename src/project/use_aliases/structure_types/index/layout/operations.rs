//! 構造体操作の型を検査し、入力上で選ぶビット区間を求める。

use super::{StructureFieldType, StructureLayout, StructureLayoutField, StructureLayouts, StructurePosition};
use core::ops::Range;
use vstd::prelude::*;

#[cfg(verus_only)]
use super::{UseAliases, representation_width, structure_before};
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;
#[cfg(verus_only)]
use vstd::utf8::encode_utf8_decode_utf8;

verus! {

/// フィールド名または変換先の型を指定する構造体操作。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureOperation<'a> {
    /// 型の宣言にあるフィールドを名前で選ぶ。
    Field(&'a str),
    /// ビット列を指定された構造体型として扱う。
    As(StructurePosition),
    /// 構造体を同じ幅のビット列として扱う。
    Raw,
}

/// 型検査後の結果型と入力から取り出す区間。
#[derive(Debug, Eq, PartialEq)]
pub struct TypedStructureOperation {
    /// 構造体型の同一性を保持する結果型。
    pub ty: StructureFieldType,
    /// 入力の最下位ビットを0とする半開区間。
    pub range: Range<u64>,
}

/// 構造体操作の型または幅が適合しない理由。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructureOperationError {
    /// `field` と `raw` には構造体型の入力が必要。
    ExpectedStructure,
    /// `as` にはビット列型の入力が必要。
    ExpectedBits,
    /// 指定位置に対応する構造体が配置表に存在しない。
    UnknownStructure(StructurePosition),
    /// 指定した名前のフィールドが入力の構造体に存在しない。
    UnknownField(StructurePosition),
    /// ビット列の幅が変換先の構造体の総幅と異なる。
    WidthMismatch {
        /// 入力のビット列幅。
        input: u64,
        /// 変換先の総幅。
        expected: u64,
    },
}

impl<'p, 'a> StructureLayout<'p, 'a> {
    /// 指定名と一致する最初のフィールドを返す。
    ///
    /// 名前は大文字と小文字を区別する。配置検査済みの宣言では同名のフィールドは一つまで。
    pub fn field(&self, name: &str) -> (result: Option<&StructureLayoutField<'p, 'a>>)
        ensures self.field_matches(name, result),
    {
        let mut i = 0;
        while i < self.fields.len()
            invariant
                i <= self.fields@.len(),
                forall|j: int| 0 <= j < i ==>
                    (#[trigger] self.fields@[j]).name.spec_bytes() != name.spec_bytes(),
            decreases self.fields@.len() - i,
        {
            let field = &self.fields[i];
            proof { encode_utf8_decode_utf8(field.name@); encode_utf8_decode_utf8(name@); }
            if field.name == name {
                return Some(field);
            }
            i += 1;
        }
        None
    }

    /// フィールド検索が同じ綴りを持つ最初の項目を返すことを表す。
    pub closed spec fn field_matches(&self, name: &str, result: Option<&StructureLayoutField>) -> bool {
        match result {
            Some(field) => exists|i: int| 0 <= i < self.fields@.len()
                && (#[trigger] self.fields@[i]) == *field
                && field.name.spec_bytes() == name.spec_bytes()
                && forall|j: int| 0 <= j < i ==> (#[trigger] self.fields@[j]).name.spec_bytes() != name.spec_bytes(),
            None => forall|i: int| 0 <= i < self.fields@.len() ==>
                (#[trigger] self.fields@[i]).name.spec_bytes() != name.spec_bytes(),
        }
    }
}

impl<'p, 'a> StructureLayouts<'p, 'a> {
    /// 宣言位置に対応する構造体の配置を返す。
    ///
    /// `position` はこの配置表を作ったプロジェクト内の位置。該当する宣言がなければ `None` を返す。
    pub fn get(&self, position: StructurePosition) -> (result: Option<&StructureLayout<'p, 'a>>)
        ensures
            self.layout_matches(position, result),
            result.is_some() <==> (exists|i: int| 0 <= i < self.entries_model().len()
                && (#[trigger] self.entries_model()[i]).position == position),
            result matches Some(layout) ==> {
                &&& layout.width > 0
                &&& self.representation_width_matches(StructureFieldType::Struct(position), layout.width as int)
                &&& forall|i: int| 0 <= i < layout.fields@.len() ==> {
                    let field = #[trigger] layout.fields@[i];
                    &&& field.range.start < field.range.end <= layout.width
                    &&& self.representation_width_matches(field.ty, field.range.end - field.range.start)
                }
            },
    {
        proof { use_type_invariant(self); }
        let entries = self.entries.as_slice();
        let mut first = 0;
        let mut last = entries.len();
        while first < last
            invariant
                first <= last <= entries@.len(),
                entries@ == self.entries@,
                entries@ == self.entries_model(),
                self.layout_entries_valid(),
                forall|i: int| 0 <= i < first ==> structure_before((#[trigger] entries@[i]).position, position),
                forall|i: int| last <= i < entries@.len() ==> structure_before(position, (#[trigger] entries@[i]).position),
            decreases last - first,
        {
            let middle = first + (last - first) / 2;
            let entry = &entries[middle];
            let at = entry.position;
            if at.file < position.file || (at.file == position.file && at.entry < position.entry) {
                assert forall|i: int| 0 <= i <= middle implies
                    structure_before((#[trigger] entries@[i]).position, position) by {
                    if i < middle { assert(structure_before(entries@[i].position, at)); }
                };
                first = middle + 1;
            } else if position.file < at.file || (position.file == at.file && position.entry < at.entry) {
                assert forall|i: int| middle <= i < entries@.len() implies
                    structure_before(position, (#[trigger] entries@[i]).position) by {
                    if i > middle { assert(structure_before(at, entries@[i].position)); }
                };
                last = middle;
            } else {
                assert(self.representation_width_matches(StructureFieldType::Struct(position), entry.width as int));
                assert(exists|i: int| 0 <= i < self.entries_model().len()
                    && (#[trigger] self.entries_model()[i]).position == position) by {
                    assert(self.entries_model()[middle as int].position == position);
                };
                return Some(entry);
            }
        }
        None
    }

    /// 配置の有無が指定した宣言位置に対応することを表す。
    pub closed spec fn layout_matches(&self, position: StructurePosition, result: Option<&StructureLayout>) -> bool {
        match result {
            Some(layout) => layout.position == position && exists|i: int| 0 <= i < self.entries@.len()
                && (#[trigger] self.entries@[i]) == *layout,
            None => forall|i: int| 0 <= i < self.entries@.len() ==> (#[trigger] self.entries@[i]).position != position,
        }
    }

    spec fn structure_field_result(
        &self, position: StructurePosition, name: &str, result: Result<TypedStructureOperation, StructureOperationError>,
    ) -> bool {
        exists|found: Option<&StructureLayout>| #[trigger] self.layout_matches(position, found)
            && match found {
                None => result == Err(StructureOperationError::UnknownStructure(position)),
                Some(layout) => exists|field: Option<&StructureLayoutField>| #[trigger] layout.field_matches(name, field)
                    && match field {
                        None => result == Err(StructureOperationError::UnknownField(position)),
                        Some(field) => result == Ok(TypedStructureOperation { ty: field.ty, range: field.range }),
                    },
            }
    }

    pub(in crate::project::use_aliases) proof fn checked_field_requires_structure(
        &self, name: &str, input: StructureFieldType, checked: TypedStructureOperation,
    )
        requires self.structure_operation_matches(StructureOperation::Field(name), input, Ok(checked)),
        ensures input is Struct,
    {
    }

    proof fn selected_field(
        &self, position: StructurePosition, name: &str, operation: TypedStructureOperation,
    ) -> (selected: (int, int))
        requires self.structure_operation_matches(StructureOperation::Field(name),
            StructureFieldType::Struct(position), Ok(operation)),
        ensures ({
            let (row, i) = selected;
            let entry = self.entries_model()[row];
            &&& 0 <= row < self.entries_model().len() && entry.position == position
            &&& 0 <= i < entry.fields@.len()
            &&& entry.fields@[i].name.spec_bytes() == name.spec_bytes()
            &&& forall|j: int| 0 <= j < i ==> (#[trigger] entry.fields@[j]).name.spec_bytes() != name.spec_bytes()
            &&& operation.ty == entry.fields@[i].ty
            &&& operation.range == entry.fields@[i].range
        }),
    {
        let (layout, field) = choose|layout: &StructureLayout, field: &StructureLayoutField|
            #[trigger] self.layout_matches(position, Some(layout))
            && #[trigger] layout.field_matches(name, Some(field))
            && operation == TypedStructureOperation { ty: field.ty, range: field.range };
        let row = choose|row: int| 0 <= row < self.entries@.len() && (#[trigger] self.entries@[row]) == *layout;
        let i = choose|i: int| 0 <= i < layout.fields@.len() && (#[trigger] layout.fields@[i]) == *field
            && forall|j: int| 0 <= j < i ==> (#[trigger] layout.fields@[j]).name.spec_bytes() != name.spec_bytes();
        (row, i)
    }

    pub(in crate::project::use_aliases) proof fn checked_conversion_operation_type(
        &self, op: StructureOperation, input: StructureFieldType, checked: TypedStructureOperation,
    )
        requires
            !(op is Field),
            self.structure_operation_matches(op, input, Ok(checked)),
        ensures
            op is Raw ==> input is Struct && checked.ty is Bits,
            op matches StructureOperation::As(position) ==> input is Bits && checked.ty == StructureFieldType::Struct(position),
    {
    }

    /// 操作ごとの入力型と、指定した配置から決まる結果型・区間または診断を表す。
    pub closed spec fn structure_operation_matches(
        &self, op: StructureOperation, input: StructureFieldType, result: Result<TypedStructureOperation, StructureOperationError>,
    ) -> bool {
        &&& self.layout_entries_valid()
        &&& match (op, input) {
            (StructureOperation::Field(name), StructureFieldType::Struct(position)) =>
                self.structure_field_result(position, name, result),
            (StructureOperation::Raw, StructureFieldType::Struct(position)) =>
                exists|found: Option<&StructureLayout>| #[trigger] self.layout_matches(position, found)
                    && match found {
                        None => result == Err(StructureOperationError::UnknownStructure(position)),
                        Some(layout) => result == Ok(TypedStructureOperation {
                            ty: StructureFieldType::Bits(layout.width), range: 0..layout.width,
                        }),
                    },
            (StructureOperation::As(position), StructureFieldType::Bits(width)) =>
                exists|found: Option<&StructureLayout>| #[trigger] self.layout_matches(position, found)
                    && match found {
                        None => result == Err(StructureOperationError::UnknownStructure(position)),
                        Some(layout) => if width == layout.width {
                            result == Ok(TypedStructureOperation { ty: StructureFieldType::Struct(position), range: 0..width })
                        } else {
                            result == Err(StructureOperationError::WidthMismatch { input: width, expected: layout.width })
                        },
                    },
            (StructureOperation::As(_), StructureFieldType::Struct(_)) => result == Err(StructureOperationError::ExpectedBits),
            (_, StructureFieldType::Bits(_)) => result == Err(StructureOperationError::ExpectedStructure),
        }
    }

    /// 値の表現に使う幅が、ビット列型または構造体の宣言幅に一致することを表す。
    pub closed spec fn representation_width_matches(&self, ty: StructureFieldType, width: int) -> bool {
        self.layout_entries_valid() && representation_width(self.entries@, ty, width)
    }

    pub(in crate::project::use_aliases) proof fn bits_representation_width(&self, bits: u64, width: int)
        requires self.representation_width_matches(StructureFieldType::Bits(bits), width),
        ensures width == bits,
    {
    }

    pub(in crate::project::use_aliases) proof fn representation_has_layout(&self, position: StructurePosition, width: int)
        requires self.representation_width_matches(StructureFieldType::Struct(position), width),
        ensures exists|i: int| 0 <= i < self.entries_model().len()
            && (#[trigger] self.entries_model()[i]).position == position,
    {
        let i = choose|i: int| 0 <= i < self.entries@.len()
            && (#[trigger] self.entries@[i]).position == position && self.entries@[i].width == width;
        assert(self.entries_model()[i].position == position);
    }

    pub(in crate::project::use_aliases) proof fn unknown_operation_structure_is_missing(
        &self, op: StructureOperation, input: StructureFieldType, position: StructurePosition,
    )
        requires self.structure_operation_matches(op, input, Err(StructureOperationError::UnknownStructure(position))),
        ensures
            (op matches StructureOperation::As(target) && target == position)
                || input == StructureFieldType::Struct(position),
            forall|i: int| 0 <= i < self.entries_model().len()
                ==> (#[trigger] self.entries_model()[i]).position != position,
    {
        reveal(StructureLayouts::layout_matches);
    }

    /// 同じ配置表で同じ型の表現幅が一意に決まることを示す。
    pub proof fn representation_width_agrees(&self, ty: StructureFieldType, a: int, b: int)
        requires
            self.representation_width_matches(ty, a),
            self.representation_width_matches(ty, b),
        ensures a == b,
    {
        if let StructureFieldType::Struct(position) = ty {
            let i = choose|i: int| 0 <= i < self.entries@.len()
                && (#[trigger] self.entries@[i]).position == position && self.entries@[i].width == a;
            let j = choose|j: int| 0 <= j < self.entries@.len()
                && (#[trigger] self.entries@[j]).position == position && self.entries@[j].width == b;
            if i < j {
                assert(structure_before(self.entries@[i].position, self.entries@[j].position));
            } else if j < i {
                assert(structure_before(self.entries@[j].position, self.entries@[i].position));
            }
        }
    }

    /// 同じ配置表で `as` と `raw` が成功したとき、全ビットが元の順で残ることを示す。
    pub proof fn raw_after_as_preserves_bits(
        &self, position: StructurePosition, width: u64, cast: TypedStructureOperation, raw: TypedStructureOperation,
        bits: Seq<bool>,
    )
        requires
            self.structure_operation_matches(StructureOperation::As(position), StructureFieldType::Bits(width), Ok(cast)),
            self.structure_operation_matches(StructureOperation::Raw, cast.ty, Ok(raw)),
            bits.len() == width,
        ensures
            cast.ty == StructureFieldType::Struct(position),
            raw.ty == StructureFieldType::Bits(width),
            cast.range == (0u64..width),
            raw.range == (0u64..width),
            bits.subrange(cast.range.start as int, cast.range.end as int)
                .subrange(raw.range.start as int, raw.range.end as int) == bits,
    {
        reveal(StructureLayouts::structure_operation_matches);
        let cast_layout = choose|found: Option<&StructureLayout>| #[trigger] self.layout_matches(position, found)
            && found is Some && found->Some_0.width == width
            && cast == (TypedStructureOperation { ty: StructureFieldType::Struct(position), range: 0..width });
        let raw_layout = choose|found: Option<&StructureLayout>| #[trigger] self.layout_matches(position, found)
            && found is Some && raw == (TypedStructureOperation {
                ty: StructureFieldType::Bits(found->Some_0.width), range: 0..found->Some_0.width,
            });
        reveal(StructureLayouts::layout_matches);
        assert(self.representation_width_matches(cast.ty, cast_layout->Some_0.width as int));
        assert(self.representation_width_matches(cast.ty, raw_layout->Some_0.width as int));
        self.representation_width_agrees(cast.ty, width as int, raw_layout->Some_0.width as int);
        assert(bits.subrange(0, width as int) =~= bits);
    }

    /// 構造体操作を検査し、結果型と配線を取り出す区間を返す。
    ///
    /// 構造体の宣言位置はこの配置表を作ったプロジェクト内の位置を指定する。
    /// `as` と `raw` は空きビットを含む総幅を返す。`field` は宣言された区間を返す。
    ///
    /// # Examples
    ///
    /// 空きビットのある構造体でも、変換は総幅を保持する。
    ///
    /// ```
    /// use circuitgame2_core::project::{
    ///     SourceSnapshot, StructureFieldType, StructureOperation, StructurePosition,
    ///     check_use_aliases, index_use_targets, parse_circuit_project,
    /// };
    /// let project = parse_circuit_project(&[SourceSnapshot {
    ///     path: "packet.ncg2", revision: 1,
    ///     text: "(struct Packet (width 8) (tag (bits 3) (at 2)))",
    /// }]).unwrap();
    /// let targets = index_use_targets(&project).unwrap();
    /// let aliases = check_use_aliases(&targets).unwrap();
    /// let layouts = aliases.check_structure_types(8).unwrap();
    /// let position = StructurePosition { file: 0, entry: 0 };
    /// let cast = layouts.check_operation(StructureOperation::As(position), StructureFieldType::Bits(8)).unwrap();
    /// let tag = layouts.check_operation(StructureOperation::Field("tag"), cast.ty).unwrap();
    /// let raw = layouts.check_operation(StructureOperation::Raw, cast.ty).unwrap();
    /// assert_eq!(cast.range, 0..8);
    /// assert_eq!(tag.range, 2..5);
    /// assert_eq!(raw.ty, StructureFieldType::Bits(8));
    /// assert_eq!(raw.range, 0..8);
    /// ```
    ///
    /// # Errors
    ///
    /// 入力の型種別を確認し、次に構造体の宣言位置を調べる。
    /// 宣言が見つかったら、フィールド名または変換時の総幅を照合する。
    pub fn check_operation(&self, op: StructureOperation, input: StructureFieldType)
        -> (result: Result<TypedStructureOperation, StructureOperationError>)
        ensures
            self.structure_operation_matches(op, input, result),
            result matches Err(StructureOperationError::WidthMismatch { input: width, .. })
                ==> op is As && input == StructureFieldType::Bits(width),
            (result matches Err(StructureOperationError::UnknownField(_))) ==> op is Field,
            result matches Ok(typed) ==> {
                &&& typed.range.start < typed.range.end
                &&& self.representation_width_matches(typed.ty, typed.range.end - typed.range.start)
                &&& exists|width: int| #[trigger] self.representation_width_matches(input, width)
                    && typed.range.end <= width
                    && (!(op is Field) ==> typed.range.start == 0 && typed.range.end == width)
            },
    {
        match self.check_operation_with_width(op, input) {
            Ok((typed, _)) => Ok(typed),
            Err(error) => Err(error),
        }
    }

    pub(in crate::project::use_aliases) fn check_operation_with_width(&self, op: StructureOperation, input: StructureFieldType)
        -> (result: Result<(TypedStructureOperation, u64), StructureOperationError>)
        ensures
            self.structure_operation_matches(op, input, match result {
                Ok((typed, _)) => Ok(typed),
                Err(error) => Err(error),
            }),
            result matches Err(StructureOperationError::WidthMismatch { input: width, .. })
                ==> op is As && input == StructureFieldType::Bits(width),
            result matches Err(StructureOperationError::UnknownField(_)) ==> op is Field,
            result matches Ok((typed, width)) ==> {
                &&& typed.range.start < typed.range.end <= width
                &&& self.representation_width_matches(input, width as int)
                &&& self.representation_width_matches(typed.ty, typed.range.end - typed.range.start)
                &&& !(op is Field) ==> typed.range.start == 0 && typed.range.end == width
            },
    {
        proof { use_type_invariant(self); }
        match (op, input) {
            (StructureOperation::Field(name), StructureFieldType::Struct(position)) => {
                let Some(layout) = self.get(position) else { return Err(StructureOperationError::UnknownStructure(position)); };
                let Some(field) = layout.field(name) else { return Err(StructureOperationError::UnknownField(position)); };
                assert(self.representation_width_matches(field.ty, field.range.end - field.range.start));
                assert(field.range.end <= layout.width);
                assert(self.structure_field_result(position, name, Ok(TypedStructureOperation {
                    ty: field.ty, range: field.range,
                })));
                Ok((TypedStructureOperation { ty: field.ty, range: field.range.start..field.range.end }, layout.width))
            },
            (StructureOperation::Raw, StructureFieldType::Struct(position)) => {
                let Some(layout) = self.get(position) else { return Err(StructureOperationError::UnknownStructure(position)); };
                assert(self.representation_width_matches(input, layout.width as int));
                assert(self.representation_width_matches(StructureFieldType::Bits(layout.width), layout.width as int));
                Ok((TypedStructureOperation { ty: StructureFieldType::Bits(layout.width), range: 0..layout.width }, layout.width))
            },
            (StructureOperation::As(position), StructureFieldType::Bits(width)) => {
                let Some(layout) = self.get(position) else { return Err(StructureOperationError::UnknownStructure(position)); };
                if width != layout.width {
                    return Err(StructureOperationError::WidthMismatch { input: width, expected: layout.width });
                }
                assert(self.representation_width_matches(input, width as int));
                assert(self.representation_width_matches(StructureFieldType::Struct(position), width as int));
                Ok((TypedStructureOperation { ty: StructureFieldType::Struct(position), range: 0..width }, width))
            },
            (StructureOperation::As(_), StructureFieldType::Struct(_)) => Err(StructureOperationError::ExpectedBits),
            (_, StructureFieldType::Bits(_)) => Err(StructureOperationError::ExpectedStructure),
        }
    }
}

#[cfg(verus_only)]
impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    pub(in crate::project::use_aliases) proof fn checked_field_operations_agree(
        &self, limit: u64, left: &StructureLayouts, right: &StructureLayouts, position: StructurePosition,
        left_name: &str, right_name: &str, first: TypedStructureOperation, second: TypedStructureOperation,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(limit, Ok(*left)),
            self.structure_types_match(limit, Ok(*right)),
            left_name.spec_bytes() == right_name.spec_bytes(),
            left.structure_operation_matches(StructureOperation::Field(left_name), StructureFieldType::Struct(position), Ok(first)),
            right.structure_operation_matches(StructureOperation::Field(right_name), StructureFieldType::Struct(position), Ok(second)),
        ensures first == second,
    {
        let (a, i) = left.selected_field(position, left_name, first);
        let (b, j) = right.selected_field(position, right_name, second);
        self.structure_type_layouts_agree_at(limit, *left, *right, a, b);
        let l = left.entries_model()[a].fields@;
        let r = right.entries_model()[b].fields@;
        if i < j {
            assert(l[i].name.spec_bytes() == r[i].name.spec_bytes());
            assert(r[i].name.spec_bytes() != right_name.spec_bytes());
        } else if j < i {
            assert(l[j].name.spec_bytes() == r[j].name.spec_bytes());
            assert(l[j].name.spec_bytes() != left_name.spec_bytes());
        }
        assert(l[i].ty == r[i].ty && l[i].range == r[i].range);
    }

    /// 同じプロジェクトと幅上限で検査した二つの配置表では、型の表現幅を引き継げる。
    pub(in crate::project::use_aliases) proof fn representation_width_transfers(
        &self, limit: u64, from: &StructureLayouts, to: &StructureLayouts, ty: StructureFieldType, width: int,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(limit, Ok(*from)),
            self.structure_types_match(limit, Ok(*to)),
            from.representation_width_matches(ty, width),
        ensures to.representation_width_matches(ty, width),
    {
        self.checked_layout_entries_are_valid(limit, *to);
        if let StructureFieldType::Struct(position) = ty {
            let a = choose|i: int| 0 <= i < from.entries_model().len()
                && (#[trigger] from.entries_model()[i]).position == position && from.entries_model()[i].width == width;
            self.checked_layout_positions_are_declared(limit, *from);
            assert(self.is_structure_position(position));
            self.checked_layout_contains(limit, *to, position);
            let b = choose|i: int| 0 <= i < to.entries_model().len()
                && (#[trigger] to.entries_model()[i]).position == position;
            self.structure_type_layouts_agree_at(limit, *from, *to, a, b);
            assert(to.entries_model()[b].width == width);
        }
    }

    pub(in crate::project::use_aliases) proof fn representation_widths_agree_across_layouts(
        &self, limit: u64, left: &StructureLayouts, right: &StructureLayouts, ty: StructureFieldType, a: int, b: int,
    )
        requires
            self.can_resolve(),
            self.structure_types_match(limit, Ok(*left)),
            self.structure_types_match(limit, Ok(*right)),
            left.representation_width_matches(ty, a),
            right.representation_width_matches(ty, b),
        ensures a == b,
    {
        if let StructureFieldType::Struct(position) = ty {
            let i = choose|i: int| 0 <= i < left.entries_model().len()
                && (#[trigger] left.entries_model()[i]).position == position && left.entries_model()[i].width == a;
            let j = choose|i: int| 0 <= i < right.entries_model().len()
                && (#[trigger] right.entries_model()[i]).position == position && right.entries_model()[i].width == b;
            self.structure_type_layouts_agree_at(limit, *left, *right, i, j);
        }
    }
}

} // verus!
