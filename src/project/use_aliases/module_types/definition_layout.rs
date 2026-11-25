//! モジュールの左辺を定義順の平坦なビット列に配置する。

use super::{ModuleCallsError, ModuleSelections, UseAliases};
#[cfg(verus_only)]
use super::ModuleCalls;
use crate::netlist::{PortBitLayout, PortBitLayoutError};
use crate::project::{LocatedName, ModuleBodyPosition, ResolvedPortType, StructureTypeError};
#[cfg(verus_only)]
use crate::netlist::{port_bit_layout_port, port_bit_layout_result, port_bit_layout_size};
#[cfg(verus_only)]
use crate::project::{StructureLayouts, location_in_source};
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// 定義スロットの幅と配置を求めるときの診断。
#[derive(Debug)]
pub enum ClockedDefinitionLayoutError<'p, 'a> {
    /// モジュールまたは断片の型や呼び出しに違反がある。
    Calls(ModuleCallsError<'p, 'a>),
    /// 左辺を駆動する式の型が未確定である。
    Unresolved {
        /// 定義スロットの添字。
        slot: usize,
        /// 左辺にある信号名の範囲。
        definition: LocatedName<'p, 'a>,
    },
    /// 定義の幅を求めるために必要な構造体を配置できなかった。
    Structure {
        /// 構造体の幅を最初に必要とした左辺の信号名。
        definition: LocatedName<'p, 'a>,
        /// 構造体の宣言と配置に関する診断。
        reason: StructureTypeError<'p, 'a>,
    },
    /// 左辺にビット範囲を割り当てられなかった。
    Capacity {
        /// 割り当てに失敗した左辺の信号名。
        definition: LocatedName<'p, 'a>,
        /// 定義スロットの添字、幅、または容量に関する診断。
        layout: PortBitLayoutError,
    },
}

impl<'t, 'p, 'a> UseAliases<'t, 'p, 'a> {
    spec fn definition_layout_site(&self, checked: &ModuleSelections, slot: int, site: LocatedName) -> bool {
        let drivers = checked.typed.sources.roots.wiring.drivers;
        &&& 0 <= slot < drivers.definitions@.len()
        &&& location_in_source(site)
        &&& site.span == drivers.definitions@[slot].name.span
        &&& *site.source == self.targets.project_model().sources_model()[drivers.origins@[slot].file as int]
    }

    spec fn definition_bit_width(&self, checked: &ModuleSelections, slot: int, width: u64, layouts: Option<StructureLayouts>) -> bool {
        match checked.types@[slot] {
            Some(signal) => match signal.ty {
                ResolvedPortType::Bits(bits) => width == bits,
                ty @ ResolvedPortType::Struct { .. } =>
                    layouts matches Some(table) && self.layout_port_width_matches(&table, ty, width as int),
            },
            None => false,
        }
    }

    #[verifier::opaque]
    spec fn definition_width_prefix(
        &self, checked: &ModuleSelections, limit: u64, widths: Seq<u64>, layouts: Option<StructureLayouts>,
    ) -> bool {
        &&& widths.len() <= checked.types@.len()
        &&& (layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)))
        &&& forall|slot: int| 0 <= slot < widths.len() ==>
            self.definition_bit_width(checked, slot, #[trigger] widths[slot], layouts)
    }

    proof fn append_definition_width(
        &self, checked: &ModuleSelections, limit: u64, before: Seq<u64>, width: u64,
        previous: Option<StructureLayouts>, layouts: Option<StructureLayouts>,
    )
        requires
            self.definition_width_prefix(checked, limit, before, previous),
            before.len() < checked.types@.len(),
            previous.is_some() ==> previous == layouts,
            layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)),
            self.definition_bit_width(checked, before.len() as int, width, layouts),
        ensures self.definition_width_prefix(checked, limit, before.push(width), layouts),
    {
        reveal(UseAliases::definition_width_prefix);
        let after = before.push(width);
        assert forall|slot: int| 0 <= slot < after.len() implies
            self.definition_bit_width(checked, slot, #[trigger] after[slot], layouts) by {
            if slot < before.len() {
                assert(after[slot] == before[slot]);
                if previous.is_none() {
                    assert(self.definition_bit_width(checked, slot, before[slot], previous));
                    assert(checked.types@[slot]->Some_0.ty is Bits);
                }
            }
        };
    }

    /// 配置と失敗時の診断が、渡された型表の定義順に対応することを表す。
    pub(super) closed spec fn clocked_definition_layout_on_checked(
        &self, checked: &ModuleSelections, limit: u64, capacity: usize,
        result: Result<PortBitLayout, ClockedDefinitionLayoutError>,
    ) -> bool {
        exists|widths: Seq<u64>, layouts: Option<StructureLayouts>|
            #[trigger] self.definition_width_prefix(checked, limit, widths, layouts) && match result {
                Ok(layout) => widths.len() == checked.types@.len() && port_bit_layout_result(widths, capacity, Ok(layout)),
                Err(ClockedDefinitionLayoutError::Unresolved { slot, definition }) =>
                    slot == widths.len() && slot < checked.types@.len()
                    && checked.types@[slot as int].is_none() && self.definition_layout_site(checked, slot as int, definition),
                Err(ClockedDefinitionLayoutError::Structure { definition, reason }) => {
                    let slot = widths.len() as int;
                    &&& layouts.is_none() && slot < checked.types@.len()
                    &&& (checked.types@[slot] matches Some(ty) && ty.ty is Struct)
                    &&& self.definition_layout_site(checked, slot, definition)
                    &&& self.structure_types_match(limit, Err(reason))
                },
                Err(ClockedDefinitionLayoutError::Capacity { definition, layout }) => {
                    let slot = match layout {
                        PortBitLayoutError::ZeroWidth { port } | PortBitLayoutError::CapacityExceeded { port, .. } => port as int,
                    };
                    &&& widths.len() == checked.types@.len()
                    &&& self.definition_layout_site(checked, slot, definition)
                    &&& port_bit_layout_result(widths, capacity, Err(layout))
                },
                Err(ClockedDefinitionLayoutError::Calls(_)) => false,
            }
    }

    /// 同じ型表の定義スロットから、そのビット範囲と幅を取り出す。
    pub(super) proof fn clocked_definition_layout_evidence(
        &self, checked: &ModuleSelections, limit: u64, capacity: usize, layout: &PortBitLayout, slot: usize,
    )
        requires self.clocked_definition_layout_on_checked(checked, limit, capacity, Ok(*layout)),
        ensures
            layout.ranges_model().len() == checked.types@.len(),
            layout.total_bits_model() <= capacity,
            slot < checked.types@.len() ==> {
                let range = layout.ranges_model()[slot as int];
                let width = range.end - range.start;
                &&& range.start < range.end <= layout.total_bits_model()
                &&& match checked.types@[slot as int] {
                    Some(signal) => match signal.ty {
                        ResolvedPortType::Bits(bits) => width == bits,
                        ty @ ResolvedPortType::Struct { .. } => exists|table: StructureLayouts|
                            self.structure_types_match(limit, Ok(table))
                                && #[trigger] self.layout_port_width_matches(&table, ty, width),
                    },
                    None => false,
                }
            },
    {
        let (widths, layouts) = choose|widths: Seq<u64>, layouts: Option<StructureLayouts>|
            #[trigger] self.definition_width_prefix(checked, limit, widths, layouts)
                && widths.len() == checked.types@.len()
                && port_bit_layout_result(widths, capacity, Ok(*layout));
        port_bit_layout_size(widths, capacity, layout);
        if slot < checked.types@.len() {
            reveal(UseAliases::definition_width_prefix);
            port_bit_layout_port(widths, capacity, *layout, slot);
            assert(self.definition_bit_width(checked, slot as int, widths[slot as int], layouts));
        }
    }

    /// すでにある型表を使って、全断片の定義を同じ順序で配置する。
    pub(super) fn place_clocked_definitions(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize, checked: &ModuleSelections<'p, 'a>,
    ) -> (result: Result<PortBitLayout, ClockedDefinitionLayoutError<'p, 'a>>)
        requires self.can_resolve(), self.module_selections_result(owner, limit, Ok(Some(*checked))),
        ensures self.clocked_definition_layout_on_checked(checked, limit, capacity, result),
    {
        let drivers = &checked.typed.sources.roots.wiring.drivers;
        proof {
            self.module_selections_evidence(owner, limit, *checked);
            self.module_selection_type_declarations(owner, limit, *checked);
        }
        let mut layouts = None;
        let mut widths = Vec::new();
        let mut slot = 0;
        assert(self.definition_width_prefix(checked, limit, widths@, layouts)) by {
            reveal(UseAliases::definition_width_prefix);
        };
        while slot < checked.types.len()
            invariant
                self.can_resolve(),
                self.module_drivers_result(owner, limit, Ok(Some(*drivers))),
                *drivers == checked.typed.sources.roots.wiring.drivers,
                slot == widths@.len() <= checked.types@.len() == drivers.definitions@.len(),
                self.definition_width_prefix(checked, limit, widths@, layouts),
                layouts matches Some(table) ==> self.structure_types_match(limit, Ok(table)),
                self.module_types_declared(checked.types@),
            decreases checked.types@.len() - slot,
        {
            let Some(signal) = &checked.types[slot] else {
                let definition = self.source_driver_location(owner, limit, drivers, slot);
                return Err(ClockedDefinitionLayoutError::Unresolved { slot, definition });
            };
            let ghost previous = layouts;
            let width = match signal.ty {
                ResolvedPortType::Bits(bits) => bits,
                ResolvedPortType::Struct { source, form } => {
                    if layouts.is_none() {
                        layouts = match self.check_structure_types(limit) {
                            Ok(table) => Some(table),
                            Err(reason) => {
                                let definition = self.source_driver_location(owner, limit, drivers, slot);
                                return Err(ClockedDefinitionLayoutError::Structure { definition, reason });
                            },
                        };
                    }
                    let Some(table) = layouts.as_ref() else { unreachable!() };
                    self.structure_port_width(source, form, table, limit)
                },
            };
            proof { self.append_definition_width(checked, limit, widths@, width, previous, layouts); }
            widths.push(width);
            slot += 1;
        }
        match PortBitLayout::from_widths(widths.as_slice(), capacity) {
            Ok(layout) => Ok(layout),
            Err(layout @ (PortBitLayoutError::ZeroWidth { port } | PortBitLayoutError::CapacityExceeded { port, .. })) => {
                let definition = self.source_driver_location(owner, limit, drivers, port);
                Err(ClockedDefinitionLayoutError::Capacity { definition, layout })
            },
        }
    }

    /// 配置した幅と診断が、検査済みの定義型と左辺の信号名に対応することを表す。
    pub closed spec fn clocked_definition_layout_result(
        &self, owner: ModuleBodyPosition, limit: u64, capacity: usize,
        result: Result<Option<PortBitLayout>, ClockedDefinitionLayoutError>,
    ) -> bool {
        match result {
            Ok(None) => self.module_calls_result(owner, limit, Ok(None)),
            Err(ClockedDefinitionLayoutError::Calls(error)) => self.module_calls_result(owner, limit, Err(error)),
            _ => exists|checked: ModuleCalls| #[trigger] self.module_calls_result(owner, limit, Ok(Some(checked)))
                && self.clocked_definition_layout_on_checked(&checked.module.expressions, limit, capacity,
                    match result {
                        Ok(Some(layout)) => Ok(layout),
                        Err(error) => Err(error),
                        _ => arbitrary(),
                    }),
        }
    }

    /// モジュール本体と全断片の左辺を、型に従って連続したビット範囲に割り当てる。
    ///
    /// 各範囲の先頭は最下位ビットを指す。範囲外の位置など、モジュール本体が得られない場合は
    /// `Ok(None)` を返す。`capacity` は全定義を合わせたビット数の上限。
    /// この配置は型表の幅を使う。平坦な配線への変換では、ビット選択を含む各式の配線を別途照合する。
    ///
    /// # Errors
    ///
    /// 型と呼び出しを検査し、定義順に未確定の型や構造体の配置を調べる。
    /// 幅がそろった後、範囲を割り当てられなかった最初の左辺を返す。
    pub fn plan_clocked_definitions(&self, owner: ModuleBodyPosition, limit: u64, capacity: usize)
        -> (result: Result<Option<PortBitLayout>, ClockedDefinitionLayoutError<'p, 'a>>)
        requires self.can_resolve(),
        ensures
            self.clocked_definition_layout_result(owner, limit, capacity, result),
            result matches Ok(Some(layout)) ==> layout.total_bits_model() <= capacity,
    {
        let checked = match self.check_module_calls(owner, limit) {
            Ok(Some(checked)) => checked,
            Ok(None) => return Ok(None),
            Err(error) => return Err(ClockedDefinitionLayoutError::Calls(error)),
        };
        proof { self.module_calls_type_evidence(owner, limit, &checked); }
        proof { self.module_output_types_evidence(owner, limit, checked.module); }
        match self.place_clocked_definitions(owner, limit, capacity, &checked.module.expressions) {
            Ok(layout) => {
                proof { self.clocked_definition_layout_evidence(&checked.module.expressions, limit, capacity, &layout, 0); }
                Ok(Some(layout))
            },
            Err(error) => Err(error),
        }
    }
}

} // verus!
