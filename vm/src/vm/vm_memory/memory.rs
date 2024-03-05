use crate::stdlib::{borrow::Cow, collections::HashMap, fmt, prelude::*};

use crate::vm::runners::cairo_pie::CairoPieMemory;
use crate::{
    types::relocatable::{MaybeRelocatable, Relocatable},
    utils::from_relocatable_to_indexes,
    vm::errors::memory_errors::MemoryError,
};
use bitvec::prelude as bv;
use core::cmp::Ordering;
use felt::Felt252;
use num_traits::ToPrimitive;

pub struct ValidationRule(
    #[allow(clippy::type_complexity)]
    pub  Box<dyn Fn(&Memory, Relocatable) -> Result<Vec<Relocatable>, MemoryError>>,
);

// #[derive(Clone, Eq, Ord, PartialEq, PartialOrd, Debug)]
// pub(crate) struct MemoryCell(MaybeRelocatable, bool);

// impl MemoryCell {
//     pub fn new(value: MaybeRelocatable) -> Self {
//         MemoryCell(value, false)
//     }

//     pub fn mark_accessed(&mut self) {
//         self.1 = true
//     }

//     pub fn is_accessed(&self) -> bool {
//         self.1
//     }

//     pub fn get_value(&self) -> &MaybeRelocatable {
//         &self.0
//     }

//     pub fn get_value_mut(&mut self) -> &mut MaybeRelocatable {
//         &mut self.0
//     }
// }

pub struct AddressSet(Vec<bv::BitVec>);

impl AddressSet {
    pub(crate) fn new() -> Self {
        Self(Vec::new())
    }

    pub(crate) fn contains(&self, addr: &Relocatable) -> bool {
        let segment = addr.segment_index;
        if segment.is_negative() {
            return false;
        }

        self.0
            .get(segment as usize)
            .and_then(|segment| segment.get(addr.offset))
            .map(|bit| *bit)
            .unwrap_or(false)
    }

    pub(crate) fn extend(&mut self, addresses: &[Relocatable]) {
        for addr in addresses {
            let segment = addr.segment_index;
            if segment.is_negative() {
                continue;
            }
            let segment = segment as usize;
            if segment >= self.0.len() {
                self.0.resize(segment + 1, bv::BitVec::new());
            }

            let offset = addr.offset;
            if offset >= self.0[segment].len() {
                self.0[segment].resize(offset + 1, false);
            }
            self.0[segment].replace(offset, true);
        }
    }
}

#[cfg(test)]
impl AddressSet {
    pub(crate) fn len(&self) -> usize {
        self.0
            .iter()
            .map(|segment| segment.iter().map(|bit| *bit as usize).sum::<usize>())
            .sum()
    }
}

#[derive(Debug, Default, PartialEq)]
pub(crate) struct MemorySegment {
    present: bv::BitVec,
    cells: Vec<Cell>,
    accessed: bv::BitVec,

    felts: Felts,
}

impl MemorySegment {
    pub fn get(&self, offset: usize) -> Option<MaybeRelocatableRef<'_>> {
        if self.present.get(offset).map(|b| b == true).unwrap_or(false) {
            match self.cells[offset] {
                Cell::RelocatableValue(value) => Some(MaybeRelocatableRef::RelocatableValue(value)),
                Cell::IntIndex(idx) => self.felts.get(idx).map(MaybeRelocatableRef::IntRef),
            }
        } else {
            None
        }
    }

    fn set(&mut self, offset: usize, val: MaybeRelocatable) -> Result<(), MemorySegmentError> {
        if self.present[offset] {
            let equals = match &self.cells[offset] {
                Cell::RelocatableValue(v) => match &val {
                    MaybeRelocatable::RelocatableValue(o) => v == o,
                    MaybeRelocatable::Int(_) => false,
                },
                Cell::IntIndex(idx) => match &val {
                    MaybeRelocatable::RelocatableValue(_) => false,
                    MaybeRelocatable::Int(felt) => self.felts.get(*idx).unwrap() == felt,
                },
            };
            if !equals {
                return Err(MemorySegmentError::InconsistentMemory(Box::new((
                    offset,
                    self.get(offset).unwrap().clone().into(),
                    val,
                ))));
            }
        } else {
            match val {
                MaybeRelocatable::RelocatableValue(relocatable) => {
                    self.cells[offset] = Cell::RelocatableValue(relocatable)
                }
                MaybeRelocatable::Int(felt) => {
                    let idx = self.felts.push(felt);
                    self.cells[offset] = Cell::IntIndex(idx)
                }
            }

            self.present.set(offset, true);
        }

        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn new(values: &[Option<MaybeRelocatable>]) -> Self {
        let mut segment = Self::default();
        segment.resize(values.len());
        for (offset, value) in values.iter().enumerate() {
            if let Some(value) = value {
                segment.set(offset, value.clone()).unwrap();
            }
        }
        segment
    }

    pub fn len(&self) -> usize {
        self.cells.len()
    }

    fn capacity(&self) -> usize {
        self.cells.capacity()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.cells.try_reserve(additional)?;
        self.present.reserve(additional);
        self.accessed.reserve(additional);
        Ok(())
    }

    fn reserve_exact(&mut self, additional: usize) {
        self.present.reserve_exact(additional);
        self.accessed.reserve_exact(additional);
        self.cells.reserve_exact(additional);
    }

    fn resize(&mut self, new_len: usize) {
        self.present.resize(new_len, false);
        self.accessed.resize(new_len, false);
        self.cells.resize(new_len, Default::default());
    }

    fn mark_accessed(&mut self, offset: usize) {
        if self.present.get(offset).map(|b| b == true).unwrap_or(false) {
            self.accessed.set(offset, true);
        }
    }

    #[cfg(test)]
    pub fn is_accessed(&self, offset: usize) -> bool {
        self.accessed
            .get(offset)
            .map(|b| b == true)
            .unwrap_or(false)
    }

    fn num_accessed(&self) -> usize {
        self.accessed.count_ones()
    }

    fn is_present(&self, offset: usize) -> bool {
        self.present.get(offset).map(|b| b == true).unwrap_or(false)
    }

    fn relocate_addresses(&mut self, relocation_rules: &HashMap<usize, Relocatable>) {
        for i in 0..self.len() {
            if self.present[i] {
                match &mut self.cells[i] {
                    Cell::RelocatableValue(r) => *r = relocate_address(*r, relocation_rules),
                    Cell::IntIndex(_) => {}
                }
            }
        }
    }

    fn append_to_pie(&self, segment_index: usize, pie_memory: &mut CairoPieMemory) {
        for i in 0..self.len() {
            if let Some(value) = self.get(i) {
                pie_memory.push(((segment_index, i), value.into()));
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn assert_equals(&self, values: &[Option<MaybeRelocatable>]) {
        for (offset, value) in values.iter().enumerate() {
            assert_eq!(*value, self.get(offset).map(Into::into));
        }
    }

    pub fn iter(&self) -> SegmentIter<'_> {
        SegmentIter {
            segment: self,
            index: 0,
        }
    }

    pub fn load_felts(&mut self, offset: usize, data: &[Felt252]) -> Result<usize, MemoryError> {
        if data.is_empty() {
            return Ok(self.len());
        }

        let current_len = self.len();
        let end = offset + data.len();

        if (offset..end).any(|i| self.is_present(i)) {
            return Err(MemoryError::InconsistentMemoryLoad);
        }

        let new_len = current_len.max(end);
        let mut current_felt_index = self.felts.0.len();
        let next_felt_index = current_felt_index + data.len();

        self.present.resize(new_len, true);
        self.accessed.resize(new_len, false);
        self.felts.0.extend_from_slice(data);

        // first part: overwrite already existing cells
        for i in offset..current_len.min(end) {
            self.cells[i] = Cell::IntIndex(current_felt_index);
            self.present.set(i, true);
            current_felt_index += 1;
        }
        if current_len < end {
            self.cells.extend(
                (current_felt_index..next_felt_index)
                    .into_iter()
                    .map(|idx| Cell::IntIndex(idx)),
            );
        }

        Ok(end)
    }
}

impl<'a> IntoIterator for &'a MemorySegment {
    type Item = Option<MaybeRelocatableRef<'a>>;

    type IntoIter = SegmentIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Debug, thiserror_no_std::Error)]
pub enum MemorySegmentError {
    #[error("Inconsistent memory assignment at offset {:?}. {:?} != {:?}", (*.0).0, (*.0).1, (*.0).2)]
    InconsistentMemory(Box<(usize, MaybeRelocatable, MaybeRelocatable)>),
}

#[derive(Debug, Clone, PartialEq)]
enum Cell {
    RelocatableValue(Relocatable),
    IntIndex(usize),
}

impl Default for Cell {
    fn default() -> Self {
        Self::RelocatableValue(Relocatable {
            segment_index: 0,
            offset: 0,
        })
    }
}

#[derive(Debug, Default, PartialEq)]
struct Felts(Vec<Felt252>);

impl Felts {
    fn push(&mut self, value: Felt252) -> usize {
        let index = self.0.len();
        self.0.push(value);
        index
    }

    fn get(&self, index: usize) -> Option<&Felt252> {
        self.0.get(index)
    }

    // fn get_mut(&mut self, index: usize) -> Option<&mut Felt252> {
    //     self.0.get_mut(index)
    // }
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum MaybeRelocatableRef<'a> {
    RelocatableValue(Relocatable),
    IntRef(&'a Felt252),
}

impl<'a> MaybeRelocatableRef<'a> {
    pub fn get_int_ref(&self) -> Option<&'a Felt252> {
        match self {
            MaybeRelocatableRef::RelocatableValue(_) => None,
            MaybeRelocatableRef::IntRef(int) => Some(*int),
        }
    }
}

impl<'a> From<MaybeRelocatableRef<'a>> for MaybeRelocatable {
    fn from(value: MaybeRelocatableRef<'a>) -> Self {
        match value {
            MaybeRelocatableRef::RelocatableValue(relocatable) => {
                MaybeRelocatable::RelocatableValue(relocatable)
            }
            MaybeRelocatableRef::IntRef(int) => MaybeRelocatable::Int(int.clone()),
        }
    }
}

impl<'a> std::fmt::Display for MaybeRelocatableRef<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MaybeRelocatableRef::RelocatableValue(rel) => rel.fmt(f),
            MaybeRelocatableRef::IntRef(num) => write!(f, "{num}"),
        }
    }
}

pub(crate) struct SegmentIter<'a> {
    segment: &'a MemorySegment,
    index: usize,
}

impl<'a> Iterator for SegmentIter<'a> {
    type Item = Option<MaybeRelocatableRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.segment.len() {
            return None;
        }
        self.index += 1;
        Some(self.segment.get(self.index - 1))
    }
}

// Version of Memory.relocate_value() that doesn't require a self reference
fn relocate_address(
    addr: Relocatable,
    relocation_rules: &HashMap<usize, Relocatable>,
) -> Relocatable {
    let segment_idx = addr.segment_index;
    if segment_idx >= 0 {
        return addr;
    }

    // Adjust the segment index to begin at zero, as per the struct field's
    match relocation_rules.get(&(-(segment_idx + 1) as usize)) {
        Some(x) => x + addr.offset,
        None => addr,
    }
}

pub struct Memory {
    pub(crate) data: Vec<MemorySegment>,
    pub(crate) temp_data: Vec<MemorySegment>,
    // relocation_rules's keys map to temp_data's indices and therefore begin at
    // zero; that is, segment_index = -1 maps to key 0, -2 to key 1...
    pub(crate) relocation_rules: HashMap<usize, Relocatable>,
    pub validated_addresses: AddressSet,
    validation_rules: Vec<Option<ValidationRule>>,
}

impl Memory {
    pub fn new() -> Memory {
        Memory {
            data: Default::default(),
            temp_data: Default::default(),
            relocation_rules: HashMap::new(),
            validated_addresses: AddressSet::new(),
            validation_rules: Vec::with_capacity(7),
        }
    }

    /// Inserts a value into a memory address
    /// Will return an Error if the segment index given by the address corresponds to a non-allocated segment,
    /// or if the inserted value is inconsistent with the current value at the memory cell
    /// If the address isnt contiguous with previously inserted data, memory gaps will be represented by None values
    pub fn insert<V>(&mut self, key: Relocatable, val: V) -> Result<(), MemoryError>
    where
        MaybeRelocatable: From<V>,
    {
        let val = MaybeRelocatable::from(val);
        let (value_index, value_offset) = from_relocatable_to_indexes(key);

        let data = if key.segment_index.is_negative() {
            &mut self.temp_data
        } else {
            &mut self.data
        };

        let data_len = data.len();
        let segment = data
            .get_mut(value_index)
            .ok_or_else(|| MemoryError::UnallocatedSegment(Box::new((value_index, data_len))))?;

        //Check if the element is inserted next to the last one on the segment
        //Forgoing this check would allow data to be inserted in a different index
        let (len, capacity) = (segment.len(), segment.capacity());
        if len <= value_offset {
            let new_len = value_offset
                .checked_add(1)
                .ok_or(MemoryError::VecCapacityExceeded)?;
            segment
                .try_reserve(new_len.saturating_sub(capacity))
                .map_err(|_| MemoryError::VecCapacityExceeded)?;
            segment.resize(new_len);
        }
        // At this point there's *something* in there

        segment.set(value_offset, val).map_err(|e| match e {
            MemorySegmentError::InconsistentMemory(e) => {
                MemoryError::InconsistentMemory(Box::new((key, e.1, e.2)))
            }
        })?;
        self.validate_memory_cell(key)
    }

    /// Retrieve a value from memory (either normal or temporary) and apply relocation rules
    pub(crate) fn get<'a, 'b: 'a, K: 'a>(&'b self, key: &'a K) -> Option<Cow<MaybeRelocatable>>
    where
        Relocatable: TryFrom<&'a K>,
    {
        let relocatable: Relocatable = key.try_into().ok()?;

        let data = if relocatable.segment_index.is_negative() {
            &self.temp_data
        } else {
            &self.data
        };
        let (i, j) = from_relocatable_to_indexes(relocatable);
        let segment = data.get(i)?;
        let value = self.relocate_value(segment.get(j)?);
        let value: MaybeRelocatable = value.into();
        Some(Cow::Owned(value))
    }

    /// Relocates the memory according to the relocation rules and clears `self.relocaction_rules`.
    pub fn relocate_memory(&mut self) -> Result<(), MemoryError> {
        if self.relocation_rules.is_empty() || self.temp_data.is_empty() {
            return Ok(());
        }
        // Relocate temporary addresses in memory
        for segment in self.data.iter_mut().chain(self.temp_data.iter_mut()) {
            segment.relocate_addresses(&self.relocation_rules);
        }
        // Move relocated temporary memory into the real memory
        for index in (0..self.temp_data.len()).rev() {
            if let Some(base_addr) = self.relocation_rules.get(&index) {
                let data_segment = self.temp_data.remove(index);
                // Insert the to-be relocated segment into the real memory
                let mut addr = *base_addr;
                if let Some(s) = self.data.get_mut(addr.segment_index as usize) {
                    s.reserve_exact(data_segment.len())
                }
                for i in 0..data_segment.len() {
                    if let Some(value) = data_segment.get(i) {
                        self.insert(addr, value)?;
                    }
                    addr = (addr + 1)?;
                }
            }
        }
        self.relocation_rules.clear();
        Ok(())
    }

    /// Add a new relocation rule.
    ///
    /// Will return an error if any of the following conditions are not met:
    ///   - Source address's segment must be negative (temporary).
    ///   - Source address's offset must be zero.
    ///   - There shouldn't already be relocation at the source segment.
    pub(crate) fn add_relocation_rule(
        &mut self,
        src_ptr: Relocatable,
        dst_ptr: Relocatable,
    ) -> Result<(), MemoryError> {
        if src_ptr.segment_index >= 0 {
            return Err(MemoryError::AddressNotInTemporarySegment(
                src_ptr.segment_index,
            ));
        }
        if src_ptr.offset != 0 {
            return Err(MemoryError::NonZeroOffset(src_ptr.offset));
        }

        // Adjust the segment index to begin at zero, as per the struct field's
        // comment.
        let segment_index = -(src_ptr.segment_index + 1) as usize;
        if self.relocation_rules.contains_key(&segment_index) {
            return Err(MemoryError::DuplicatedRelocation(src_ptr.segment_index));
        }

        self.relocation_rules.insert(segment_index, dst_ptr);
        Ok(())
    }

    /// Gets the value from memory address as a Felt252 value.
    /// Returns an Error if the value at the memory address is missing or not a Felt252.
    pub fn get_integer(&self, key: Relocatable) -> Result<Cow<Felt252>, MemoryError> {
        match self
            .get(&key)
            .ok_or_else(|| MemoryError::UnknownMemoryCell(Box::new(key)))?
        {
            Cow::Borrowed(MaybeRelocatable::Int(int)) => Ok(Cow::Borrowed(int)),
            Cow::Owned(MaybeRelocatable::Int(int)) => Ok(Cow::Owned(int)),
            _ => Err(MemoryError::ExpectedInteger(Box::new(key))),
        }
    }

    /// Gets the value from memory address as a Relocatable value.
    /// Returns an Error if the value at the memory address is missing or not a Relocatable.
    pub fn get_relocatable(&self, key: Relocatable) -> Result<Relocatable, MemoryError> {
        match self
            .get(&key)
            .ok_or_else(|| MemoryError::UnknownMemoryCell(Box::new(key)))?
        {
            Cow::Borrowed(MaybeRelocatable::RelocatableValue(rel)) => Ok(*rel),
            Cow::Owned(MaybeRelocatable::RelocatableValue(rel)) => Ok(rel),
            _ => Err(MemoryError::ExpectedRelocatable(Box::new(key))),
        }
    }

    /// Inserts a value into memory
    /// Returns an error if the memory cell asignment is invalid
    pub fn insert_value<T: Into<MaybeRelocatable>>(
        &mut self,
        key: Relocatable,
        val: T,
    ) -> Result<(), MemoryError> {
        self.insert(key, &val.into())
    }

    pub fn add_validation_rule(&mut self, segment_index: usize, rule: ValidationRule) {
        if segment_index >= self.validation_rules.len() {
            // Fill gaps
            self.validation_rules
                .resize_with(segment_index + 1, || None);
        }
        self.validation_rules.insert(segment_index, Some(rule));
    }

    fn validate_memory_cell(&mut self, addr: Relocatable) -> Result<(), MemoryError> {
        if let Some(Some(rule)) = addr
            .segment_index
            .to_usize()
            .and_then(|x| self.validation_rules.get(x))
        {
            if !self.validated_addresses.contains(&addr) {
                self.validated_addresses
                    .extend(rule.0(self, addr)?.as_slice());
            }
        }
        Ok(())
    }

    ///Applies validation_rules to the current memory
    pub fn validate_existing_memory(&mut self) -> Result<(), MemoryError> {
        for (index, rule) in self.validation_rules.iter().enumerate() {
            if index >= self.data.len() {
                continue;
            }
            let Some(rule) = rule else {
                continue;
            };
            for offset in 0..self.data[index].len() {
                let addr = Relocatable::from((index as isize, offset));
                if !self.validated_addresses.contains(&addr) {
                    self.validated_addresses
                        .extend(rule.0(self, addr)?.as_slice());
                }
            }
        }
        Ok(())
    }

    /// Compares two ranges of values in memory of length `len`
    /// Returns the ordering and the first relative position at which they differ
    /// Special cases:
    /// - `lhs` exists in memory but `rhs` doesn't -> (Ordering::Greater, 0)
    /// - `rhs` exists in memory but `lhs` doesn't -> (Ordering::Less, 0)
    /// - None of `lhs` or `rhs` exist in memory -> (Ordering::Equal, 0)
    /// Everything else behaves much like `memcmp` in C.
    /// This is meant as an optimization for hints to avoid allocations.
    pub(crate) fn memcmp(
        &self,
        lhs: Relocatable,
        rhs: Relocatable,
        len: usize,
    ) -> (Ordering, usize) {
        let get_segment = |idx: isize| {
            if idx.is_negative() {
                self.temp_data.get(-(idx + 1) as usize)
            } else {
                self.data.get(idx as usize)
            }
        };
        match (
            get_segment(lhs.segment_index),
            get_segment(rhs.segment_index),
        ) {
            (None, None) => {
                return (Ordering::Equal, 0);
            }
            (Some(_), None) => {
                return (Ordering::Greater, 0);
            }
            (None, Some(_)) => {
                return (Ordering::Less, 0);
            }
            (Some(lhs_segment), Some(rhs_segment)) => {
                let (lhs_start, rhs_start) = (lhs.offset, rhs.offset);
                for i in 0..len {
                    let (lhs, rhs) = (
                        lhs_segment.get(lhs_start + i),
                        rhs_segment.get(rhs_start + i),
                    );
                    let ord = lhs.cmp(&rhs);
                    if ord == Ordering::Equal {
                        continue;
                    }
                    return (ord, i);
                }
            }
        };
        (Ordering::Equal, len)
    }

    pub(crate) fn mem_eq(&self, lhs: Relocatable, rhs: Relocatable, len: usize) -> bool {
        self.memcmp(lhs, rhs, len) == (Ordering::Equal, len)
    }

    /// Gets a range of memory values from addr to addr + size
    /// The outputed range may contain gaps if the original memory has them
    pub fn get_range(&self, addr: Relocatable, size: usize) -> Vec<Option<Cow<MaybeRelocatable>>> {
        let mut values = Vec::new();

        for i in 0..size {
            values.push((addr + i).ok().and_then(|x| self.get(&x)));
        }

        values
    }

    /// Gets a range of memory values from addr to addr + size
    /// Fails if there if any of the values inside the range is missing (memory gap)
    pub fn get_continuous_range(
        &self,
        addr: Relocatable,
        size: usize,
    ) -> Result<Vec<MaybeRelocatable>, MemoryError> {
        let mut values = Vec::with_capacity(size);

        for i in 0..size {
            values.push(match self.get(&(addr + i)?) {
                Some(elem) => elem.into_owned(),
                None => return Err(MemoryError::GetRangeMemoryGap(Box::new((addr, size)))),
            });
        }

        Ok(values)
    }

    /// Gets a range of Felt252 memory values from addr to addr + size
    /// Fails if there if any of the values inside the range is missing (memory gap),
    /// or is not a Felt252
    pub fn get_integer_range(
        &self,
        addr: Relocatable,
        size: usize,
    ) -> Result<Vec<Cow<Felt252>>, MemoryError> {
        let mut values = Vec::new();

        for i in 0..size {
            values.push(self.get_integer((addr + i)?)?);
        }

        Ok(values)
    }

    pub fn mark_as_accessed(&mut self, addr: Relocatable) {
        let (i, j) = from_relocatable_to_indexes(addr);
        let data = if addr.segment_index < 0 {
            &mut self.temp_data
        } else {
            &mut self.data
        };

        data.get_mut(i).map(|s| s.mark_accessed(j));
    }

    pub fn get_amount_of_accessed_addresses_for_segment(
        &self,
        segment_index: usize,
    ) -> Option<usize> {
        let segment = self.data.get(segment_index)?;
        Some(segment.num_accessed())
    }

    pub fn load_felts(
        &mut self,
        ptr: Relocatable,
        data: &[Felt252],
    ) -> Result<Relocatable, MemoryError> {
        if data.is_empty() {
            return Ok(ptr);
        }

        let (value_index, _) = from_relocatable_to_indexes(ptr);

        let segments = if ptr.segment_index.is_negative() {
            &mut self.temp_data
        } else {
            &mut self.data
        };

        let data_len = segments.len();
        let segment = segments
            .get_mut(value_index)
            .ok_or_else(|| MemoryError::UnallocatedSegment(Box::new((value_index, data_len))))?;

        segment
            .load_felts(ptr.offset, data)
            .map(|new_offset| Relocatable {
                segment_index: ptr.segment_index,
                offset: new_offset,
            })
    }
}

impl From<&Memory> for CairoPieMemory {
    fn from(mem: &Memory) -> CairoPieMemory {
        let mut pie_memory = Vec::default();
        for (i, segment) in mem.data.iter().enumerate() {
            segment.append_to_pie(i, &mut pie_memory);
        }
        pie_memory
    }
}

impl fmt::Display for Memory {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, segment) in self.temp_data.iter().enumerate() {
            for (j, cell) in segment.iter().enumerate() {
                if let Some(elem) = cell {
                    let temp_segment = i + 1;
                    writeln!(f, "(-{temp_segment},{j}) : {elem}")?;
                }
            }
        }
        for (i, segment) in self.data.iter().enumerate() {
            for (j, cell) in segment.iter().enumerate() {
                if let Some(elem) = cell {
                    writeln!(f, "({i},{j}) : {elem}")?;
                }
            }
        }
        writeln!(f, "}}")
    }
}

/// Applies `relocation_rules` to a value
pub(crate) trait RelocateValue<'a, Input: 'a, Output: 'a> {
    fn relocate_value(&self, value: Input) -> Output;
}

impl RelocateValue<'_, Relocatable, Relocatable> for Memory {
    fn relocate_value(&self, addr: Relocatable) -> Relocatable {
        let segment_idx = addr.segment_index;
        if segment_idx >= 0 {
            return addr;
        }

        // Adjust the segment index to begin at zero, as per the struct field's
        // comment.
        match self.relocation_rules.get(&(-(segment_idx + 1) as usize)) {
            Some(x) => x + addr.offset,
            None => addr,
        }
    }
}

impl<'a> RelocateValue<'a, &'a Felt252, &'a Felt252> for Memory {
    fn relocate_value(&self, value: &'a Felt252) -> &'a Felt252 {
        value
    }
}

impl<'a> RelocateValue<'a, &'a MaybeRelocatable, Cow<'a, MaybeRelocatable>> for Memory {
    fn relocate_value(&self, value: &'a MaybeRelocatable) -> Cow<'a, MaybeRelocatable> {
        match value {
            MaybeRelocatable::Int(_) => Cow::Borrowed(value),
            MaybeRelocatable::RelocatableValue(addr) => {
                Cow::Owned(self.relocate_value(*addr).into())
            }
        }
    }
}

impl<'a> RelocateValue<'a, MaybeRelocatableRef<'a>, MaybeRelocatableRef<'a>> for Memory {
    fn relocate_value(&self, value: MaybeRelocatableRef<'a>) -> MaybeRelocatableRef<'a> {
        match value {
            MaybeRelocatableRef::RelocatableValue(addr) => {
                MaybeRelocatableRef::RelocatableValue(self.relocate_value(addr))
            }
            MaybeRelocatableRef::IntRef(_) => value,
        }
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod memory_tests {
    use core::ops::Shl;

    use super::*;
    use crate::{
        relocatable,
        types::instance_definitions::ecdsa_instance_def::EcdsaInstanceDef,
        utils::test_utils::*,
        vm::{
            runners::builtin_runner::{RangeCheckBuiltinRunner, SignatureBuiltinRunner},
            vm_memory::memory_segments::MemorySegmentManager,
        },
    };
    use assert_matches::assert_matches;
    use felt::felt_str;
    use num_traits::One;

    use crate::vm::errors::memory_errors::MemoryError;

    use crate::utils::test_utils::memory_from_memory;
    use crate::utils::test_utils::memory_inner;

    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_and_get_succesful() {
        let key = Relocatable::from((0, 0));
        let val = MaybeRelocatable::from(Felt252::new(5));
        let mut memory = Memory::new();
        memory.data.push(MemorySegment::default());
        memory.insert(key, &val).unwrap();
        assert_eq!(
            memory.get(&key).unwrap().as_ref(),
            &MaybeRelocatable::from(Felt252::new(5))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_valuef_from_temp_segment() {
        let mut memory = Memory::new();
        memory.temp_data = vec![MemorySegment::new(&[
            None,
            None,
            Some(mayberelocatable!(8)),
        ])];
        assert_eq!(
            memory.get(&mayberelocatable!(-1, 2)).unwrap().as_ref(),
            &mayberelocatable!(8),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_value_in_temp_segment() {
        let key = Relocatable::from((-1, 3));
        let val = MaybeRelocatable::from(Felt252::new(8));
        let mut memory = Memory::new();
        memory.temp_data.push(MemorySegment::default());
        memory.insert(key, &val).unwrap();
        assert_eq!(
            memory.temp_data[0].get(3).map(Into::into),
            Some(MaybeRelocatable::from(Felt252::new(8)))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_and_get_from_temp_segment_succesful() {
        let key = Relocatable::from((-1, 0));
        let val = MaybeRelocatable::from(Felt252::new(5));
        let mut memory = Memory::new();
        memory.temp_data.push(MemorySegment::default());
        memory.insert(key, &val).unwrap();
        assert_eq!(
            memory.get(&key).unwrap().as_ref(),
            &MaybeRelocatable::from(Felt252::new(5)),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_and_get_from_temp_segment_failed() {
        let key = relocatable!(-1, 1);
        let mut memory = Memory::new();
        memory.temp_data = vec![MemorySegment::new(&[None, Some(mayberelocatable!(8))])];
        assert_eq!(
            memory.insert(key, &mayberelocatable!(5)),
            Err(MemoryError::InconsistentMemory(Box::new((
                relocatable!(-1, 1),
                mayberelocatable!(8),
                mayberelocatable!(5)
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_non_allocated_memory() {
        let key = Relocatable::from((0, 0));
        let memory = Memory::new();
        assert_eq!(memory.get(&key), None);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_non_existant_element() {
        let key = Relocatable::from((0, 0));
        let memory = Memory::new();
        assert_eq!(memory.get(&key), None);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_non_allocated_memory() {
        let key = Relocatable::from((0, 0));
        let val = MaybeRelocatable::from(Felt252::new(5));
        let mut memory = Memory::new();
        let error = memory.insert(key, &val);
        assert_eq!(
            error,
            Err(MemoryError::UnallocatedSegment(Box::new((0, 0))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_inconsistent_memory() {
        let key = Relocatable::from((0, 0));
        let val_a = MaybeRelocatable::from(Felt252::new(5));
        let val_b = MaybeRelocatable::from(Felt252::new(6));
        let mut memory = Memory::new();
        memory.data.push(MemorySegment::default());
        memory
            .insert(key, &val_a)
            .expect("Unexpected memory insert fail");
        let error = memory.insert(key, &val_b);
        assert_eq!(
            error,
            Err(MemoryError::InconsistentMemory(Box::new((
                key, val_a, val_b
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_non_contiguous_element() {
        let key_a = Relocatable::from((0, 0));
        let key_b = Relocatable::from((0, 2));
        let val = MaybeRelocatable::from(Felt252::new(5));
        let mut memory = Memory::new();
        memory.data.push(MemorySegment::default());
        memory.insert(key_a, &val).unwrap();
        memory.insert(key_b, &val).unwrap();
        assert_eq!(memory.get(&key_b).unwrap().as_ref(), &val);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_non_contiguous_element_memory_gaps_none() {
        let key_a = Relocatable::from((0, 0));
        let key_b = Relocatable::from((0, 5));
        let val = MaybeRelocatable::from(Felt252::new(5));
        let mut memory = Memory::new();
        memory.data.push(MemorySegment::default());
        memory.insert(key_a, &val).unwrap();
        memory.insert(key_b, &val).unwrap();
        assert_eq!(memory.get(&key_b).unwrap().as_ref(), &val);
        assert_eq!(memory.get(&MaybeRelocatable::from((0, 1))), None);
        assert_eq!(memory.get(&MaybeRelocatable::from((0, 2))), None);
        assert_eq!(memory.get(&MaybeRelocatable::from((0, 3))), None);
        assert_eq!(memory.get(&MaybeRelocatable::from((0, 4))), None);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_range_check_within_bounds() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        builtin.add_validation_rule(&mut segments.memory);
        for _ in 0..3 {
            segments.add();
        }

        segments
            .memory
            .insert(
                Relocatable::from((0, 0)),
                &MaybeRelocatable::from(Felt252::new(45)),
            )
            .unwrap();
        segments.memory.validate_existing_memory().unwrap();
        assert!(segments
            .memory
            .validated_addresses
            .contains(&Relocatable::from((0, 0))));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_range_check_outside_bounds() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let mut segments = MemorySegmentManager::new();
        segments.add();
        builtin.initialize_segments(&mut segments);
        segments
            .memory
            .insert(
                Relocatable::from((1, 0)),
                &MaybeRelocatable::from(Felt252::new(-10)),
            )
            .unwrap();
        builtin.add_validation_rule(&mut segments.memory);
        let error = segments.memory.validate_existing_memory();
        assert_eq!(
            error,
            Err(MemoryError::RangeCheckNumOutOfBounds(Box::new((
                Felt252::new(-10),
                Felt252::one().shl(128_u32)
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_invalid_signature() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        segments.memory = memory![
            (
                (0, 0),
                (
                    "874739451078007766457464989774322083649278607533249481151382481072868806602",
                    10
                )
            ),
            (
                (0, 1),
                (
                    "-1472574760335685482768423018116732869320670550222259018541069375211356613248",
                    10
                )
            )
        ];
        builtin.add_validation_rule(&mut segments.memory);
        let error = segments.memory.validate_existing_memory();
        assert_eq!(
            error,
            Err(MemoryError::SignatureNotFound(Box::new((0, 0).into())))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_valid_signature() {
        let mut builtin = SignatureBuiltinRunner::new(&EcdsaInstanceDef::default(), true);

        let signature_r = felt_str!(
            "1839793652349538280924927302501143912227271479439798783640887258675143576352"
        );
        let signature_s = felt_str!(
            "1819432147005223164874083361865404672584671743718628757598322238853218813979"
        );

        builtin
            .add_signature(Relocatable::from((1, 0)), &(signature_r, signature_s))
            .unwrap();

        let mut segments = MemorySegmentManager::new();

        segments.memory = memory![
            (
                (1, 0),
                (
                    "874739451078007766457464989774322083649278607533249481151382481072868806602",
                    10
                )
            ),
            ((1, 1), 2)
        ];

        builtin.initialize_segments(&mut segments);

        builtin.add_validation_rule(&mut segments.memory);

        let result = segments.memory.validate_existing_memory();

        assert_eq!(result, Ok(()))
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_range_check_relocatable_value() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        segments.memory = memory![((0, 0), (0, 4))];
        builtin.add_validation_rule(&mut segments.memory);
        let error = segments.memory.validate_existing_memory();
        assert_eq!(
            error,
            Err(MemoryError::RangeCheckFoundNonInt(Box::new(relocatable!(
                0, 0
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn validate_existing_memory_for_range_check_out_of_bounds_diff_segment() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let mut segments = MemorySegmentManager::new();
        segments.memory = Memory::new();
        segments.add();
        builtin.initialize_segments(&mut segments);
        segments
            .memory
            .insert(
                Relocatable::from((0, 0)),
                &MaybeRelocatable::from(Felt252::new(-45)),
            )
            .unwrap();
        builtin.add_validation_rule(&mut segments.memory);
        assert_eq!(segments.memory.validate_existing_memory(), Ok(()));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_integer_valid() {
        let memory = memory![((0, 0), 10)];
        assert_eq!(
            memory
                .get_integer(Relocatable::from((0, 0)))
                .unwrap()
                .as_ref(),
            &Felt252::new(10)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_integer_invalid_expected_integer() {
        let mut segments = MemorySegmentManager::new();
        segments.add();
        segments
            .memory
            .insert(Relocatable::from((0, 0)), &MaybeRelocatable::from((0, 10)))
            .unwrap();
        assert_matches!(
            segments.memory.get_integer(Relocatable::from((0, 0))),
            Err(MemoryError::ExpectedInteger(
                bx
            )) if *bx == Relocatable::from((0, 0))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn default_memory() {
        let mem: Memory = Default::default();
        assert_eq!(mem.data.len(), 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn insert_and_get_temporary_succesful() {
        let mut memory = Memory::new();
        memory.temp_data.push(MemorySegment::default());

        let key = Relocatable::from((-1, 0));
        let val = MaybeRelocatable::from(Felt252::new(5));
        memory.insert(key, &val).unwrap();

        assert_eq!(memory.get(&key).unwrap().as_ref(), &val);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn add_relocation_rule() {
        let mut memory = Memory::new();

        assert_eq!(
            memory.add_relocation_rule((-1, 0).into(), (1, 2).into()),
            Ok(()),
        );
        assert_eq!(
            memory.add_relocation_rule((-2, 0).into(), (-1, 1).into()),
            Ok(()),
        );
        assert_eq!(
            memory.add_relocation_rule((5, 0).into(), (0, 0).into()),
            Err(MemoryError::AddressNotInTemporarySegment(5)),
        );
        assert_eq!(
            memory.add_relocation_rule((-3, 6).into(), (0, 0).into()),
            Err(MemoryError::NonZeroOffset(6)),
        );
        assert_eq!(
            memory.add_relocation_rule((-1, 0).into(), (0, 0).into()),
            Err(MemoryError::DuplicatedRelocation(-1)),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_value_bigint() {
        let mut memory = Memory::new();
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory
            .add_relocation_rule((-2, 0).into(), (2, 2).into())
            .unwrap();

        // Test when value is Some(BigInt):
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::Int(Felt252::new(0))),
            Cow::Owned(MaybeRelocatable::Int(Felt252::new(0))),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_value_mayberelocatable() {
        let mut memory = Memory::new();
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory
            .add_relocation_rule((-2, 0).into(), (2, 2).into())
            .unwrap();

        // Test when value is Some(MaybeRelocatable) with segment_index >= 0:
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((0, 0).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((0, 0).into())),
        );
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((5, 0).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((5, 0).into())),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_value_mayberelocatable_temporary_segment_no_rules() {
        let mut memory = Memory::new();
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory
            .add_relocation_rule((-2, 0).into(), (2, 2).into())
            .unwrap();

        // Test when value is Some(MaybeRelocatable) with segment_index < 0 and
        // there are no applicable relocation rules:
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((-5, 0).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((-5, 0).into())),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_value_mayberelocatable_temporary_segment_rules() {
        let mut memory = Memory::new();
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory
            .add_relocation_rule((-2, 0).into(), (2, 2).into())
            .unwrap();

        // Test when value is Some(MaybeRelocatable) with segment_index < 0 and
        // there are applicable relocation rules:
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((-1, 0).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((2, 0).into())),
        );
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((-2, 0).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((2, 2).into())),
        );
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((-1, 5).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((2, 5).into())),
        );
        assert_eq!(
            memory.relocate_value(&MaybeRelocatable::RelocatableValue((-2, 5).into())),
            Cow::Owned(MaybeRelocatable::RelocatableValue((2, 7).into())),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_for_continuous_memory() {
        let memory = memory![((1, 0), 2), ((1, 1), 3), ((1, 2), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2));
        let value2 = MaybeRelocatable::from(Felt252::new(3));
        let value3 = MaybeRelocatable::from(Felt252::new(4));

        let expected_vec = vec![
            Some(Cow::Borrowed(&value1)),
            Some(Cow::Borrowed(&value2)),
            Some(Cow::Borrowed(&value3)),
        ];
        assert_eq!(memory.get_range(Relocatable::from((1, 0)), 3), expected_vec);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_for_non_continuous_memory() {
        let memory = memory![((1, 0), 2), ((1, 1), 3), ((1, 3), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2));
        let value2 = MaybeRelocatable::from(Felt252::new(3));
        let value3 = MaybeRelocatable::from(Felt252::new(4));

        let expected_vec = vec![
            Some(Cow::Borrowed(&value1)),
            Some(Cow::Borrowed(&value2)),
            None,
            Some(Cow::Borrowed(&value3)),
        ];
        assert_eq!(memory.get_range(Relocatable::from((1, 0)), 4), expected_vec);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_continuous_range_for_continuous_memory() {
        let memory = memory![((1, 0), 2), ((1, 1), 3), ((1, 2), 4)];

        let value1 = MaybeRelocatable::from(Felt252::new(2));
        let value2 = MaybeRelocatable::from(Felt252::new(3));
        let value3 = MaybeRelocatable::from(Felt252::new(4));

        let expected_vec = vec![value1, value2, value3];
        assert_eq!(
            memory.get_continuous_range(Relocatable::from((1, 0)), 3),
            Ok(expected_vec)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_continuous_range_for_non_continuous_memory() {
        let memory = memory![((1, 0), 2), ((1, 1), 3), ((1, 3), 4)];

        assert_eq!(
            memory.get_continuous_range(Relocatable::from((1, 0)), 3),
            Err(MemoryError::GetRangeMemoryGap(Box::new(((1, 0).into(), 3))))
        );
    }

    /// Test that relocate_memory() works when there are no relocation rules.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_empty_relocation_rules() {
        let mut memory = memory![((0, 0), 1), ((0, 1), 2), ((0, 2), 3)];

        assert_eq!(memory.relocate_memory(), Ok(()));
        check_memory!(memory, ((0, 0), 1), ((0, 1), 2), ((0, 2), 3));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_new_segment_with_gap() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (2, 1).into())
            .unwrap();
        memory.data.push(MemorySegment::default());

        assert_eq!(memory.relocate_memory(), Ok(()));
        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (2, 1)),
            ((0, 2), 3),
            ((1, 0), (2, 2)),
            ((1, 1), 5),
            ((1, 2), (2, 3)),
            ((2, 1), 7),
            ((2, 2), 8),
            ((2, 3), 9)
        );
        assert!(memory.temp_data.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_new_segment() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory.data.push(MemorySegment::default());

        assert_eq!(memory.relocate_memory(), Ok(()));

        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (2, 0)),
            ((0, 2), 3),
            ((1, 0), (2, 1)),
            ((1, 1), 5),
            ((1, 2), (2, 2)),
            ((2, 0), 7),
            ((2, 1), 8),
            ((2, 2), 9)
        );
        assert!(memory.temp_data.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_new_segment_unallocated() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();

        assert_eq!(
            memory.relocate_memory(),
            Err(MemoryError::UnallocatedSegment(Box::new((2, 2))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_into_existing_segment() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (1, 3).into())
            .unwrap();

        assert_eq!(memory.relocate_memory(), Ok(()));

        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (1, 3)),
            ((0, 2), 3),
            ((1, 0), (1, 4)),
            ((1, 1), 5),
            ((1, 2), (1, 5)),
            ((1, 3), 7),
            ((1, 4), 8),
            ((1, 5), 9)
        );
        assert!(memory.temp_data.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_into_existing_segment_inconsistent_memory() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (1, 0).into())
            .unwrap();

        assert_eq!(
            memory.relocate_memory(),
            Err(MemoryError::InconsistentMemory(Box::new((
                (1, 0).into(),
                (1, 1).into(),
                7.into(),
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_new_segment_2_temporary_segments_one_relocated() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9),
            ((-2, 0), 10),
            ((-2, 1), 11)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory.data.push(MemorySegment::default());

        assert_eq!(memory.relocate_memory(), Ok(()));
        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (2, 0)),
            ((0, 2), 3),
            ((1, 0), (2, 1)),
            ((1, 1), 5),
            ((1, 2), (2, 2)),
            ((2, 0), 7),
            ((2, 1), 8),
            ((2, 2), 9),
            ((-1, 0), 10),
            ((-1, 1), 11)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_new_segment_2_temporary_segments_relocated() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), 7),
            ((-1, 1), 8),
            ((-1, 2), 9),
            ((-2, 0), 10),
            ((-2, 1), 11)
        ];
        memory.data.push(MemorySegment::default());
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory.data.push(MemorySegment::default());
        memory
            .add_relocation_rule((-2, 0).into(), (3, 0).into())
            .unwrap();

        assert_eq!(memory.relocate_memory(), Ok(()));

        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (2, 0)),
            ((0, 2), 3),
            ((1, 0), (2, 1)),
            ((1, 1), 5),
            ((1, 2), (2, 2)),
            ((2, 0), 7),
            ((2, 1), 8),
            ((2, 2), 9),
            ((3, 0), 10),
            ((3, 1), 11)
        );
        assert!(memory.temp_data.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_memory_display() {
        let memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), (-1, 0)),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];

        assert_eq!(
            format!("{}", memory),
            "(-1,0) : -1:0\n(-1,1) : 8\n(-1,2) : 9\n(0,0) : 1\n(0,1) : -1:0\n(0,2) : 3\n(1,0) : -1:1\n(1,1) : 5\n(1,2) : -1:2\n}\n");
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_memory_into_existing_segment_temporary_values_in_temporary_memory() {
        let mut memory = memory![
            ((0, 0), 1),
            ((0, 1), (-1, 0)),
            ((0, 2), 3),
            ((1, 0), (-1, 1)),
            ((1, 1), 5),
            ((1, 2), (-1, 2)),
            ((-1, 0), (-1, 0)),
            ((-1, 1), 8),
            ((-1, 2), 9)
        ];
        memory
            .add_relocation_rule((-1, 0).into(), (1, 3).into())
            .unwrap();

        assert_eq!(memory.relocate_memory(), Ok(()));
        check_memory!(
            memory,
            ((0, 0), 1),
            ((0, 1), (1, 3)),
            ((0, 2), 3),
            ((1, 0), (1, 4)),
            ((1, 1), 5),
            ((1, 2), (1, 5)),
            ((1, 3), (1, 3)),
            ((1, 4), 8),
            ((1, 5), 9)
        );
        assert!(memory.temp_data.is_empty());
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_address_with_rules() {
        let mut memory = Memory::new();
        memory
            .add_relocation_rule((-1, 0).into(), (2, 0).into())
            .unwrap();
        memory
            .add_relocation_rule((-2, 0).into(), (2, 2).into())
            .unwrap();

        assert_eq!(
            relocate_address((-1, 0).into(), &memory.relocation_rules),
            (2, 0).into(),
        );
        assert_eq!(
            relocate_address((-2, 1).into(), &memory.relocation_rules),
            (2, 3).into(),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_address_no_rules() {
        let memory = Memory::new();
        assert_eq!(
            relocate_address((-1, 0).into(), &memory.relocation_rules),
            (-1, 0).into(),
        );
        assert_eq!(
            relocate_address((-2, 1).into(), &memory.relocation_rules),
            (-2, 1).into(),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn relocate_address_real_addr() {
        let memory = Memory::new();
        assert_eq!(
            relocate_address((1, 0).into(), &memory.relocation_rules),
            (1, 0).into(),
        );
        assert_eq!(
            relocate_address((1, 1).into(), &memory.relocation_rules),
            (1, 1).into(),
        );
    }

    #[test]
    fn mark_address_as_accessed() {
        let mut memory = memory![((0, 0), 0)];
        assert!(!memory.data[0].is_accessed(0));
        memory.mark_as_accessed(relocatable!(0, 0));
        assert!(memory.data[0].is_accessed(0));
    }

    #[test]
    fn get_amount_of_accessed_addresses_for_segment_valid() {
        let mut memory = memory![((0, 0), 0)];
        assert_eq!(
            memory.get_amount_of_accessed_addresses_for_segment(0),
            Some(0)
        );
        memory.mark_as_accessed(relocatable!(0, 0));
        assert_eq!(
            memory.get_amount_of_accessed_addresses_for_segment(0),
            Some(1)
        );
    }

    #[test]
    fn get_amount_of_accessed_addresses_for_segment_invalid_segment() {
        let memory = memory![((0, 0), 0)];
        assert_eq!(memory.get_amount_of_accessed_addresses_for_segment(1), None);
    }

    use core::cmp::Ordering::*;

    fn check_memcmp(
        lhs: (isize, usize),
        rhs: (isize, usize),
        len: usize,
        ord: Ordering,
        pos: usize,
    ) {
        let mem = memory![
            ((-2, 0), 1),
            ((-2, 1), (1, 1)),
            ((-2, 3), 0),
            ((-2, 4), 0),
            ((-1, 0), 1),
            ((-1, 1), (1, 1)),
            ((-1, 3), 0),
            ((-1, 4), 3),
            ((0, 0), 1),
            ((0, 1), (1, 1)),
            ((0, 3), 0),
            ((0, 4), 0),
            ((1, 0), 1),
            ((1, 1), (1, 1)),
            ((1, 3), 0),
            ((1, 4), 3)
        ];
        assert_eq!((ord, pos), mem.memcmp(lhs.into(), rhs.into(), len));
    }

    #[test]
    fn insert_alloc_fails_gracefully() {
        let mut mem = memory![((0, 0), 1)];
        let err = mem.insert((0, usize::MAX >> 1).into(), Felt252::one());
        assert_eq!(err, Err(MemoryError::VecCapacityExceeded));
    }

    #[test]
    fn insert_overflow_fails_gracefully() {
        let mut mem = memory![((0, 0), 1)];
        let err = mem.insert((0, usize::MAX).into(), Felt252::one());
        assert_eq!(err, Err(MemoryError::VecCapacityExceeded));
    }

    #[test]
    fn memcmp() {
        check_memcmp((0, 0), (0, 0), 3, Equal, 3);
        check_memcmp((0, 0), (1, 0), 3, Equal, 3);
        check_memcmp((0, 0), (1, 0), 5, Less, 4);
        check_memcmp((1, 0), (0, 0), 5, Greater, 4);
        check_memcmp((2, 2), (2, 5), 8, Equal, 0);
        check_memcmp((0, 0), (2, 5), 8, Greater, 0);
        check_memcmp((2, 5), (0, 0), 8, Less, 0);
        check_memcmp((-2, 0), (-2, 0), 3, Equal, 3);
        check_memcmp((-2, 0), (-1, 0), 3, Equal, 3);
        check_memcmp((-2, 0), (-1, 0), 5, Less, 4);
        check_memcmp((-1, 0), (-2, 0), 5, Greater, 4);
        check_memcmp((-3, 2), (-3, 5), 8, Equal, 0);
        check_memcmp((-2, 0), (-3, 5), 8, Greater, 0);
        check_memcmp((-3, 5), (-2, 0), 8, Less, 0);
    }

    #[test]
    fn cairo_pie_memory_from_memory() {
        let memory = memory![((8, 9), 3), ((1, 2), 5), ((7, 6), (1, 2))];

        assert_eq!(
            CairoPieMemory::from(&memory),
            vec![
                ((1, 2), MaybeRelocatable::from(5)),
                ((7, 6), MaybeRelocatable::from((1, 2))),
                ((8, 9), MaybeRelocatable::from(3))
            ]
        )
    }
}
