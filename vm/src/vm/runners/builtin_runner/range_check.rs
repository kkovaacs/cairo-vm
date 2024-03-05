use crate::stdlib::{
    cmp::{max, min},
    ops::Shl,
    prelude::*,
};

use crate::{
    types::{
        instance_definitions::range_check_instance_def::CELLS_PER_RANGE_CHECK,
        relocatable::{MaybeRelocatable, Relocatable},
    },
    vm::{
        errors::{memory_errors::MemoryError, runner_errors::RunnerError},
        vm_memory::{
            memory::{Memory, ValidationRule},
            memory_segments::MemorySegmentManager,
        },
    },
};
use felt::Felt252;
use num_traits::{One, Zero};

use super::RANGE_CHECK_BUILTIN_NAME;

// NOTE: the current implementation is based on the bound 0x10000
const _INNER_RC_BOUND: u64 = 1u64 << INNER_RC_BOUND_SHIFT;
const INNER_RC_BOUND_SHIFT: u64 = 16;
const INNER_RC_BOUND_MASK: u64 = u16::MAX as u64;

// TODO: use constant instead of receiving as false parameter
const N_PARTS: u64 = 8;

#[derive(Debug, Clone)]
pub struct RangeCheckBuiltinRunner {
    ratio: Option<u32>,
    base: usize,
    pub(crate) stop_ptr: Option<usize>,
    pub(crate) cells_per_instance: u32,
    pub(crate) n_input_cells: u32,
    pub _bound: Option<Felt252>,
    pub(crate) included: bool,
    pub(crate) n_parts: u32,
    pub(crate) instances_per_component: u32,
}

impl RangeCheckBuiltinRunner {
    pub fn new(ratio: Option<u32>, n_parts: u32, included: bool) -> RangeCheckBuiltinRunner {
        let bound = Felt252::one().shl(16 * n_parts);
        let _bound = if n_parts != 0 && bound.is_zero() {
            None
        } else {
            Some(Felt252::new(bound))
        };

        RangeCheckBuiltinRunner {
            ratio,
            base: 0,
            stop_ptr: None,
            cells_per_instance: CELLS_PER_RANGE_CHECK,
            n_input_cells: CELLS_PER_RANGE_CHECK,
            _bound,
            included,
            n_parts,
            instances_per_component: 1,
        }
    }

    pub fn initialize_segments(&mut self, segments: &mut MemorySegmentManager) {
        self.base = segments.add().segment_index as usize // segments.add() always returns a positive index
    }

    pub fn initial_stack(&self) -> Vec<MaybeRelocatable> {
        if self.included {
            vec![MaybeRelocatable::from((self.base as isize, 0))]
        } else {
            vec![]
        }
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn ratio(&self) -> Option<u32> {
        self.ratio
    }

    pub fn add_validation_rule(&self, memory: &mut Memory) {
        let rule: ValidationRule = ValidationRule(Box::new(
            |memory: &Memory, address: Relocatable| -> Result<Vec<Relocatable>, MemoryError> {
                let num = memory
                    .get_integer(address)
                    .map_err(|_| MemoryError::RangeCheckFoundNonInt(Box::new(address)))?;
                if num.bits() <= N_PARTS * INNER_RC_BOUND_SHIFT {
                    Ok(vec![address.to_owned()])
                } else {
                    Err(MemoryError::RangeCheckNumOutOfBounds(Box::new((
                        num.into_owned(),
                        Felt252::one() << ((N_PARTS * INNER_RC_BOUND_SHIFT) as u32),
                    ))))
                }
            },
        ));
        memory.add_validation_rule(self.base, rule);
    }

    pub fn deduce_memory_cell(
        &self,
        _address: Relocatable,
        _memory: &Memory,
    ) -> Result<Option<MaybeRelocatable>, RunnerError> {
        Ok(None)
    }

    pub fn get_memory_segment_addresses(&self) -> (usize, Option<usize>) {
        (self.base, self.stop_ptr)
    }

    pub fn get_used_cells(&self, segments: &MemorySegmentManager) -> Result<usize, MemoryError> {
        segments
            .get_segment_used_size(self.base)
            .ok_or(MemoryError::MissingSegmentUsedSizes)
    }

    pub fn get_range_check_usage(&self, memory: &Memory) -> Option<(usize, usize)> {
        let range_check_segment = memory.data.get(self.base)?;
        let mut rc_bounds =
            (!range_check_segment.is_empty()).then_some((usize::MAX, usize::MIN))?;

        // Split value into n_parts parts of less than _INNER_RC_BOUND size.
        for offset in 0..range_check_segment.len() {
            rc_bounds = range_check_segment
                .get(offset)
                .as_ref()?
                .get_int_ref()?
                .to_le_digits()
                // TODO: maybe skip leading zeros
                .into_iter()
                .flat_map(|digit| {
                    (0..=3)
                        .rev()
                        .map(move |i| ((digit >> (i * INNER_RC_BOUND_SHIFT)) & INNER_RC_BOUND_MASK))
                })
                .take(self.n_parts as usize)
                .fold(rc_bounds, |mm, x| {
                    (min(mm.0, x as usize), max(mm.1, x as usize))
                });
        }
        Some(rc_bounds)
    }

    pub fn get_used_instances(
        &self,
        segments: &MemorySegmentManager,
    ) -> Result<usize, MemoryError> {
        self.get_used_cells(segments)
    }

    pub fn final_stack(
        &mut self,
        segments: &MemorySegmentManager,
        pointer: Relocatable,
    ) -> Result<Relocatable, RunnerError> {
        if self.included {
            let stop_pointer_addr = (pointer - 1)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(RANGE_CHECK_BUILTIN_NAME)))?;
            let stop_pointer = segments
                .memory
                .get_relocatable(stop_pointer_addr)
                .map_err(|_| RunnerError::NoStopPointer(Box::new(RANGE_CHECK_BUILTIN_NAME)))?;
            if self.base as isize != stop_pointer.segment_index {
                return Err(RunnerError::InvalidStopPointerIndex(Box::new((
                    RANGE_CHECK_BUILTIN_NAME,
                    stop_pointer,
                    self.base,
                ))));
            }
            let stop_ptr = stop_pointer.offset;
            let num_instances = self.get_used_instances(segments)?;
            let used = num_instances * self.cells_per_instance as usize;
            if stop_ptr != used {
                return Err(RunnerError::InvalidStopPointer(Box::new((
                    RANGE_CHECK_BUILTIN_NAME,
                    Relocatable::from((self.base as isize, used)),
                    Relocatable::from((self.base as isize, stop_ptr)),
                ))));
            }
            self.stop_ptr = Some(stop_ptr);
            Ok(stop_pointer_addr)
        } else {
            self.stop_ptr = Some(0);
            Ok(pointer)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relocatable;
    use crate::serde::deserialize_program::BuiltinName;
    use crate::stdlib::collections::HashMap;
    use crate::vm::vm_memory::memory::Memory;
    use crate::{
        hint_processor::builtin_hint_processor::builtin_hint_processor_definition::BuiltinHintProcessor,
        types::program::Program,
        utils::test_utils::*,
        vm::{
            runners::{builtin_runner::BuiltinRunner, cairo_runner::CairoRunner},
            vm_core::VirtualMachine,
        },
    };

    use felt::felt_str;
    #[cfg(target_arch = "wasm32")]
    use wasm_bindgen_test::*;

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_instances() {
        let builtin = RangeCheckBuiltinRunner::new(Some(10), 12, true);

        let mut vm = vm!();
        vm.segments.segment_used_sizes = Some(vec![1]);

        assert_eq!(builtin.get_used_instances(&vm.segments), Ok(1));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(10), 12, true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer).unwrap(),
            Relocatable::from((2, 1))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_stop_pointer() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(10), 12, true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![998]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer),
            Err(RunnerError::InvalidStopPointer(Box::new((
                RANGE_CHECK_BUILTIN_NAME,
                relocatable!(0, 998),
                relocatable!(0, 0)
            ))))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_when_notincluded() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(10), 12, false);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), (0, 0))
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer).unwrap(),
            Relocatable::from((2, 2))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn final_stack_error_non_relocatable() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(10), 12, true);

        let mut vm = vm!();

        vm.segments = segments![
            ((0, 0), (0, 0)),
            ((0, 1), (0, 1)),
            ((2, 0), (0, 0)),
            ((2, 1), 2)
        ];

        vm.segments.segment_used_sizes = Some(vec![0]);

        let pointer = Relocatable::from((2, 2));

        assert_eq!(
            builtin.final_stack(&vm.segments, pointer),
            Err(RunnerError::NoStopPointer(Box::new(
                RANGE_CHECK_BUILTIN_NAME
            )))
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_and_allocated_size_test() {
        let builtin: BuiltinRunner = RangeCheckBuiltinRunner::new(Some(10), 12, true).into();

        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);

        let program = program!(
            builtins = vec![BuiltinName::range_check],
            data = vec!(
                felt_str!("4612671182993129469"),
                felt_str!("5189976364521848832"),
                felt_str!("18446744073709551615"),
                felt_str!("5199546496550207487"),
                felt_str!("4612389712311386111"),
                felt_str!("5198983563776393216"),
                felt_str!("2"),
                felt_str!("2345108766317314046"),
                felt_str!("5191102247248822272"),
                felt_str!("5189976364521848832"),
                felt_str!("7"),
                felt_str!("1226245742482522112"),
                felt_str!(
                    "3618502788666131213697322783095070105623107215331596699973092056135872020470",
                    10
                ),
                felt_str!("2345108766317314046"),
            ),
            main = Some(8),
        );

        let mut cairo_runner = cairo_runner!(program);

        let mut hint_processor = BuiltinHintProcessor::new_empty();

        let address = cairo_runner.initialize(&mut vm).unwrap();

        cairo_runner
            .run_until_pc(address, &mut vm, &mut hint_processor)
            .unwrap();

        assert_eq!(builtin.get_used_cells_and_allocated_size(&vm), Ok((0, 1)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_allocated_memory_units() {
        let builtin: BuiltinRunner = RangeCheckBuiltinRunner::new(Some(10), 12, true).into();

        let mut vm = vm!();

        let program = program!(
            builtins = vec![BuiltinName::range_check],
            data = vec!(
                felt_str!("4612671182993129469"),
                felt_str!("5189976364521848832"),
                felt_str!("18446744073709551615"),
                felt_str!("5199546496550207487"),
                felt_str!("4612389712311386111"),
                felt_str!("5198983563776393216"),
                felt_str!("2"),
                felt_str!("2345108766317314046"),
                felt_str!("5191102247248822272"),
                felt_str!("5189976364521848832"),
                felt_str!("7"),
                felt_str!("1226245742482522112"),
                felt_str!(
                    "3618502788666131213697322783095070105623107215331596699973092056135872020470",
                    10
                ),
                felt_str!("2345108766317314046"),
            ),
            main = Some(8),
        );

        let mut cairo_runner = cairo_runner!(program);

        let mut hint_processor = BuiltinHintProcessor::new_empty();

        let address = cairo_runner.initialize(&mut vm).unwrap();

        cairo_runner
            .run_until_pc(address, &mut vm, &mut hint_processor)
            .unwrap();

        assert_eq!(builtin.get_allocated_memory_units(&vm), Ok(1));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn initialize_segments_for_range_check() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let mut segments = MemorySegmentManager::new();
        builtin.initialize_segments(&mut segments);
        assert_eq!(builtin.base, 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_initial_stack_for_range_check_with_base() {
        let mut builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        builtin.base = 1;
        let initial_stack = builtin.initial_stack();
        assert_eq!(
            initial_stack[0].clone(),
            MaybeRelocatable::RelocatableValue((builtin.base() as isize, 0).into())
        );
        assert_eq!(initial_stack.len(), 1);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_segment_addresses() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);

        assert_eq!(builtin.get_memory_segment_addresses(), (0, None),);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_missing_segment_used_sizes() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let vm = vm!();

        assert_eq!(
            builtin.get_memory_accesses(&vm),
            Err(MemoryError::MissingSegmentUsedSizes),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses_empty() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_memory_accesses(&vm), Ok(vec![]));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_memory_accesses() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![4]);
        assert_eq!(
            builtin.get_memory_accesses(&vm),
            Ok(vec![
                (builtin.base() as isize, 0).into(),
                (builtin.base() as isize, 1).into(),
                (builtin.base() as isize, 2).into(),
                (builtin.base() as isize, 3).into(),
            ]),
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_base() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        assert_eq!(builtin.base(), 0);
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn test_ratio() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        assert_eq!(builtin.ratio(), Some(8));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_missing_segment_used_sizes() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let vm = vm!();

        assert_eq!(
            builtin.get_used_cells(&vm.segments),
            Err(MemoryError::MissingSegmentUsedSizes)
        );
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells_empty() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![0]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(0));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_cells() {
        let builtin = BuiltinRunner::RangeCheck(RangeCheckBuiltinRunner::new(Some(256), 8, true));
        let mut vm = vm!();

        vm.segments.segment_used_sizes = Some(vec![4]);
        assert_eq!(builtin.get_used_cells(&vm.segments), Ok(4));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_check_usage_succesful_a() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let memory = memory![((0, 0), 1), ((0, 1), 2), ((0, 2), 3), ((0, 3), 4)];
        assert_eq!(builtin.get_range_check_usage(&memory), Some((0, 4)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_check_usage_succesful_b() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let memory = memory![
            ((0, 0), 1465218365),
            ((0, 1), 2134570341),
            ((0, 2), 31349610736_i64),
            ((0, 3), 413468326585859_i64)
        ];
        assert_eq!(builtin.get_range_check_usage(&memory), Some((0, 62821)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_check_usage_succesful_c() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let memory = memory![
            ((0, 0), 634834751465218365_i64),
            ((0, 1), 42876922134570341_i64),
            ((0, 2), 23469831349610736_i64),
            ((0, 3), 23468413468326585859_i128),
            ((0, 4), 75346043276073460326_i128),
            ((0, 5), 87234598724867609478353436890268_i128)
        ];
        assert_eq!(builtin.get_range_check_usage(&memory), Some((0, 61576)));
    }

    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_range_check_empty_memory() {
        let builtin = RangeCheckBuiltinRunner::new(Some(8), 8, true);
        let memory = Memory::new();
        assert_eq!(builtin.get_range_check_usage(&memory), None);
    }

    /// Test that the method get_used_perm_range_check_units works as intended.
    #[test]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
    fn get_used_perm_range_check_units() {
        let builtin_runner: BuiltinRunner = RangeCheckBuiltinRunner::new(Some(8), 8, true).into();
        let mut vm = vm!();

        vm.current_step = 8;
        vm.segments.segment_used_sizes = Some(vec![1]);
        assert_eq!(builtin_runner.get_used_perm_range_check_units(&vm), Ok(8));
    }
}
