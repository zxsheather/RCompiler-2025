use std::collections::HashSet;

use crate::middleend::ir::lower::ENTRY_BLOCK_LABEL;
use crate::middleend::ir::module::{
    CallTarget, IRBinaryOp, IRCastOp, IRFunction, IRInstruction, IRInstructionKind, IRValue,
};
use crate::{
    frontend::r_semantic::{built_in::get_built_in_funcs, tyctxt::TypeContext},
    middleend::ir::{
        module::{IRBasicBlock, IRICmpOp, IRType},
        utils::{mangle_symbol_name, rx_to_ir_type},
    },
};

#[derive(Debug)]
pub struct BuiltinLowering {
    pub functions: Vec<IRFunction>,
    pub externs: Vec<IRFunction>,
}

impl BuiltinLowering {
    pub fn empty() -> Self {
        Self {
            functions: Vec::new(),
            externs: Vec::new(),
        }
    }
}

pub fn build_builtin_lowering(
    type_ctx: &TypeContext,
    defined_symbols: &HashSet<String>,
) -> BuiltinLowering {
    let mut lowering = BuiltinLowering::empty();

    for (name, _sig) in get_built_in_funcs() {
        let symbol = mangle_symbol_name(name);
        if defined_symbols.contains(&symbol) {
            continue;
        }
        match name {
            "print" => {
                let func = build_print(type_ctx);
                lowering.functions.push(func);
            }
            "println" => {
                let func = build_println(type_ctx);
                lowering.functions.push(func);
            }
            "printInt" => {
                let func = build_print_int(type_ctx);
                lowering.functions.push(func);
            }
            "printlnInt" => {
                let func = build_println_int(type_ctx);
                lowering.functions.push(func);
            }
            _ => {}
        }
    }

    lowering.externs.extend(build_runtime_externs());

    lowering
}

fn build_runtime_externs() -> Vec<IRFunction> {
    let mut externs = Vec::new();
    let putchar = IRFunction {
        name: "putchar".to_string(),
        params: vec![("c".to_string(), IRType::I32)],
        return_type: IRType::I32,
        basic_blocks: Vec::new(),
    };
    externs.push(putchar);

    let getchar = IRFunction {
        name: "getchar".to_string(),
        params: Vec::new(),
        return_type: IRType::I32,
        basic_blocks: Vec::new(),
    };
    externs.push(getchar);

    let exit = IRFunction {
        name: "exit".to_string(),
        params: vec![("code".to_string(), IRType::I32)],
        return_type: IRType::Void,
        basic_blocks: Vec::new(),
    };
    externs.push(exit);

    // llvm.memset.p0.i32(ptr, i8, i32, i1)
    let memset = IRFunction {
        name: "llvm.memset.p0.i32".to_string(),
        params: vec![
            ("dest".to_string(), IRType::Ptr(Box::new(IRType::I8))),
            ("val".to_string(), IRType::I8),
            ("len".to_string(), IRType::I32),
            ("is_volatile".to_string(), IRType::I1),
        ],
        return_type: IRType::Void,
        basic_blocks: Vec::new(),
    };
    externs.push(memset);

    // llvm.memcpy.p0.p0.i32(ptr, ptr, i32, i1)
    let memcpy = IRFunction {
        name: "llvm.memcpy.p0.p0.i32".to_string(),
        params: vec![
            ("dest".to_string(), IRType::Ptr(Box::new(IRType::I8))),
            ("src".to_string(), IRType::Ptr(Box::new(IRType::I8))),
            ("len".to_string(), IRType::I32),
            ("is_volatile".to_string(), IRType::I1),
        ],
        return_type: IRType::Void,
        basic_blocks: Vec::new(),
    };
    externs.push(memcpy);

    externs
}

fn build_print(type_ctx: &TypeContext) -> IRFunction {
    let sig = type_ctx
        .get_function("print")
        .expect("builtin signature must exist");
    let arg_ty = rx_to_ir_type(type_ctx, &sig.params()[0]);
    let str_inner = match &arg_ty {
        IRType::Ptr(inner) => inner.as_ref().clone(),
        _ => panic!("unexpected type for print argument: {:?}", arg_ty),
    };

    let mut entry_insts = Vec::new();

    let load_slice = IRInstruction::new(IRInstructionKind::Load {
        ptr: IRValue::Argument {
            index: 0,
            name: Some("arg0".into()),
            ty: arg_ty.clone(),
        },
        align: None,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%0".into(),
            ty: str_inner.clone(),
        },
        Some(str_inner.clone()),
    );
    entry_insts.push(load_slice);

    let data_ptr = IRInstruction::new(IRInstructionKind::ExtractValue {
        aggregate: IRValue::InstructionRef {
            id: "%0".into(),
            ty: str_inner.clone(),
        },
        indices: vec![0],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%1".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        Some(IRType::Ptr(Box::new(IRType::I8))),
    );
    entry_insts.push(data_ptr);

    let len_val = IRInstruction::new(IRInstructionKind::ExtractValue {
        aggregate: IRValue::InstructionRef {
            id: "%0".into(),
            ty: str_inner.clone(),
        },
        indices: vec![1],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%2".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );
    entry_insts.push(len_val);

    let entry_block = IRBasicBlock {
        label: ENTRY_BLOCK_LABEL.into(),
        instructions: entry_insts,
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "loop_cond".into(),
        })),
    };

    let loop_cond_phi = IRInstruction::new(IRInstructionKind::Phi {
        ty: IRType::I32,
        incomings: vec![
            (
                IRValue::ConstInt {
                    value: 0,
                    ty: IRType::I32,
                },
                ENTRY_BLOCK_LABEL.into(),
            ),
            (
                IRValue::InstructionRef {
                    id: "%9".into(),
                    ty: IRType::I32,
                },
                "loop_body".into(),
            ),
        ],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let cmp_len = IRInstruction::new(IRInstructionKind::ICmp {
        op: IRICmpOp::Slt,
        lhs: IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::InstructionRef {
            id: "%2".into(),
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%4".into(),
            ty: IRType::I1,
        },
        Some(IRType::I1),
    );

    let loop_cond_block = IRBasicBlock {
        label: "loop_cond".into(),
        instructions: vec![loop_cond_phi, cmp_len],
        terminator: Some(IRInstruction::new(IRInstructionKind::CondBr {
            cond: IRValue::InstructionRef {
                id: "%4".into(),
                ty: IRType::I1,
            },
            then_dest: "loop_body".into(),
            else_dest: "loop_end".into(),
        })),
    };

    let gep = IRInstruction::new(IRInstructionKind::GetElementPtr {
        base: IRValue::InstructionRef {
            id: "%1".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        indices: vec![IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        }],
        in_bounds: true,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%5".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        Some(IRType::Ptr(Box::new(IRType::I8))),
    );

    let load_char = IRInstruction::new(IRInstructionKind::Load {
        ptr: IRValue::InstructionRef {
            id: "%5".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        align: None,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%6".into(),
            ty: IRType::I8,
        },
        Some(IRType::I8),
    );

    let cast_char = IRInstruction::new(IRInstructionKind::Cast {
        op: IRCastOp::SExt,
        value: IRValue::InstructionRef {
            id: "%6".into(),
            ty: IRType::I8,
        },
        to_type: IRType::I32,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%7".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let putchar_call = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct("putchar".into()),
        args: vec![IRValue::InstructionRef {
            id: "%7".into(),
            ty: IRType::I32,
        }],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%8".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let next_index = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Add,
        lhs: IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 1,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%9".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let loop_body_block = IRBasicBlock {
        label: "loop_body".into(),
        instructions: vec![gep, load_char, cast_char, putchar_call, next_index],
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "loop_cond".into(),
        })),
    };

    let loop_end_block = IRBasicBlock {
        label: "loop_end".into(),
        instructions: Vec::new(),
        terminator: Some(IRInstruction::new(IRInstructionKind::Ret { value: None })),
    };

    IRFunction {
        name: mangle_symbol_name("print"),
        params: vec![("arg0".into(), arg_ty)],
        return_type: IRType::Void,
        basic_blocks: vec![
            entry_block,
            loop_cond_block,
            loop_body_block,
            loop_end_block,
        ],
    }
}

fn build_println(type_ctx: &TypeContext) -> IRFunction {
    let sig = type_ctx
        .get_function("println")
        .expect("builtin signature must exist");
    let arg_ty = rx_to_ir_type(type_ctx, &sig.params()[0]);

    let call_print = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct(mangle_symbol_name("print")),
        args: vec![IRValue::Argument {
            index: 0,
            name: Some("arg0".into()),
            ty: arg_ty.clone(),
        }],
    });

    let newline_call = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct("putchar".into()),
        args: vec![IRValue::ConstInt {
            value: 10,
            ty: IRType::I32,
        }],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let entry_block = IRBasicBlock {
        label: ENTRY_BLOCK_LABEL.into(),
        instructions: vec![call_print, newline_call],
        terminator: Some(IRInstruction::new(IRInstructionKind::Ret { value: None })),
    };

    IRFunction {
        name: mangle_symbol_name("println"),
        params: vec![("arg0".into(), arg_ty)],
        return_type: IRType::Void,
        basic_blocks: vec![entry_block],
    }
}

fn build_print_int(_type_ctx: &TypeContext) -> IRFunction {
    let arg_ty = IRType::I32;
    let array_ty = IRType::Array {
        elem_type: Box::new(IRType::I8),
        size: 16,
    };

    let alloca_buf = IRInstruction::new(IRInstructionKind::Alloca {
        alloc_type: array_ty.clone(),
        align: None,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::Ptr(Box::new(array_ty.clone())),
        },
        Some(IRType::Ptr(Box::new(array_ty.clone()))),
    );

    let is_negative = IRInstruction::new(IRInstructionKind::ICmp {
        op: IRICmpOp::Slt,
        lhs: IRValue::Argument {
            index: 0,
            name: Some("arg0".into()),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 0,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%1".into(),
            ty: IRType::I1,
        },
        Some(IRType::I1),
    );

    let entry_block = IRBasicBlock {
        label: ENTRY_BLOCK_LABEL.into(),
        instructions: vec![alloca_buf, is_negative],
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "extract_loop".into(),
        })),
    };

    let loop_phi_value = IRInstruction::new(IRInstructionKind::Phi {
        ty: IRType::I32,
        incomings: vec![
            (
                IRValue::Argument {
                    index: 0,
                    name: Some("arg0".into()),
                    ty: IRType::I32,
                },
                ENTRY_BLOCK_LABEL.into(),
            ),
            (
                IRValue::InstructionRef {
                    id: "%11".into(),
                    ty: IRType::I32,
                },
                "extract_loop".into(),
            ),
        ],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%2".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let loop_phi_index = IRInstruction::new(IRInstructionKind::Phi {
        ty: IRType::I32,
        incomings: vec![
            (
                IRValue::ConstInt {
                    value: 0,
                    ty: IRType::I32,
                },
                ENTRY_BLOCK_LABEL.into(),
            ),
            (
                IRValue::InstructionRef {
                    id: "%12".into(),
                    ty: IRType::I32,
                },
                "extract_loop".into(),
            ),
        ],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let remainder = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::SRem,
        lhs: IRValue::InstructionRef {
            id: "%2".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 10,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%4".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let remainder_is_neg = IRInstruction::new(IRInstructionKind::ICmp {
        op: IRICmpOp::Slt,
        lhs: IRValue::InstructionRef {
            id: "%4".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 0,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%5".into(),
            ty: IRType::I1,
        },
        Some(IRType::I1),
    );

    let negated_remainder = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Sub,
        lhs: IRValue::ConstInt {
            value: 0,
            ty: IRType::I32,
        },
        rhs: IRValue::InstructionRef {
            id: "%4".into(),
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%6".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let abs_remainder = IRInstruction::new(IRInstructionKind::Select {
        cond: IRValue::InstructionRef {
            id: "%5".into(),
            ty: IRType::I1,
        },
        true_val: IRValue::InstructionRef {
            id: "%6".into(),
            ty: IRType::I32,
        },
        false_val: IRValue::InstructionRef {
            id: "%4".into(),
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%7".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let digit_char = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Add,
        lhs: IRValue::InstructionRef {
            id: "%7".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 48,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%8".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let digit_char_i8 = IRInstruction::new(IRInstructionKind::Cast {
        op: IRCastOp::Trunc,
        value: IRValue::InstructionRef {
            id: "%8".into(),
            ty: IRType::I32,
        },
        to_type: IRType::I8,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%9".into(),
            ty: IRType::I8,
        },
        Some(IRType::I8),
    );

    let digit_ptr = IRInstruction::new(IRInstructionKind::GetElementPtr {
        base: IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::Ptr(Box::new(array_ty.clone())),
        },
        indices: vec![
            IRValue::ConstInt {
                value: 0,
                ty: IRType::I32,
            },
            IRValue::InstructionRef {
                id: "%3".into(),
                ty: IRType::I32,
            },
        ],
        in_bounds: true,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%10".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        Some(IRType::Ptr(Box::new(IRType::I8))),
    );

    let store_digit = IRInstruction::new(IRInstructionKind::Store {
        value: IRValue::InstructionRef {
            id: "%9".into(),
            ty: IRType::I8,
        },
        ptr: IRValue::InstructionRef {
            id: "%10".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        align: None,
    });

    let divided_value = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::SDiv,
        lhs: IRValue::InstructionRef {
            id: "%2".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 10,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%11".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let next_index = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Add,
        lhs: IRValue::InstructionRef {
            id: "%3".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 1,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%12".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let division_done = IRInstruction::new(IRInstructionKind::ICmp {
        op: IRICmpOp::Eq,
        lhs: IRValue::InstructionRef {
            id: "%11".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 0,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%13".into(),
            ty: IRType::I1,
        },
        Some(IRType::I1),
    );

    let extract_loop_block = IRBasicBlock {
        label: "extract_loop".into(),
        instructions: vec![
            loop_phi_value,
            loop_phi_index,
            remainder,
            remainder_is_neg,
            negated_remainder,
            abs_remainder,
            digit_char,
            digit_char_i8,
            digit_ptr,
            store_digit,
            divided_value,
            next_index,
            division_done,
        ],
        terminator: Some(IRInstruction::new(IRInstructionKind::CondBr {
            cond: IRValue::InstructionRef {
                id: "%13".into(),
                ty: IRType::I1,
            },
            then_dest: "maybe_neg".into(),
            else_dest: "extract_loop".into(),
        })),
    };

    let maybe_neg_block = IRBasicBlock {
        label: "maybe_neg".into(),
        instructions: Vec::new(),
        terminator: Some(IRInstruction::new(IRInstructionKind::CondBr {
            cond: IRValue::InstructionRef {
                id: "%1".into(),
                ty: IRType::I1,
            },
            then_dest: "neg_store".into(),
            else_dest: "output_setup".into(),
        })),
    };

    let neg_ptr = IRInstruction::new(IRInstructionKind::GetElementPtr {
        base: IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::Ptr(Box::new(array_ty.clone())),
        },
        indices: vec![
            IRValue::ConstInt {
                value: 0,
                ty: IRType::I32,
            },
            IRValue::InstructionRef {
                id: "%12".into(),
                ty: IRType::I32,
            },
        ],
        in_bounds: true,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%14".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        Some(IRType::Ptr(Box::new(IRType::I8))),
    );

    let store_neg = IRInstruction::new(IRInstructionKind::Store {
        value: IRValue::ConstInt {
            value: 45,
            ty: IRType::I8,
        },
        ptr: IRValue::InstructionRef {
            id: "%14".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        align: None,
    });

    let neg_index = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Add,
        lhs: IRValue::InstructionRef {
            id: "%12".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 1,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%15".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let neg_store_block = IRBasicBlock {
        label: "neg_store".into(),
        instructions: vec![neg_ptr, store_neg, neg_index],
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "output_setup".into(),
        })),
    };

    let output_len_phi = IRInstruction::new(IRInstructionKind::Phi {
        ty: IRType::I32,
        incomings: vec![
            (
                IRValue::InstructionRef {
                    id: "%12".into(),
                    ty: IRType::I32,
                },
                "maybe_neg".into(),
            ),
            (
                IRValue::InstructionRef {
                    id: "%15".into(),
                    ty: IRType::I32,
                },
                "neg_store".into(),
            ),
        ],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%16".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let output_setup_block = IRBasicBlock {
        label: "output_setup".into(),
        instructions: vec![output_len_phi],
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "output_loop_cond".into(),
        })),
    };

    let output_phi = IRInstruction::new(IRInstructionKind::Phi {
        ty: IRType::I32,
        incomings: vec![
            (
                IRValue::InstructionRef {
                    id: "%16".into(),
                    ty: IRType::I32,
                },
                "output_setup".into(),
            ),
            (
                IRValue::InstructionRef {
                    id: "%19".into(),
                    ty: IRType::I32,
                },
                "output_loop_body".into(),
            ),
        ],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%17".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let loop_done = IRInstruction::new(IRInstructionKind::ICmp {
        op: IRICmpOp::Eq,
        lhs: IRValue::InstructionRef {
            id: "%17".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 0,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%18".into(),
            ty: IRType::I1,
        },
        Some(IRType::I1),
    );

    let output_cond_block = IRBasicBlock {
        label: "output_loop_cond".into(),
        instructions: vec![output_phi, loop_done],
        terminator: Some(IRInstruction::new(IRInstructionKind::CondBr {
            cond: IRValue::InstructionRef {
                id: "%18".into(),
                ty: IRType::I1,
            },
            then_dest: "output_end".into(),
            else_dest: "output_loop_body".into(),
        })),
    };

    let decrement = IRInstruction::new(IRInstructionKind::Binary {
        op: IRBinaryOp::Sub,
        lhs: IRValue::InstructionRef {
            id: "%17".into(),
            ty: IRType::I32,
        },
        rhs: IRValue::ConstInt {
            value: 1,
            ty: IRType::I32,
        },
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%19".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let output_ptr = IRInstruction::new(IRInstructionKind::GetElementPtr {
        base: IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::Ptr(Box::new(array_ty.clone())),
        },
        indices: vec![
            IRValue::ConstInt {
                value: 0,
                ty: IRType::I32,
            },
            IRValue::InstructionRef {
                id: "%19".into(),
                ty: IRType::I32,
            },
        ],
        in_bounds: true,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%20".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        Some(IRType::Ptr(Box::new(IRType::I8))),
    );

    let load_char = IRInstruction::new(IRInstructionKind::Load {
        ptr: IRValue::InstructionRef {
            id: "%20".into(),
            ty: IRType::Ptr(Box::new(IRType::I8)),
        },
        align: None,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%21".into(),
            ty: IRType::I8,
        },
        Some(IRType::I8),
    );

    let char_i32 = IRInstruction::new(IRInstructionKind::Cast {
        op: IRCastOp::SExt,
        value: IRValue::InstructionRef {
            id: "%21".into(),
            ty: IRType::I8,
        },
        to_type: IRType::I32,
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%22".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let putchar_call = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct("putchar".into()),
        args: vec![IRValue::InstructionRef {
            id: "%22".into(),
            ty: IRType::I32,
        }],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%23".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let output_body_block = IRBasicBlock {
        label: "output_loop_body".into(),
        instructions: vec![decrement, output_ptr, load_char, char_i32, putchar_call],
        terminator: Some(IRInstruction::new(IRInstructionKind::Br {
            dest: "output_loop_cond".into(),
        })),
    };

    let output_end_block = IRBasicBlock {
        label: "output_end".into(),
        instructions: Vec::new(),
        terminator: Some(IRInstruction::new(IRInstructionKind::Ret { value: None })),
    };

    IRFunction {
        name: mangle_symbol_name("printInt"),
        params: vec![("arg0".into(), arg_ty)],
        return_type: IRType::Void,
        basic_blocks: vec![
            entry_block,
            extract_loop_block,
            maybe_neg_block,
            neg_store_block,
            output_setup_block,
            output_cond_block,
            output_body_block,
            output_end_block,
        ],
    }
}

fn build_println_int(_type_ctx: &TypeContext) -> IRFunction {
    let arg_ty = IRType::I32;

    let call_print_int = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct(mangle_symbol_name("printInt")),
        args: vec![IRValue::Argument {
            index: 0,
            name: Some("arg0".into()),
            ty: IRType::I32,
        }],
    });

    let newline_call = IRInstruction::new(IRInstructionKind::Call {
        callee: CallTarget::Direct("putchar".into()),
        args: vec![IRValue::ConstInt {
            value: 10,
            ty: IRType::I32,
        }],
    })
    .with_result(
        IRValue::InstructionRef {
            id: "%0".into(),
            ty: IRType::I32,
        },
        Some(IRType::I32),
    );

    let entry_block = IRBasicBlock {
        label: ENTRY_BLOCK_LABEL.into(),
        instructions: vec![call_print_int, newline_call],
        terminator: Some(IRInstruction::new(IRInstructionKind::Ret { value: None })),
    };

    IRFunction {
        name: mangle_symbol_name("printlnInt"),
        params: vec![("arg0".into(), arg_ty)],
        return_type: IRType::Void,
        basic_blocks: vec![entry_block],
    }
}
