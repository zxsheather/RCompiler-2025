use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct IRModule {
    pub name: String,
    pub funcs: Vec<IRFunction>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRFunction {
    pub name: String,
    pub params: Vec<(String, IRType)>,
    pub return_type: IRType,
    pub basic_blocks: Vec<IRBasicBlock>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRBasicBlock {
    pub label: String,
    pub instructions: Vec<IRInstruction>,
    pub terminator: Option<IRInstruction>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRInstruction {
    pub result: Option<IRValue>,
    pub ty: Option<IRType>,
    pub kind: IRInstructionKind,
    pub debug: Option<DebugLocation>,
}

impl IRInstruction {
    pub fn new(kind: IRInstructionKind) -> Self {
        Self {
            result: None,
            ty: None,
            kind,
            debug: None,
        }
    }

    pub fn with_result(mut self, result: IRValue, ty: Option<IRType>) -> Self {
        self.result = Some(result);
        self.ty = ty;
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRInstructionKind {
    Alloca {
        alloc_type: IRType,
        align: Option<usize>,
    },
    Load {
        ptr: IRValue,
        align: Option<usize>,
    },
    Store {
        value: IRValue,
        ptr: IRValue,
        align: Option<usize>,
    },
    GetElementPtr {
        base: IRValue,
        indices: Vec<IRValue>,
        in_bounds: bool,
    },
    Binary {
        op: IRBinaryOp,
        lhs: IRValue,
        rhs: IRValue,
    },
    ICmp {
        op: IRICmpOp,
        lhs: IRValue,
        rhs: IRValue,
    },
    Cast {
        op: IRCastOp,
        value: IRValue,
        to_type: IRType,
    },
    Br {
        dest: String,
    },
    CondBr {
        cond: IRValue,
        then_dest: String,
        else_dest: String,
    },
    Call {
        callee: CallTarget,
        args: Vec<IRValue>,
    },
    Ret {
        value: Option<IRValue>,
    },
    Phi {
        ty: IRType,
        incomings: Vec<(IRValue, String)>,
    },
    Select {
        cond: IRValue,
        true_val: IRValue,
        false_val: IRValue,
    },
    InsertValue {
        aggregate: IRValue,
        value: IRValue,
        indices: Vec<usize>,
    },
    ExtractValue {
        aggregate: IRValue,
        indices: Vec<usize>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallTarget {
    Direct(String),
    #[allow(dead_code)]
    Indirect(IRValue),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRBinaryOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

impl fmt::Display for IRBinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op_str = match self {
            IRBinaryOp::Add => "add",
            IRBinaryOp::Sub => "sub",
            IRBinaryOp::Mul => "mul",
            IRBinaryOp::UDiv => "udiv",
            IRBinaryOp::SDiv => "sdiv",
            IRBinaryOp::URem => "urem",
            IRBinaryOp::SRem => "srem",
            IRBinaryOp::And => "and",
            IRBinaryOp::Or => "or",
            IRBinaryOp::Xor => "xor",
            IRBinaryOp::Shl => "shl",
            IRBinaryOp::LShr => "lshr",
            IRBinaryOp::AShr => "ashr",
        };
        write!(f, "{op_str}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRCastOp {
    Trunc,
    ZExt,
    SExt,
    PtrToInt,
    IntToPtr,
    BitCast,
}

impl fmt::Display for IRCastOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op_str = match self {
            IRCastOp::Trunc => "trunc",
            IRCastOp::ZExt => "zext",
            IRCastOp::SExt => "sext",
            IRCastOp::PtrToInt => "ptrtoint",
            IRCastOp::IntToPtr => "inttoptr",
            IRCastOp::BitCast => "bitcast",
        };
        write!(f, "{op_str}")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IRICmpOp {
    Eq,
    Ne,
    Sgt,
    Sge,
    Slt,
    Sle,
    Ugt,
    Uge,
    Ult,
    Ule,
}

impl fmt::Display for IRICmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op_str = match self {
            IRICmpOp::Eq => "eq",
            IRICmpOp::Ne => "ne",
            IRICmpOp::Sgt => "sgt",
            IRICmpOp::Sge => "sge",
            IRICmpOp::Slt => "slt",
            IRICmpOp::Sle => "sle",
            IRICmpOp::Ugt => "ugt",
            IRICmpOp::Uge => "uge",
            IRICmpOp::Ult => "ult",
            IRICmpOp::Ule => "ule",
        };
        write!(f, "{op_str}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRType {
    Void,
    I1,
    I8,
    I32,
    Ptr(Box<IRType>),
    Struct { fields: Vec<IRType> },
    Array { elem_type: Box<IRType>, size: usize },
}

impl IRType {
    pub fn is_integer_type(&self) -> bool {
        matches!(self, IRType::I1 | IRType::I8 | IRType::I32)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRValue {
    ConstInt {
        value: i64,
        ty: IRType,
    },
    #[allow(dead_code)]
    ConstNull(IRType),
    Undef(IRType),
    #[allow(dead_code)]
    Local {
        name: String,
        ty: IRType,
    },
    #[allow(dead_code)]
    Global {
        name: String,
        ty: IRType,
    },
    Argument {
        index: usize,
        name: Option<String>,
        ty: IRType,
    },
    InstructionRef {
        id: String,
        ty: IRType,
    },
}

impl IRValue {
    pub fn get_type(&self) -> IRType {
        match self {
            IRValue::ConstInt { ty, .. } => ty.clone(),
            IRValue::ConstNull(ty) => ty.clone(),
            IRValue::Undef(ty) => ty.clone(),
            IRValue::Local { ty, .. } => ty.clone(),
            IRValue::Global { ty, .. } => ty.clone(),
            IRValue::Argument { ty, .. } => ty.clone(),
            IRValue::InstructionRef { ty, .. } => ty.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DebugLocation {
    pub line: usize,
    pub column: usize,
}
