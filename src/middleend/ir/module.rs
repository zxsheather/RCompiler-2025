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

    pub fn with_debug(mut self, debug: DebugLocation) -> Self {
        self.debug = Some(debug);
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum CallTarget {
    Direct(String),
    Indirect(IRValue),
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRNode {
    Instruction(IRInstruction),
    Value(IRValue),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IRCastOp {
    Trunc,
    ZExt,
    SExt,
    PtrToInt,
    IntToPtr,
    BitCast,
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

#[derive(Debug, Clone, PartialEq)]
pub enum IRValue {
    ConstInt {
        value: i64,
        ty: IRType,
    },
    ConstNull(IRType),
    Undef(IRType),
    Local {
        name: String,
        ty: IRType,
    },
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
