use std::fmt;

use crate::frontend::r_semantic::error::{SemanticError, SemanticResult};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RxType {
    I32,
    U32,
    ISize,
    USize,
    IntLiteral, // untyped integer literal (no suffix)
    Bool,
    String,
    Str,
    Char,
    Unit,
    Tuple(Vec<RxType>),
    Array(Box<RxType>, Option<usize>),
    Struct(String),
    // Enum(String),
    Ref(Box<RxType>, bool),

    // bottom type: denotes divergence (e.g., return)
    Never,

    // special type for main function
    MainReturn,
}

impl fmt::Display for RxType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RxType::I32 => write!(f, "i32"),
            RxType::U32 => write!(f, "u32"),
            RxType::ISize => write!(f, "isize"),
            RxType::USize => write!(f, "usize"),
            RxType::Bool => write!(f, "bool"),
            RxType::IntLiteral => write!(f, "<int>"),
            RxType::String => write!(f, "String"),
            RxType::Char => write!(f, "char"),
            RxType::Str => write!(f, "str"),
            RxType::Unit => write!(f, "()"),
            RxType::Tuple(elems_tys) => {
                let elems: Vec<String> = elems_tys.iter().map(|t| t.to_string()).collect();
                write!(f, "({})", elems.join(", "))
            }
            RxType::Array(t, sz) => {
                if let Some(n) = sz {
                    write!(f, "[{}; {}]", t, n)
                } else {
                    write!(f, "[{}]", t)
                }
            }
            RxType::Struct(s) => write!(f, "{s}"),
            // RxType::Enum(e) => write!(f, "{e}"),
            RxType::Ref(inner_type, mutable) => {
                if *mutable {
                    write!(f, "&mut {}", inner_type)
                } else {
                    write!(f, "&{}", inner_type)
                }
            }
            RxType::Never => write!(f, "!"),
            RxType::MainReturn => write!(f, "<main return>"),
        }
    }
}

impl RxType {
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            RxType::I32 | RxType::U32 | RxType::ISize | RxType::USize | RxType::IntLiteral
        )
    }

    pub fn is_concrete_int(&self) -> bool {
        matches!(
            self,
            RxType::I32 | RxType::U32 | RxType::ISize | RxType::USize
        )
    }

    pub fn is_never(&self) -> bool {
        matches!(self, RxType::Never)
    }

    pub fn unify(a: &RxType, b: &RxType) -> Option<RxType> {
        if a.is_never() {
            return Some(b.clone());
        }
        if b.is_never() {
            return Some(a.clone());
        }
        match (a, b) {
            // We allow main to return () implicitly, but not vice versa
            (RxType::MainReturn, RxType::Unit) => Some(RxType::MainReturn),

            (RxType::IntLiteral, t) if t.is_concrete_int() => Some(t.clone()),
            (t, RxType::IntLiteral) if t.is_concrete_int() => Some(t.clone()),
            (RxType::Array(elem_a, size_a), RxType::Array(elem_b, size_b)) if size_a == size_b => {
                let Some(new_ty) = RxType::unify(&elem_a, &elem_b) else {
                    return None;
                };
                Some(RxType::Array(Box::new(new_ty), *size_a))
            }
            (RxType::Ref(inner_a, mut_a), RxType::Ref(inner_b, mut_b)) => {
                let Some(new_ty) = RxType::unify(&inner_a, &inner_b) else {
                    return None;
                };
                if !mut_a && *mut_b {
                    // &T with &mut T => &T
                    Some(RxType::Ref(Box::new(new_ty), false))
                } else if *mut_a && !mut_b {
                    // &mut T with &T => &T
                    Some(RxType::Ref(Box::new(new_ty), false))
                } else if mut_a == mut_b {
                    // same mutability
                    Some(RxType::Ref(Box::new(new_ty), *mut_a))
                } else {
                    None
                }
            }
            (RxType::Tuple(elems_a), RxType::Tuple(elems_b)) if elems_a.len() == elems_b.len() => {
                let mut new_elems = Vec::new();
                for (elem_a, elem_b) in elems_a.iter().zip(elems_b.iter()) {
                    let Some(new_ty) = RxType::unify(elem_a, elem_b) else {
                        return None;
                    };
                    new_elems.push(new_ty);
                }
                Some(RxType::Tuple(new_elems))
            }
            _ => {
                if a == b {
                    Some(a.clone())
                } else {
                    None
                }
            }
        }
    }

    pub fn method_key(&self) -> String {
        match self {
            RxType::Struct(name) => name.clone(),
            RxType::U32 => "u32".to_string(),
            RxType::USize => "usize".to_string(),
            RxType::String => "String".to_string(),
            RxType::Char => "char".to_string(),
            RxType::Str => "str".to_string(),
            RxType::Array(_, _) => "Array".to_string(),
            RxType::Ref(inner, _) => inner.method_key(),
            RxType::IntLiteral => "u32".to_string(),
            _ => "".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum RxValue {
    I32(i32),
    U32(u32),
    ISize(isize),
    USize(usize),
    IntLiteral(i64),
    Bool(bool),
    String(String),
    Char(char),
    Str(&'static str),
}

impl RxValue {
    pub fn get_type(&self) -> RxType {
        match self {
            RxValue::I32(_) => RxType::I32,
            RxValue::U32(_) => RxType::U32,
            RxValue::ISize(_) => RxType::ISize,
            RxValue::USize(_) => RxType::USize,
            RxValue::IntLiteral(_) => RxType::IntLiteral,
            RxValue::Bool(_) => RxType::Bool,
            RxValue::String(_) => RxType::String,
            RxValue::Char(_) => RxType::Char,
            RxValue::Str(_) => RxType::Str,
        }
    }

    pub fn as_usize(&self) -> SemanticResult<usize> {
        match self {
            RxValue::USize(v) => Ok(*v),
            RxValue::IntLiteral(v) if *v >= 0 => Ok(*v as usize),
            _ => Err(SemanticError::InternalError {
                message: format!("Cannot convert {:?} to usize", self),
            }),
        }
    }
}
