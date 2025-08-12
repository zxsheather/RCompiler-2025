use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RxType {
    I32,
    U32,
    ISize,
    USize,
    Bool,
    String,
    Unit,
    Tuple(Vec<RxType>),
    Array(Box<RxType>, Option<usize>),
}

impl fmt::Display for RxType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RxType::I32 => write!(f, "i32"),
            RxType::U32 => write!(f, "u32"),
            RxType::ISize => write!(f, "isize"),
            RxType::USize => write!(f, "usize"),
            RxType::Bool => write!(f, "bool"),
            RxType::String => write!(f, "string"),
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
        }
    }
}

impl RxType {
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            RxType::I32 | RxType::U32 | RxType::ISize | RxType::USize
        )
    }
}
