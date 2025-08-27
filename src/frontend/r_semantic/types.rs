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
    Struct(String),
    Ref(Box<RxType>, bool),

    // bottom type: denotes divergence (e.g., return)
    Never,
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
            RxType::Struct(s) => write!(f, "{s}"),
            RxType::Ref(inner_type, mutable) => {
                if *mutable {
                    write!(f, "&mut {}", inner_type)
                } else {
                    write!(f, "&{}", inner_type)
                }
            }
            RxType::Never => write!(f, "!"),
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

    pub fn is_never(&self) -> bool {
        matches!(self, RxType::Never)
    }

    pub fn unify(a: &RxType, b: &RxType) -> Option<RxType> {
        if a.is_never() {
            Some(b.clone())
        } else if b.is_never() {
            Some(a.clone())
        } else if a == b {
            Some(a.clone())
        } else {
            None
        }
    }
}
