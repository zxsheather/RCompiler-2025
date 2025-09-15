use crate::frontend::r_semantic::analyzer::{FuncSig, SelfKind};
use crate::frontend::r_semantic::types::RxType;

pub fn get_built_in_funcs() -> Vec<(&'static str, FuncSig)> {
    vec![
        (
            "print",
            FuncSig::new(
                vec![RxType::Ref(Box::new(RxType::Str), false)],
                RxType::Unit,
                SelfKind::None,
            ),
        ),
        (
            "println",
            FuncSig::new(
                vec![RxType::Ref(Box::new(RxType::Str), false)],
                RxType::Unit,
                SelfKind::None,
            ),
        ),
        (
            "printInt",
            FuncSig::new(vec![RxType::I32], RxType::Unit, SelfKind::None),
        ),
        (
            "printlnInt",
            FuncSig::new(vec![RxType::I32], RxType::Unit, SelfKind::None),
        ),
        (
            "getString",
            FuncSig::new(vec![], RxType::String, SelfKind::None),
        ),
        ("getInt", FuncSig::new(vec![], RxType::I32, SelfKind::None)),
        (
            "exit",
            FuncSig::new(vec![RxType::I32], RxType::MainReturn, SelfKind::None),
        ),
    ]
}

pub fn get_built_in_methods() -> Vec<(&'static str, &'static str, FuncSig)> {
    vec![
        (
            "String",
            "as_str",
            FuncSig::new(
                vec![],
                RxType::Ref(Box::new(RxType::Str), false),
                SelfKind::Borrowed { ty: RxType::String },
            ),
        ),
        (
            "String",
            "as_mut_str",
            FuncSig::new(
                vec![],
                RxType::Ref(Box::new(RxType::Str), true),
                SelfKind::Borrowed { ty: RxType::String },
            ),
        ),
        (
            "String",
            "append",
            FuncSig::new(
                vec![RxType::Ref(Box::new(RxType::Str), false)],
                RxType::Unit,
                SelfKind::BorrowedMut { ty: RxType::String },
            ),
        ),
        (
            "String",
            "len",
            FuncSig::new(
                vec![],
                RxType::USize,
                SelfKind::Borrowed { ty: RxType::String },
            ),
        ),
        (
            "str",
            "len",
            FuncSig::new(
                vec![],
                RxType::USize,
                SelfKind::Borrowed { ty: RxType::Str },
            ),
        ),
        (
            "Array",
            "len",
            FuncSig::new(
                vec![],
                RxType::USize,
                SelfKind::Borrowed {
                    ty: RxType::Array(Box::new(RxType::Never), None),
                },
            ),
        ),
        (
            "usize",
            "to_string",
            FuncSig::new(
                vec![],
                RxType::String,
                SelfKind::Borrowed { ty: RxType::USize },
            ),
        ),
        (
            "u32",
            "to_string",
            FuncSig::new(
                vec![],
                RxType::String,
                SelfKind::Borrowed { ty: RxType::U32 },
            ),
        ),
    ]
}

pub fn get_built_in_static_methods() -> Vec<(&'static str, &'static str, FuncSig)> {
    vec![(
        "String",
        "from",
        FuncSig::new(
            vec![RxType::Ref(Box::new(RxType::Str), false)],
            RxType::String,
            SelfKind::None,
        ),
    )]
}
