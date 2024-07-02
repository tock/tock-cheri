//! A slightly better asm context than asm!.
//! Allows inline concat with ';' and provides some FOR_EACH / FOR_RANGE style helpers
//! Some of this has become RISCV specific, probably best to factor that out

#[macro_export]
macro_rules! easm_help {
    // Usage FOR_EACH(Var in [...] : "code")
    // If Var were "v" Code should refer to "\\v"
    // "FOR_N" will expand to a completely unrolled loop.
    {@PROC($ln : expr, FOR_EACH($v : literal in [$($vals:literal),*] : $($code : expr)+), $($ins:tt)*) -> @RES($($out:tt)*)} =>
    // It is hard to do variable substitution in rust without declaring another macro
    // Might as well asm macros here
        {$crate::easm_help!(@PROC(concat!($ln,"f"), $($ins)*) -> @RES($($out)* concat!(
            ".macro _foreach_help_", $ln, " ", $v, "
                ", $($code),+ ,"
             .endm
             .set FOR_N, 0
             ", $("_foreach_help_", $ln, " ", $vals, "; .set FOR_N, FOR_N + 1;"),*
        ),))};
    // Usage FOR_RANGE(Var in lower ... upper "code")
    // Bit of a hack, will only work with a limited range of 0..32, but gives literals like 3 instead of 1+1+1.
    {@PROC($ln : expr, FOR_RANGE($v : literal in $l : literal .. $u: literal : $($code : expr)+), $($ins:tt)*) -> @RES($($out:tt)*)} =>
        {$crate::easm_help!(@PROC($ln, FOR_EACH($v
            in ["0","1","2","3","4","5","6","7","8","9","10","11","12","13","14","15","16","17","18","19","20","21","22","23","24","25","26","27","28","29","30","31","32"]
            : ".if \\" $v " >= " $l " && \\" $v "<" $u "\n" $($code)+ " \n .endif\n"), $($ins)*) -> @RES($($out)*))};

    // ; starts C style string concat (until next ,) for easier macro insertion
    {@PROC($ln : expr, ; $($As : expr)* , $($ins:tt)*) -> @RES($($out:tt)*)} =>
        {$crate::easm_help!(@PROC($ln, $($ins)*) -> @RES($($out)* concat!($($As),*),))};

    // Unwrap when nothing left to process
    {@PROC($ln : expr,) -> @RES($($out:tt)*)} =>
        {core::arch::asm!($($out)*)};

    // Output a common prelude to include helpers.
    // Currently not being used.
    {@PROC($ln : expr, @PRELUDE, $($ins:tt)*) -> @RES($($out:tt)*)} =>
        {$crate::easm_help!(@PROC($ln, $($ins)*) -> @RES(
        "", $($out)*))};

    // Not one of the new easm terms, pass it through
    {@PROC($ln : expr, $e : tt $($ins:tt)*) -> @RES($($out:tt)*)} =>
        {$crate::easm_help!(@PROC($ln, $($ins)*) -> @RES($($out)* $e))};
    {@PROC($ln : expr, $e : tt) -> @RES($($out:tt)*)} =>
        {$crate::easm_help!(@PROC($ln,) -> @RES($($out)* $e))};
}

#[macro_export]
macro_rules! easm {
    // Wrap in a @PROC(...) -> @RES(...) term to ensure that partial results parse.
    {$($tail:tt)*} =>
        {$crate::easm_help!(@PROC(line!(), @PRELUDE, $($tail)*) -> @RES())};
}
