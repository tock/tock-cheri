//! Provides a helper to initialise constants (such as integers) provided via environment variables
//! at compile time. This allows passing configuration constants from the command line to program.

use core::panic;

/// Usage:
/// ```ignore
///     use misc::const_env_int;
///     const_env_int!(pub MY_U8:u8);
///     const_env_int!(MY_SIZE:usize);
///     const_env_int!(pub MY_VAR:u8 = default 77);
/// ```
///
/// Format for numbers passed is [0x|0b]? [0..9]* [K|M|G|Ki|Mi|Gi]?
///
/// If the command line parameter is not set, the default will be chosen if one has been specified.
/// Otherwise, a compile time panic will occur.
///
#[macro_export]
macro_rules! const_env_int {
    ($vis:vis $name:ident : $ty:ty $(= default $e : expr)?) => (
        $vis const $name : $ty = {
             $crate::parse_env_int!($name : $ty $(= default $e)?)
        };
    );
}

/// Usage:
///     parse_env_int!(Name : Ty (= default Value)?)
#[macro_export]
macro_rules! parse_env_int {
    ($name:ident : $ty : ty = default $e : expr) => (
        {
            const RESULT : $ty = match option_env!(stringify!($name)) {
                Some (s) =>  $crate::const_env::const_parse(s) as $ty,
                None => $e
            };
            RESULT
        }
    );
    ($name:ident : $ty : ty) => (
        $crate::parse_env_int!($name : $ty = default panic!("Environment variable not set"))
    );
}

// Need to rewrite most of this logic that probably exists in core because it has to be const fn
pub const fn const_parse(s: &str) -> u64 {
    let mut res = 0u64;
    let mut i = 0usize;

    // Trim leading whitespace
    while i < s.len() && s.as_bytes()[i] == b' ' {
        i += 1;
    }

    // Get base from prefix (either 0x, 0b, or else base 10. Base 8 is rubbish)
    let base = {
        if (s.len() - i) >= 2 && s.as_bytes()[i] == b'0' {
            match s.as_bytes()[i + 1] {
                b'x' | b'X' => {
                    i += 2;
                    16
                }
                b'b' | b'B' => {
                    i += 2;
                    2
                }
                _ => 10,
            }
        } else {
            10
        }
    };

    // Parse number
    while i < s.len() {
        let mut c = s.as_bytes()[i];
        let val = if c >= b'0' && c <= b'9' {
            c - b'0'
        } else {
            if c >= b'a' {
                c -= b'a' - b'A';
            }
            if c >= b'A' && c <= b'F' {
                (c - b'A') + 10
            } else {
                break;
            }
        };
        res *= base;
        res += val as u64;
        i += 1;
    }

    // Parse suffixes
    if i != s.len() && s.as_bytes()[i] != b' ' {
        let c = s.as_bytes()[i];
        i += 1;
        let mult = if i == s.len() {
            1000
        } else {
            let c2 = s.as_bytes()[i];
            i += 1;
            if c2 == b'i' {
                1024
            } else if c2 == b' ' {
                1000
            } else {
                panic!("Invalid character of suffix");
            }
        };
        res *= match c {
            b'k' | b'K' => mult,
            b'm' | b'M' => mult * mult,
            b'g' | b'G' => mult * mult * mult,
            _ => panic!("Suffix should start with K, M, or G"),
        };
    }

    // Trim trailing whitespace
    while i != s.len() && s.as_bytes()[i] == b' ' {
        i += 1;
    }

    // Error check
    if i != s.len() {
        panic!("Invalid suffix");
    }

    res
}

#[cfg(test)]
mod tests {
    use crate::const_env::const_parse;

    #[test]
    fn test_base_10() {
        assert_eq!(const_parse("1"), 1);
        assert_eq!(const_parse("123"), 123);
        assert_eq!(const_parse("0"), 0);
        assert_eq!(const_parse("01"), 1);
    }

    #[test]
    fn test_base_16() {
        assert_eq!(const_parse("0x1"), 0x1);
        assert_eq!(const_parse("0x01"), 0x1);
        assert_eq!(const_parse("0X123"), 0x123);
        assert_eq!(const_parse("0x123aAaFf"), 0x123aAaFf);
        assert_eq!(const_parse("0x0"), 0x0);
    }

    #[test]
    fn test_base_2() {
        assert_eq!(const_parse("0b1"), 0b1);
        assert_eq!(const_parse("0b01"), 0b01);
        assert_eq!(const_parse("0B101010"), 0b101010);
        assert_eq!(const_parse("0b0"), 0b0);
    }

    #[test]
    fn test_suffix() {
        assert_eq!(const_parse("0x123k"), 0x123 * 1000);
        assert_eq!(const_parse("0x123K"), 0x123 * 1000);
        assert_eq!(const_parse("0x123Ki"), 0x123 * 1024);
        assert_eq!(const_parse("0x123Ki"), 0x123 * 1024);
        assert_eq!(const_parse("0x123Mi"), 0x123 * 1024 * 1024);
        assert_eq!(const_parse("0x123Gi"), 0x123 * 1024 * 1024 * 1024);
    }

    #[test]
    fn test_trim() {
        assert_eq!(const_parse("0x123Ki  "), 0x123 * 1024);
        assert_eq!(const_parse(" 0x123Ki"), 0x123 * 1024);
        assert_eq!(const_parse(" 0x123Ki  "), 0x123 * 1024);
        assert_eq!(const_parse(" 0x123    "), 0x123);
    }

    #[test]
    fn test_default() {
        const_env_int!(THIS_WILL_NOT_BE_A_VAR : u32  = default 77);
        assert_eq!(THIS_WILL_NOT_BE_A_VAR, 77);
    }
}
