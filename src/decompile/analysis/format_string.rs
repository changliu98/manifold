//! Variadic argument types named by a printf/scanf conversion string.
//!
//! C11 7.21.6.1 (fprintf) and 7.21.6.2 (fscanf), plus the glibc `%m`
//! conversion and `m` allocation modifier. A conversion specification names
//! the type the callee reads for its argument, so it is ABI evidence about the
//! caller's value, exactly like a prototype parameter. Anything outside this
//! grammar (register_printf_function conversions, mixed positional forms, a
//! truncated specification) makes no claim at all rather than a partial one.

use crate::x86::types::XType;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Length {
    None,
    Char,     // hh
    Short,    // h
    Long,     // l
    LongLong, // ll, q
    Max,      // j
    Size,     // z, Z
    Ptrdiff,  // t
    Double,   // L
}

fn length(bytes: &[u8], mut i: usize) -> (Length, usize) {
    let at = |k: usize| bytes.get(k).copied();
    let len = match at(i) {
        Some(b'h') if at(i + 1) == Some(b'h') => {
            i += 1;
            Length::Char
        }
        Some(b'h') => Length::Short,
        Some(b'l') if at(i + 1) == Some(b'l') => {
            i += 1;
            Length::LongLong
        }
        Some(b'l') => Length::Long,
        Some(b'q') => Length::LongLong,
        Some(b'j') => Length::Max,
        Some(b'z') | Some(b'Z') => Length::Size,
        Some(b't') => Length::Ptrdiff,
        Some(b'L') => Length::Double,
        _ => return (Length::None, i),
    };
    (len, i + 1)
}

fn digits(bytes: &[u8], mut i: usize) -> (Option<usize>, usize) {
    let start = i;
    let mut value = 0usize;
    while let Some(d) = bytes.get(i).filter(|b| b.is_ascii_digit()) {
        value = value.saturating_mul(10).saturating_add((d - b'0') as usize);
        i += 1;
    }
    ((i > start).then_some(value), i)
}

/// `n$` at `i`: Some(zero-based argument) and the index after `$`.
fn position(bytes: &[u8], i: usize) -> Option<(usize, usize)> {
    match digits(bytes, i) {
        (Some(n), j) if n > 0 && bytes.get(j) == Some(&b'$') => Some((n - 1, j + 1)),
        _ => None,
    }
}

/// None: not a C conversion. Some(None): consumes an argument whose type has
/// no XType (long double). Some(Some(t)): the argument's type.
fn printf_type(conversion: u8, length: Length) -> Option<Option<XType>> {
    use Length::*;
    Some(match conversion {
        b'd' | b'i' => Some(match length {
            None | Char | Short => XType::Xint,
            _ => XType::Xlong,
        }),
        b'o' | b'u' | b'x' | b'X' => Some(match length {
            None | Char | Short => XType::Xintunsigned,
            Size => XType::Xany64,
            Ptrdiff => XType::Xlong,
            _ => XType::Xlongunsigned,
        }),
        b'c' => Some(if length == Long {
            XType::Xintunsigned
        } else {
            XType::Xint
        }),
        b'C' => Some(XType::Xintunsigned),
        b's' => Some(if length == Long {
            XType::Xptr
        } else {
            XType::Xcharptr
        }),
        b'S' | b'p' => Some(XType::Xptr),
        b'n' => Some(if length == None {
            XType::Xintptr
        } else {
            XType::Xptr
        }),
        b'e' | b'E' | b'f' | b'F' | b'g' | b'G' | b'a' | b'A' => {
            (length != Double).then_some(XType::Xfloat)
        }
        _ => return Option::None,
    })
}

fn scanf_type(conversion: u8, length: Length, allocate: bool) -> Option<XType> {
    use Length::*;
    Some(match conversion {
        b'd' | b'i' | b'n' | b'o' | b'u' | b'x' | b'X' => match length {
            None => XType::Xintptr,
            Char => XType::Xcharptr,
            _ => XType::Xptr,
        },
        b's' | b'c' | b'[' if allocate => XType::Xcharptrptr,
        b's' | b'c' | b'[' if length == Long => XType::Xptr,
        b's' | b'c' | b'[' => XType::Xcharptr,
        b'e' | b'E' | b'f' | b'F' | b'g' | b'G' | b'a' | b'A' => match length {
            None => XType::Xsingleptr,
            Long => XType::Xfloatptr,
            _ => XType::Xptr,
        },
        b'p' => XType::Xptr,
        _ => return Option::None,
    })
}

/// (argument offset after the format string, type) for every variadic
/// argument the format names. Empty when the string is not well formed.
pub fn format_argument_types(format: &str, scanf: bool) -> Vec<(usize, XType)> {
    let bytes = format.as_bytes();
    let mut claims: Vec<(usize, Option<XType>)> = Vec::new();
    let mut next = 0usize;
    let mut positional: Option<bool> = None;
    let mut consume = |explicit: Option<usize>, ty: Option<XType>, positional: &mut Option<bool>| {
        match (*positional, explicit.is_some()) {
            (Some(p), q) if p != q => return false,
            _ => *positional = Some(explicit.is_some()),
        }
        let at = explicit.unwrap_or_else(|| {
            next += 1;
            next - 1
        });
        claims.push((at, ty));
        true
    };
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] != b'%' {
            i += 1;
            continue;
        }
        i += 1;
        match bytes.get(i) {
            Some(b'%') => {
                i += 1;
                continue;
            }
            None => return Vec::new(),
            _ => {}
        }
        let explicit = position(bytes, i).map(|(n, j)| {
            i = j;
            n
        });
        if scanf {
            let suppress = bytes.get(i) == Some(&b'*');
            if suppress {
                i += 1;
            }
            i = digits(bytes, i).1;
            let allocate = bytes.get(i) == Some(&b'm');
            if allocate {
                i += 1;
            }
            let (len, j) = length(bytes, i);
            i = j;
            let Some(&conversion) = bytes.get(i) else {
                return Vec::new();
            };
            i += 1;
            if conversion == b'[' {
                if bytes.get(i) == Some(&b'^') {
                    i += 1;
                }
                if bytes.get(i) == Some(&b']') {
                    i += 1;
                }
                while bytes.get(i).is_some_and(|b| *b != b']') {
                    i += 1;
                }
                if i >= bytes.len() {
                    return Vec::new();
                }
                i += 1;
            }
            let Some(ty) = scanf_type(conversion, len, allocate) else {
                return Vec::new();
            };
            if !suppress && !consume(explicit, Some(ty), &mut positional) {
                return Vec::new();
            }
        } else {
            while bytes.get(i).is_some_and(|b| b"-+ #0'I".contains(b)) {
                i += 1;
            }
            for precision in [false, true] {
                if precision {
                    if bytes.get(i) != Some(&b'.') {
                        break;
                    }
                    i += 1;
                }
                if bytes.get(i) == Some(&b'*') {
                    i += 1;
                    let star = position(bytes, i).map(|(n, j)| {
                        i = j;
                        n
                    });
                    if !consume(star, Some(XType::Xint), &mut positional) {
                        return Vec::new();
                    }
                } else {
                    i = digits(bytes, i).1;
                }
            }
            let (len, j) = length(bytes, i);
            i = j;
            let Some(&conversion) = bytes.get(i) else {
                return Vec::new();
            };
            i += 1;
            if conversion == b'm' {
                continue; // glibc: strerror(errno), no argument
            }
            let Some(ty) = printf_type(conversion, len) else {
                return Vec::new();
            };
            if !consume(explicit, ty, &mut positional) {
                return Vec::new();
            }
        }
    }
    // A positional argument named twice must agree with itself.
    claims.sort_by_key(|(at, _)| *at);
    let mut result: Vec<(usize, XType)> = Vec::new();
    for window in claims.windows(2) {
        if window[0].0 == window[1].0 && window[0].1 != window[1].1 {
            return Vec::new();
        }
    }
    for (at, ty) in claims {
        if let Some(ty) = ty {
            if result.last().is_none_or(|(last, _)| *last != at) {
                result.push((at, ty));
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use XType::*;

    #[test]
    fn printf_conversions_name_promoted_argument_types() {
        assert_eq!(
            format_argument_types("open(\"%s\"): %s\n", false),
            vec![(0, Xcharptr), (1, Xcharptr)]
        );
        assert_eq!(
            format_argument_types("%d %hhd %ld %zu %zd %lu %c %p %f %%", false),
            vec![
                (0, Xint),
                (1, Xint),
                (2, Xlong),
                (3, Xany64),
                (4, Xlong),
                (5, Xlongunsigned),
                (6, Xint),
                (7, Xptr),
                (8, Xfloat)
            ]
        );
    }

    #[test]
    fn star_width_and_precision_consume_int_arguments() {
        assert_eq!(
            format_argument_types("%-*.*s|%m|%5.2f", false),
            vec![(0, Xint), (1, Xint), (2, Xcharptr), (3, Xfloat)]
        );
    }

    #[test]
    fn long_double_consumes_a_position_without_a_claim() {
        assert_eq!(
            format_argument_types("%Lf %s", false),
            vec![(1, Xcharptr)]
        );
    }

    #[test]
    fn positional_arguments_are_mapped_and_must_agree() {
        assert_eq!(
            format_argument_types("%2$s %1$d %2$s", false),
            vec![(0, Xint), (1, Xcharptr)]
        );
        assert!(format_argument_types("%1$s %1$d", false).is_empty());
        assert!(format_argument_types("%1$s %d", false).is_empty());
    }

    #[test]
    fn unknown_or_truncated_specifications_make_no_claim() {
        assert!(format_argument_types("%s %Q", false).is_empty());
        assert!(format_argument_types("%s %", false).is_empty());
        assert!(format_argument_types("%[abc", true).is_empty());
    }

    #[test]
    fn scanf_conversions_name_destination_pointers() {
        assert_eq!(
            format_argument_types("%d %*d %ld %lf %f %s %ms %[^,] %hhu %n", true),
            vec![
                (0, Xintptr),
                (1, Xptr),
                (2, Xfloatptr),
                (3, Xsingleptr),
                (4, Xcharptr),
                (5, Xcharptrptr),
                (6, Xcharptr),
                (7, Xcharptr),
                (8, Xintptr)
            ]
        );
    }
}
