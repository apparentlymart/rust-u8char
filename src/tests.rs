use super::*;

#[test]
fn from_char() {
    table_test(
        |c| {
            let uc = u8char::from_char(c);
            (uc.to_byte_array(), uc.len())
        },
        &[
            TableTest {
                input: '\0',
                want: ([0x00, 0x00, 0x00, 0x00], 1),
            },
            TableTest {
                input: '\n',
                want: ([0x0a, 0x00, 0x00, 0x00], 1),
            },
            TableTest {
                input: '\u{00A4}',
                want: ([0xc2, 0xa4, 0x00, 0x00], 2),
            },
            TableTest {
                input: '\u{275D}',
                want: ([0xe2, 0x9d, 0x9d, 0x00], 3),
            },
            TableTest {
                input: '\u{275E}',
                want: ([0xe2, 0x9d, 0x9e, 0x00], 3),
            },
            TableTest {
                input: '\u{1FBC6}',
                want: ([0xf0, 0x9f, 0xaf, 0x86], 4),
            },
        ],
    );
}

#[test]
fn unstable_niches_value_range() {
    // This is here to confirm the value ranges we use when the unstable_niches
    // feature is available, which tell rustc it's allowed to use values outside
    // of our valid range to optimize the size of an enum containing u8char.

    let mut range_le = (0xffffffff_u32, 0x00000000_u32);
    let mut range_be = (0xffffffff_u32, 0x00000000_u32);
    for cp in 0..=0x10FFF {
        let Some(c) = char::from_u32(cp) else {
            continue;
        };
        let uc = u8char::from_char(c);
        let raw_le = u32::from_le_bytes(uc.to_byte_array());
        let raw_be = u32::from_be_bytes(uc.to_byte_array());
        if raw_le < range_le.0 {
            range_le.0 = raw_le;
        }
        if raw_be < range_be.0 {
            range_be.0 = raw_be;
        }
        if raw_le > range_le.1 {
            range_le.1 = raw_le;
        }
        if raw_be > range_be.1 {
            range_be.1 = raw_be;
        }
    }
    // The following should match the valid value ranges declared using
    // rustc_layout_scalar_valid_range_start and
    // rustc_layout_scalar_valid_range_end attributes on `utf8char`.
    assert_eq!(range_le, (0x00000000, 0xbfbf90f0));
    assert_eq!(range_be, (0x00000000, 0xf090bfbf));
}

#[test]
fn len_by_first_byte_consistent() {
    // This compares only successful results from length_by_initial_byte
    // to results of length_by_initial_byte_valid for the same input,
    // expecting them to always match.
    for b in 0_u8..=255 {
        let Ok(checked) = util::length_by_initial_byte(b) else {
            continue; // intentionally ignoring invalid starting bytes
        };
        let assumed = util::length_by_initial_byte_valid(b);
        assert_eq!(
            assumed, checked,
            "checked and assumed are equal for {b:#04x}",
        );
    }
}

struct TableTest<In, Out> {
    pub input: In,
    pub want: Out,
}

fn table_test<In, Out>(run: impl Fn(In) -> Out, tests: &[TableTest<In, Out>])
where
    In: core::fmt::Debug + Clone,
    Out: core::fmt::Debug + std::cmp::PartialEq,
{
    let mut fails = 0;
    for test in tests {
        let got = run(test.input.clone());
        if got != test.want {
            eprintln!("- test failure");
            eprintln!("    input: {:02x?}", test.input);
            eprintln!("    got:   {:02x?}", got);
            eprintln!("    want:  {:02x?}", test.want);
            fails += 1;
        }
    }
    if fails != 0 {
        panic!("{fails} tests failed");
    }
}
