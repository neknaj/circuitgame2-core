use circuitgame2_core::project::{
    BitSelectionError, CircuitLiteralWidthError, ConcatWidthError, check_bit_selection,
    check_circuit_literal_width, check_concat_width,
};
use circuitgame2_core::syntax::{BitLiteralSize, bit_literal_size};

#[test]
fn distinguishes_written_width_from_the_bits_required_by_the_value() {
    for (word, written_bits, required_bits) in [
        ("#b0000", 4, 0),
        ("#b00101", 5, 3),
        ("#x01", 8, 1),
        ("#x03", 8, 2),
        ("#x07", 8, 3),
        ("#x0a", 8, 4),
        ("#x0F", 8, 4),
        ("#x10", 8, 5),
    ] {
        assert_eq!(
            bit_literal_size(word),
            Some(BitLiteralSize { written_bits, required_bits })
        );
    }
    for word in ["#b", "#b2", "#x", "#xG", "#B0", "1", "#xF ; comment"] {
        assert_eq!(bit_literal_size(word), None);
    }
}

#[test]
fn sizes_literals_using_expected_width_without_implicitly_widening_fixed_bits() {
    assert_eq!(check_circuit_literal_width("#x01", Some(1), 128), Ok(1));
    assert_eq!(check_circuit_literal_width("#x01", None, 128), Ok(8));
    assert_eq!(check_circuit_literal_width("#x00", Some(1), 1), Ok(1));
    assert_eq!(check_circuit_literal_width("#b1", Some(16), 16), Ok(16));
    assert_eq!(
        check_circuit_literal_width("#x02", Some(1), 128),
        Err(CircuitLiteralWidthError::DoesNotFit { expected: 1, required: 2 })
    );
    for word in ["0", "1"] {
        assert_eq!(check_circuit_literal_width(word, None, 128), Ok(1));
        assert_eq!(
            check_circuit_literal_width(word, Some(8), 128),
            Err(CircuitLiteralWidthError::FixedBitWidth { expected: 8 })
        );
    }
    assert_eq!(
        check_circuit_literal_width("#x00", Some(0), 128),
        Err(CircuitLiteralWidthError::ZeroWidth)
    );
    assert_eq!(
        check_circuit_literal_width("#xzz", Some(0), 128),
        Err(CircuitLiteralWidthError::InvalidLiteral)
    );
    assert_eq!(
        check_circuit_literal_width("#x01", None, 7),
        Err(CircuitLiteralWidthError::LimitExceeded { width: 8, limit: 7 })
    );
}

#[test]
fn accepts_literals_beyond_the_range_of_machine_values() {
    let wide = format!("#x8{}", "0".repeat(63));
    assert_eq!(
        bit_literal_size(&wide),
        Some(BitLiteralSize { written_bits: 256, required_bits: 256 })
    );
    assert_eq!(check_circuit_literal_width(&wide, Some(256), 256), Ok(256));
    assert_eq!(
        check_circuit_literal_width(&wide, Some(255), 256),
        Err(CircuitLiteralWidthError::DoesNotFit { expected: 255, required: 256 })
    );
    let padded = format!("#x{}1", "0".repeat(63));
    assert_eq!(check_circuit_literal_width(&padded, Some(1), 1), Ok(1));
    assert_eq!(check_circuit_literal_width("#x0", Some(u64::MAX), u64::MAX), Ok(u64::MAX));
}

#[test]
fn checks_the_last_selected_bit_without_wrapping() {
    assert_eq!(check_bit_selection(32, 0, 16, 2), Ok(30));
    assert_eq!(check_bit_selection(32, 1, 16, 2), Ok(31));
    assert_eq!(check_bit_selection(32, 31, 1, u64::MAX), Ok(31));
    assert_eq!(
        check_bit_selection(32, 2, 16, 2),
        Err(BitSelectionError::Outside { start: 2, last: 32, input_width: 32 })
    );
    assert_eq!(check_bit_selection(0, 0, 0, 0), Err(BitSelectionError::ZeroCount));
    assert_eq!(check_bit_selection(32, 0, 1, 0), Err(BitSelectionError::ZeroStride));
    assert_eq!(
        check_bit_selection(u64::MAX, u64::MAX - 1, 1, 1),
        Ok(u64::MAX - 1)
    );
    let max = u64::MAX;
    assert_eq!(
        check_bit_selection(max, max, max, max),
        Err(BitSelectionError::Outside {
            start: max,
            last: u128::from(max) * u128::from(max),
            input_width: max,
        })
    );
}

#[test]
fn sums_concat_widths_until_the_first_invalid_argument() {
    assert_eq!(check_concat_width(&[2, 3, 4], 9), Ok(9));
    assert_eq!(check_concat_width(&[], 8), Err(ConcatWidthError::Empty));
    assert_eq!(
        check_concat_width(&[3, 0, 9], 8),
        Err(ConcatWidthError::ZeroWidth { argument: 1 })
    );
    assert_eq!(
        check_concat_width(&[3, 6, 0], 8),
        Err(ConcatWidthError::LimitExceeded { argument: 1, width: 9, limit: 8 })
    );
    assert_eq!(
        check_concat_width(&[u64::MAX, 1], u64::MAX),
        Err(ConcatWidthError::LimitExceeded {
            argument: 1,
            width: u128::from(u64::MAX) + 1,
            limit: u64::MAX,
        })
    );
}
