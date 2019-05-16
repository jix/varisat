//! Variable length integer encoding.
//!
//! This uses a different encoding from the leb128 encoding used for binary DRAT and CLRAT. It uses
//! the same amount of bytes for each input, but is faster to encode and decode.
//!
//! Numbers are encoded like this:
//! ```text
//! 1xxxxxxx for up to 7 bits
//! 01xxxxxx xxxxxxxx for up to 14 bits
//! 001xxxxx xxxxxxxx xxxxxxxx for up to 21 bits
//! ...
//! ```
//!
//! The x-bits store the number from LSB to MSB. This scheme allows faster encoding and decoding, as
//! the bits are kept consecutive and the length can be determined from the first or first two
//! bytes.
//!
//! The current implementations are not optimal but fast enough to not be the bottleneck when
//! checking proofs.
use std::convert::{TryFrom, TryInto};
use std::io::{self, BufRead, Write};

/// Write an encoded 64 bit number.
pub fn write_u64(target: &mut impl Write, mut value: u64) -> Result<(), io::Error> {
    let bits = (64 - value.leading_zeros()) as u32;
    let blocks = (bits * (64 / 7)) / 64;
    if value < (1 << (8 * 7)) {
        value = ((value << 1) | 1) << blocks;
        let bytes = unsafe { std::mem::transmute::<u64, [u8; 8]>(value.to_le()) };
        target.write_all(&bytes[..(blocks + 1) as usize])
    } else {
        let lo_data = ((value << 1) | 1) << blocks;
        let lo_bytes = unsafe { std::mem::transmute::<u64, [u8; 8]>(lo_data.to_le()) };
        let hi_data = value >> (64 - (blocks + 1));
        let hi_bytes = unsafe { std::mem::transmute::<u64, [u8; 8]>(hi_data.to_le()) };

        target.write_all(&lo_bytes)?;
        target.write_all(&hi_bytes[..(blocks as usize) + 1 - 8])
    }
}

/// Read an encoded 64 bit number, if at least 16 bytes lookahead are available.
fn read_u64_fast(bytes: &[u8; 16]) -> (u64, usize) {
    let lo_data = u64::from_le(unsafe {
        std::mem::transmute::<[u8; 8], u64>(*<&[u8; 8]>::try_from(&bytes[..8]).unwrap())
    });

    let len = (lo_data | (1 << 9)).trailing_zeros() + 1;

    if len <= 8 {
        let result = lo_data & (!0u64 >> (64 - 8 * len));

        let result = result >> len;

        (result, len as usize)
    } else {
        let hi_data = u64::from_le(unsafe {
            std::mem::transmute::<[u8; 8], u64>(*<&[u8; 8]>::try_from(&bytes[8..]).unwrap())
        });

        let hi_data = hi_data & (!0u64 >> (64 - 8 * (len - 8)));

        let result = (lo_data >> len) | (hi_data << (64 - len));

        (result as u64, len as usize)
    }
}

/// Read an encoded 64 bit number from a buffered reader.
///
/// This uses [`read_u64_fast`] if the remaining buffer is larger than 16 bytes and falls back to a
/// slower implementation otherwise.
pub fn read_u64(source: &mut impl BufRead) -> Result<u64, io::Error> {
    let buf = source.fill_buf()?;
    if buf.len() >= 16 {
        let next_bytes: &[u8; 16] = (&buf[..16]).try_into().unwrap();
        let (value, advance) = read_u64_fast(next_bytes);
        source.consume(advance);
        Ok(value)
    } else {
        let mut scan = 1 << 9;
        let mut byte: [u8; 1] = [0];
        let mut begin = 1;
        source.read_exact(&mut byte[..])?;
        let mut result = byte[0] as u64;
        scan |= byte[0] as u64;
        if byte[0] == 0 {
            begin += 1;
            source.read_exact(&mut byte[..])?;
            result |= (byte[0] as u64) << 8;
            scan |= (byte[0] as u64) << 8;
        }
        let len = scan.trailing_zeros() + 1;

        result >>= len;

        for i in begin..len {
            source.read_exact(&mut byte[..])?;
            result |= (byte[0] as u64) << (8 * i - len);
        }

        Ok(result as u64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;

    proptest! {
        #[test]
        fn roundtrip (
            numbers in prop::collection::vec(prop::num::u64::ANY, 0..10_000)
        ) {
            let mut buf = vec![];

            for &num in numbers.iter() {
                write_u64(&mut buf, num)?;
            }

            let mut read = std::io::BufReader::with_capacity(128, &buf[..]);

            let mut out = vec![];

            while let Ok(num) = read_u64(&mut read) {
                out.push(num)
            }

            prop_assert_eq!(numbers, out);
        }
    }
}
