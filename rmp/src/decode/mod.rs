//! Provides various functions and structs for MessagePack decoding.

mod dec;
mod ext;
mod sint;
mod str;
mod uint;

pub use self::sint::{read_nfix, read_i8, read_i16, read_i32, read_i64};
pub use self::uint::{read_pfix, read_u8, read_u16, read_u32, read_u64};
pub use self::dec::{read_f32, read_f64};
pub use self::str::{read_str_len, read_str, read_str_from_slice, DecodeStringError};
pub use self::ext::{read_fixext1, read_fixext2, read_fixext4, read_fixext8, read_fixext16, read_ext_meta, ExtMeta};

use num_traits::cast::FromPrimitive;

use crate::{Marker, adapters::{Read, ReadError}};
use core::fmt;

/// An error that can occur when attempting to read a MessagePack marker from the reader.
#[derive(Debug)]
pub struct MarkerReadError<E: ReadError>(pub E);

/// An error which can occur when attempting to read a MessagePack value from the reader.
#[derive(Debug)]
pub enum ValueReadError<E: ReadError> {
    /// Failed to read the marker.
    InvalidMarkerRead(E),
    /// Failed to read the data.
    InvalidDataRead(E),
    /// The type decoded isn't match with the expected one.
    TypeMismatch(Marker),
}

#[cfg(feature = "std")]
impl<E: ReadError + std::error::Error> std::error::Error for ValueReadError<E> {
    #[cold]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            ValueReadError::InvalidMarkerRead(ref err) |
            ValueReadError::InvalidDataRead(ref err) => Some(err),
            ValueReadError::TypeMismatch(..) => None,
        }
    }
}

impl<E: ReadError> fmt::Display for ValueReadError<E> {
    #[cold]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match *self {
            ValueReadError::InvalidMarkerRead(..) => "failed to read MessagePack marker",
            ValueReadError::InvalidDataRead(..) => "failed to read MessagePack data",
            ValueReadError::TypeMismatch(..) => {
                "the type decoded isn't match with the expected one"
            }
        })
    }
}

impl<E: ReadError> From<MarkerReadError<E>> for ValueReadError<E> {
    #[cold]
    fn from(err: MarkerReadError<E>) -> ValueReadError<E> {
        match err {
            MarkerReadError(err) => ValueReadError::InvalidMarkerRead(err),
        }
    }
}

#[cfg(feature = "std")]
impl From<std::io::Error> for MarkerReadError<std::io::Error> {
    #[cold]
    fn from(err: std::io::Error) -> MarkerReadError<std::io::Error> {
        MarkerReadError(err)
    }
}

/// Attempts to read a single byte from the given reader and to decode it as a MessagePack marker.
#[inline]
pub fn read_marker<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<Marker, MarkerReadError<E>> {
    let mut buf = [0; 1];
    rd.read(&mut buf).map_err(MarkerReadError)?;
    Ok(Marker::from_u8(buf[0]))
}

/// Attempts to read a single byte from the given reader and to decode it as a nil value.
///
/// According to the MessagePack specification, a nil value is represented as a single `0xc0` byte.
///
/// # Errors
///
/// This function will return `ValueReadError` on any I/O error while reading the nil marker,
/// except the EINTR, which is handled internally.
///
/// It also returns `ValueReadError::TypeMismatch` if the actual type is not equal with the
/// expected one, indicating you with the actual type.
///
/// # Note
///
/// This function will silently retry on every EINTR received from the underlying `Read` until
/// successful read.
pub fn read_nil<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<(), ValueReadError<E>> {
    match read_marker(rd)? {
        Marker::Null => Ok(()),
        marker => Err(ValueReadError::TypeMismatch(marker)),
    }
}

/// Attempts to read a single byte from the given reader and to decode it as a boolean value.
///
/// According to the MessagePack specification, an encoded boolean value is represented as a single
/// byte.
///
/// # Errors
///
/// This function will return `ValueReadError` on any I/O error while reading the bool marker,
/// except the EINTR, which is handled internally.
///
/// It also returns `ValueReadError::TypeMismatch` if the actual type is not equal with the
/// expected one, indicating you with the actual type.
///
/// # Note
///
/// This function will silently retry on every EINTR received from the underlying `Read` until
/// successful read.
pub fn read_bool<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<bool, ValueReadError<E>> {
    match read_marker(rd)? {
        Marker::True => Ok(true),
        Marker::False => Ok(false),
        marker => Err(ValueReadError::TypeMismatch(marker)),
    }
}

/// An error which can occur when attempting to read a MessagePack numeric value from the reader.
#[derive(Debug)]
pub enum NumValueReadError<E: ReadError> {
    /// Failed to read the marker.
    InvalidMarkerRead(E),
    /// Failed to read the data.
    InvalidDataRead(E),
    /// The type decoded isn't match with the expected one.
    TypeMismatch(Marker),
    /// Out of range integral type conversion attempted.
    OutOfRange,
}

#[cfg(feature = "std")]
impl<E: ReadError + std::error::Error> std::error::Error for NumValueReadError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            NumValueReadError::InvalidMarkerRead(ref err) |
            NumValueReadError::InvalidDataRead(ref err) => Some(err),
            NumValueReadError::TypeMismatch(..) |
            NumValueReadError::OutOfRange => None,
        }
    }
}

impl<E: ReadError> fmt::Display for NumValueReadError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match *self {
            NumValueReadError::InvalidMarkerRead(..) => "failed to read MessagePack marker",
            NumValueReadError::InvalidDataRead(..) => "failed to read MessagePack data",
            NumValueReadError::TypeMismatch(..) => {
                "the type decoded isn't match with the expected one"
            }
            NumValueReadError::OutOfRange => "out of range integral type conversion attempted",
        })
    }
}

impl<E: ReadError> From<MarkerReadError<E>> for NumValueReadError<E> {
    #[cold]
    fn from(err: MarkerReadError<E>) -> NumValueReadError<E> {
        match err {
            MarkerReadError(err) => NumValueReadError::InvalidMarkerRead(err),
        }
    }
}

impl<E: ReadError> From<ValueReadError<E>> for NumValueReadError<E> {
    #[cold]
    fn from(err: ValueReadError<E>) -> NumValueReadError<E> {
        match err {
            ValueReadError::InvalidMarkerRead(err) => NumValueReadError::InvalidMarkerRead(err),
            ValueReadError::InvalidDataRead(err) => NumValueReadError::InvalidDataRead(err),
            ValueReadError::TypeMismatch(err) => NumValueReadError::TypeMismatch(err),
        }
    }
}

// Helper functions to map I/O error into the `InvalidDataRead` error.

#[doc(hidden)]
#[inline]
pub fn read_data_u8<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u8, ValueReadError<E>> {
    let mut buf = [0; 1];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(buf[0])
}

#[doc(hidden)]
#[inline]
pub fn read_data_u16<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u16, ValueReadError<E>> {
    let mut buf = [0; 2];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(u16::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_u32<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u32, ValueReadError<E>> {
    let mut buf = [0; 4];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(u32::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_u64<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u64, ValueReadError<E>> {
    let mut buf = [0; 8];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(u64::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_i8<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<i8, ValueReadError<E>> {
    let mut buf = [0; 1];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(i8::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_i16<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<i16, ValueReadError<E>> {
    let mut buf = [0; 2];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(i16::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_i32<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<i32, ValueReadError<E>> {
    let mut buf = [0; 4];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(i32::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_i64<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<i64, ValueReadError<E>> {
    let mut buf = [0; 8];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(i64::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_f32<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<f32, ValueReadError<E>> {
    let mut buf = [0; 4];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(f32::from_be_bytes(buf))
}

#[doc(hidden)]
#[inline]
pub fn read_data_f64<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<f64, ValueReadError<E>> {
    let mut buf = [0; 8];
    rd.read(&mut buf).map_err(ValueReadError::InvalidDataRead)?;
    Ok(f64::from_be_bytes(buf))
}

/// Attempts to read up to 9 bytes from the given reader and to decode them as integral `T` value.
///
/// This function will try to read up to 9 bytes from the reader (1 for marker and up to 8 for data)
/// and interpret them as a big-endian `T`.
///
/// Unlike `read_*`, this function weakens type restrictions, allowing you to safely decode packed
/// values even if you aren't sure about the actual integral type.
///
/// # Errors
///
/// This function will return `NumValueReadError` on any I/O error while reading either the marker
/// or the data.
///
/// It also returns `NumValueReadError::OutOfRange` if the actual type is not an integer or it does
/// not fit in the given numeric range.
///
/// # Examples
///
/// ```
/// let buf = [0xcd, 0x1, 0x2c];
///
/// assert_eq!(300u16, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300i16, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300u32, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300i32, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300u64, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300i64, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300usize, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// assert_eq!(300isize, rmp::decode::read_int(&mut &buf[..]).unwrap());
/// ```
pub fn read_int<T: FromPrimitive, R: Read<E>, E: ReadError>(rd: &mut R) -> Result<T, NumValueReadError<E>> {
    let val = match read_marker(rd)? {
        Marker::FixPos(val) => T::from_u8(val),
        Marker::FixNeg(val) => T::from_i8(val),
        Marker::U8 => T::from_u8(read_data_u8(rd)?),
        Marker::U16 => T::from_u16(read_data_u16(rd)?),
        Marker::U32 => T::from_u32(read_data_u32(rd)?),
        Marker::U64 => T::from_u64(read_data_u64(rd)?),
        Marker::I8 => T::from_i8(read_data_i8(rd)?),
        Marker::I16 => T::from_i16(read_data_i16(rd)?),
        Marker::I32 => T::from_i32(read_data_i32(rd)?),
        Marker::I64 => T::from_i64(read_data_i64(rd)?),
        marker => return Err(NumValueReadError::TypeMismatch(marker)),
    };

    val.ok_or(NumValueReadError::OutOfRange)
}

/// Attempts to read up to 5 bytes from the given reader and to decode them as a big-endian u32
/// array size.
///
/// Array format family stores a sequence of elements in 1, 3, or 5 bytes of extra bytes in addition
/// to the elements.
///
/// # Note
///
/// This function will silently retry on every EINTR received from the underlying `Read` until
/// successful read.
// TODO: Docs.
// NOTE: EINTR is managed internally.
pub fn read_array_len<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u32, ValueReadError<E>>
{
    match read_marker(rd)? {
        Marker::FixArray(size) => Ok(size as u32),
        Marker::Array16 => Ok(read_data_u16(rd)? as u32),
        Marker::Array32 => Ok(read_data_u32(rd)?),
        marker => Err(ValueReadError::TypeMismatch(marker)),
    }
}

/// Attempts to read up to 5 bytes from the given reader and to decode them as a big-endian u32
/// map size.
///
/// Map format family stores a sequence of elements in 1, 3, or 5 bytes of extra bytes in addition
/// to the elements.
///
/// # Note
///
/// This function will silently retry on every EINTR received from the underlying `Read` until
/// successful read.
// TODO: Docs.
pub fn read_map_len<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u32, ValueReadError<E>> {
    let marker = read_marker(rd)?;
    marker_to_len(rd, marker)
}

pub fn marker_to_len<R: Read<E>, E: ReadError>(rd: &mut R, marker: Marker) -> Result<u32, ValueReadError<E>> {
    match marker {
        Marker::FixMap(size) => Ok(size as u32),
        Marker::Map16 => Ok(read_data_u16(rd)? as u32),
        Marker::Map32 => Ok(read_data_u32(rd)?),
        marker => Err(ValueReadError::TypeMismatch(marker)),
    }
}

/// Attempts to read up to 5 bytes from the given reader and to decode them as Binary array length.
///
/// # Note
///
/// This function will silently retry on every EINTR received from the underlying `Read` until
/// successful read.
// TODO: Docs.
pub fn read_bin_len<R: Read<E>, E: ReadError>(rd: &mut R) -> Result<u32, ValueReadError<E>> {
    match read_marker(rd)? {
        Marker::Bin8 => Ok(read_data_u8(rd)? as u32),
        Marker::Bin16 => Ok(read_data_u16(rd)? as u32),
        Marker::Bin32 => Ok(read_data_u32(rd)?),
        marker => Err(ValueReadError::TypeMismatch(marker)),
    }
}
