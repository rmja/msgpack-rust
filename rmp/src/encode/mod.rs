//! Provides various functions and structs for MessagePack encoding.

mod bin;
mod dec;
mod ext;
mod map;
mod sint;
mod str;
mod uint;
mod vec;

pub use self::sint::{write_nfix, write_i8, write_i16, write_i32, write_i64, write_sint};
pub use self::uint::{write_pfix, write_u8, write_u16, write_u32, write_u64, write_uint};
pub use self::dec::{write_f32, write_f64};
pub use self::str::{write_str_len, write_str};
pub use self::bin::{write_bin_len, write_bin};

use crate::{Marker, adapters::{Write, WriteError}};
use core::fmt;

// An error returned from the `write_marker` and `write_fixval` functions.
struct MarkerWriteError<E: WriteError>(pub E);

impl<E: WriteError> From<E> for MarkerWriteError<E> {
    #[cold]
    fn from(err: E) -> MarkerWriteError<E> {
        MarkerWriteError(err)
    }
}

#[cfg(feature = "std")]
impl<E: WriteError> From<MarkerWriteError<E>> for std::io::Error {
    #[cold]
    fn from(err: MarkerWriteError<E>) -> std::io::Error {
        match err {
            MarkerWriteError(err) => err
        }
    }
}

/// Attempts to write the given marker into the writer.
fn write_marker<W: Write<E>, E: WriteError>(wr: &mut W, marker: Marker) -> Result<(), MarkerWriteError<E>> {
    wr.write(&[marker.to_u8()]).map_err(MarkerWriteError)
}

/// An error returned from primitive values write functions.
struct DataWriteError<E: WriteError>(E);

impl<E: WriteError> From<E> for DataWriteError<E> {
    #[cold]
    #[inline]
    fn from(err: E) -> DataWriteError<E> {
        DataWriteError(err)
    }
}

#[cfg(feature = "std")]
impl<E: WriteError> From<DataWriteError<E>> for std::io::Error {
    #[cold]
    #[inline]
    fn from(err: DataWriteError) -> std::io::Error {
        err.0
    }
}

/// Encodes and attempts to write a nil value into the given write.
///
/// According to the MessagePack specification, a nil value is represented as a single `0xc0` byte.
///
/// # Errors
///
/// This function will return `Error` on any I/O error occurred while writing the nil marker.
///
/// # Examples
///
/// ```
/// let mut buf = Vec::new();
///
/// rmp::encode::write_nil(&mut buf).unwrap();
///
/// assert_eq!(vec![0xc0], buf);
/// ```
#[inline]
pub fn write_nil<W: Write<E>, E: WriteError>(wr: &mut W) -> Result<(), E> {
    write_marker(wr, Marker::Null).map_err(|e| e.0)
}

/// Encodes and attempts to write a bool value into the given write.
///
/// According to the MessagePack specification, an encoded boolean value is represented as a single
/// byte.
///
/// # Errors
///
/// Each call to this function may generate an I/O error indicating that the operation could not be
/// completed.
#[inline]
pub fn write_bool<W: Write<E>, E: WriteError>(wr: &mut W, val: bool) -> Result<(), E> {
    let marker = if val {
        Marker::True
    } else {
        Marker::False
    };

    write_marker(wr, marker).map_err(|e| e.0)
}

#[inline]
fn write_data_u8<W: Write<E>, E: WriteError>(wr: &mut W, val: u8) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_u16<W: Write<E>, E: WriteError>(wr: &mut W, val: u16) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_u32<W: Write<E>, E: WriteError>(wr: &mut W, val: u32) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_u64<W: Write<E>, E: WriteError>(wr: &mut W, val: u64) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_i8<W: Write<E>, E: WriteError>(wr: &mut W, val: i8) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_i16<W: Write<E>, E: WriteError>(wr: &mut W, val: i16) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_i32<W: Write<E>, E: WriteError>(wr: &mut W, val: i32) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_i64<W: Write<E>, E: WriteError>(wr: &mut W, val: i64) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_f32<W: Write<E>, E: WriteError>(wr: &mut W, val: f32) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

#[inline]
fn write_data_f64<W: Write<E>, E: WriteError>(wr: &mut W, val: f64) -> Result<(), DataWriteError<E>> {
    wr.write(&val.to_be_bytes()).map_err(DataWriteError)
}

/// An error that can occur when attempting to write multi-byte MessagePack value.
#[derive(Debug)]
pub enum ValueWriteError<E: WriteError> {
    /// I/O error while writing marker.
    InvalidMarkerWrite(E),
    /// I/O error while writing data.
    InvalidDataWrite(E),
}

impl<E: WriteError> From<MarkerWriteError<E>> for ValueWriteError<E> {
    #[cold]
    fn from(err: MarkerWriteError<E>) -> ValueWriteError<E> {
        match err {
            MarkerWriteError(err) => ValueWriteError::InvalidMarkerWrite(err),
        }
    }
}

impl<E: WriteError> From<DataWriteError<E>> for ValueWriteError<E> {
    #[cold]
    fn from(err: DataWriteError<E>) -> ValueWriteError<E> {
        match err {
            DataWriteError(err) => ValueWriteError::InvalidDataWrite(err),
        }
    }
}

#[cfg(feature = "std")]
impl From<ValueWriteError<std::io::Error>> for std::io::Error {
    #[cold]
    fn from(err: ValueWriteError<std::io::Error>) -> std::io::Error {
        match err {
            ValueWriteError::InvalidMarkerWrite(err) |
            ValueWriteError::InvalidDataWrite(err) => err,
        }
    }
}

#[cfg(feature = "std")]
impl<E: WriteError + std::error::Error> std::error::Error for ValueWriteError<E> {
    #[cold]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            ValueWriteError::InvalidMarkerWrite(ref err) |
            ValueWriteError::InvalidDataWrite(ref err) => Some(err),
        }
    }
}

impl<E: WriteError> fmt::Display for ValueWriteError<E> {
    #[cold]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str("error while writing multi-byte MessagePack value")
    }
}

/// Encodes and attempts to write the most efficient array length implementation to the given write,
/// returning the marker used.
///
/// # Errors
///
/// This function will return `ValueWriteError` on any I/O error occurred while writing either the
/// marker or the data.
pub fn write_array_len<W: Write<E>, E: WriteError>(wr: &mut W, len: u32) -> Result<Marker, ValueWriteError<E>> {
    let marker = if len < 16 {
        write_marker(wr, Marker::FixArray(len as u8))?;
        Marker::FixArray(len as u8)
    } else if len < 65536 {
        write_marker(wr, Marker::Array16)?;
        write_data_u16(wr, len as u16)?;
        Marker::Array16
    } else {
        write_marker(wr, Marker::Array32)?;
        write_data_u32(wr, len)?;
        Marker::Array32
    };

    Ok(marker)
}

/// Encodes and attempts to write the most efficient map length implementation to the given write,
/// returning the marker used.
///
/// # Errors
///
/// This function will return `ValueWriteError` on any I/O error occurred while writing either the
/// marker or the data.
pub fn write_map_len<W: Write<E>, E: WriteError>(wr: &mut W, len: u32) -> Result<Marker, ValueWriteError<E>> {
    let marker = if len < 16 {
        write_marker(wr, Marker::FixMap(len as u8))?;
        Marker::FixMap(len as u8)
    } else if len < 65536 {
        write_marker(wr, Marker::Map16)?;
        write_data_u16(wr, len as u16)?;
        Marker::Map16
    } else {
        write_marker(wr, Marker::Map32)?;
        write_data_u32(wr, len)?;
        Marker::Map32
    };

    Ok(marker)
}

/// Encodes and attempts to write the most efficient ext metadata implementation to the given
/// write, returning the marker used.
///
/// # Errors
///
/// This function will return `ValueWriteError` on any I/O error occurred while writing either the
/// marker or the data.
///
/// # Panics
///
/// Panics if `ty` is negative, because it is reserved for future MessagePack extension including
/// 2-byte type information.
pub fn write_ext_meta<W: Write<E>, E: WriteError>(wr: &mut W, len: u32, ty: i8) -> Result<Marker, ValueWriteError<E>> {
    let marker = match len {
        1 => {
            write_marker(wr, Marker::FixExt1)?;
            Marker::FixExt1
        }
        2 => {
            write_marker(wr, Marker::FixExt2)?;
            Marker::FixExt2
        }
        4 => {
            write_marker(wr, Marker::FixExt4)?;
            Marker::FixExt4
        }
        8 => {
            write_marker(wr, Marker::FixExt8)?;
            Marker::FixExt8
        }
        16 => {
            write_marker(wr, Marker::FixExt16)?;
            Marker::FixExt16
        }
        len if len < 256 => {
            write_marker(wr, Marker::Ext8)?;
            write_data_u8(wr, len as u8)?;
            Marker::Ext8
        }
        len if len < 65536 => {
            write_marker(wr, Marker::Ext16)?;
            write_data_u16(wr, len as u16)?;
            Marker::Ext16
        }
        len => {
            write_marker(wr, Marker::Ext32)?;
            write_data_u32(wr, len)?;
            Marker::Ext32
        }
    };

    write_data_i8(wr, ty)?;

    Ok(marker)
}
