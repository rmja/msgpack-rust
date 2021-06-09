use alloc::vec::Vec;

pub trait Write<E: WriteError> {
    fn write(&mut self, buf: &[u8]) -> Result<(), E>;
}

pub trait WriteError : 'static + core::fmt::Debug {}

impl WriteError for () {
}

// https://static.rust-lang.org/doc/master/src/std/io/impls.rs.html#211-232
impl<'a> Write<()> for &'a mut [u8] {
    #[inline]
    fn write(&mut self, data: &[u8]) -> Result<(), ()> {
        if data.len() > self.len() {
            return Err(())
        }
        let amt = core::cmp::min(data.len(), self.len());
        let (a, b) = core::mem::replace(self, &mut []).split_at_mut(amt);
        a.copy_from_slice(&data[..amt]);
        *self = b;
        Ok(())
    }
}

// https://static.rust-lang.org/doc/master/src/std/io/impls.rs.html#237-252
impl Write<()> for Vec<u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<(), ()> {
        self.extend_from_slice(buf);
        Ok(())
    }
}

#[cfg(feature = "std")]
impl WriteError for std::io::Error {
}