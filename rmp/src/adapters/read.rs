pub trait Read<E: ReadError> {
    fn read(&mut self, buf: &mut [u8]) -> Result<(), E>;
}

pub trait ReadError : 'static + core::fmt::Debug {}

impl ReadError for () {
}

// https://static.rust-lang.org/doc/master/src/std/io/impls.rs.html#155-194
impl<'a> Read<()> for &'a [u8] {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<(), ()> {
        if buf.len() > self.len() {
            return Err(());
        }
        let (a, b) = self.split_at(buf.len());

        // First check if the amount of bytes we want to read is small:
        // `copy_from_slice` will generally expand to a call to `memcpy`, and
        // for a single byte the overhead is significant.
        if buf.len() == 1 {
            buf[0] = a[0];
        } else {
            buf.copy_from_slice(a);
        }

        *self = b;
        Ok(())
    }
}

// https://static.rust-lang.org/doc/master/src/std/io/cursor.rs.html#220-226
#[cfg(feature = "std")]
impl<T> Read<std::io::Error> for std::io::Cursor<T> where T: AsRef<[u8]> {
    fn read(&mut self, buf: &mut [u8]) -> Result<(), std::io::Error> {
        use std::io::BufRead;
        std::io::Read::read_exact(&mut self.fill_buf()?, buf)?;
        self.set_position(self.position() + buf.len() as u64);
        Ok(())
    }
}

#[cfg(feature = "std")]
impl ReadError for std::io::Error {
}