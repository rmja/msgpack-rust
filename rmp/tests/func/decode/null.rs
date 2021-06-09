use std::io::Cursor;

use crate::msgpack::decode::*;

#[test]
fn pass() {
    let buf = [0xc0];
    let mut cur = Cursor::new(&buf[..]);

    assert_eq!((), read_nil(&mut cur).unwrap());
    assert_eq!(1, cur.position());
}

#[test]
fn fail_invalid_marker() {
    let buf = [0xc1];
    let mut cur = Cursor::new(&buf[..]);

    match read_nil(&mut cur) {
        Err(ValueReadError::TypeMismatch(..)) => (),
        other => panic!("unexpected result: {:?}", other)
    }
    assert_eq!(1, cur.position());
}

#[test]
fn fail_unexpected_eof() {
    let buf = [];
    let mut cur = Cursor::new(&buf[..]);

    read_nil(&mut cur).err().unwrap();
    assert_eq!(0, cur.position());
}