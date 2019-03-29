use std::cell::RefCell;
/// Testing helpers for in memory IO.
use std::io;
use std::mem::replace;
use std::rc::Rc;

/// Can be passed as `Write + 'static` while allowing retrieval of the written data.
#[derive(Clone, Default)]
pub struct RcWriteBuffer {
    buffer: Rc<RefCell<Vec<u8>>>,
}

impl io::Write for RcWriteBuffer {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        self.buffer.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        Ok(())
    }
}

impl RcWriteBuffer {
    /// Return data written since the last call.
    pub fn take(&self) -> Vec<u8> {
        replace(&mut *self.buffer.borrow_mut(), vec![])
    }
}
