/// A custom never type because ! is not stable
#[derive(Copy, Clone)]
pub enum Never {}
impl Default for Never {
    fn default() -> Self {
        panic!()
    }
}
