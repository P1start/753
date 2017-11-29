#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct FileId(pub u32);

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Span {
    /// The start point of the `Span`.
    pub lo: u32,
    /// The end point of the `Span` (not included).
    pub hi: u32,

    pub file: FileId,
}

impl Span {
    pub fn new(lo: u32, hi: u32, file: FileId) -> Span {
        Span { lo, hi, file }
    }
}