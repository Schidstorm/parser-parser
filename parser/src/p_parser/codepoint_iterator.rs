use std::iter::Peekable;


#[derive(Clone)]
pub struct CodePointIterator<I: Iterator> {
    iter: I,
    column: u32,
    line: u32,
}

impl<I: Iterator> CodePointIterator<I> {
    pub fn new(iter: I) -> CodePointIterator<I> {
        CodePointIterator {
            iter,
            line: 0,
            column: 0,
        }
    }

    pub fn line(&self) -> u32 {
        self.line
    }

    pub fn column(&self) -> u32 {
        self.column
    }
}

impl<I: Iterator> CodePointIterator<Peekable<I>> {
    #[inline]
    pub fn peek(&mut self) -> Option<&I::Item> {    
        self.iter.peek() 
    }
}

impl<I: Iterator<Item = (usize, char)>> Iterator for CodePointIterator<I> {
    type Item = (usize, char);

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(item) => {
                match item.1 {
                    '\n' => {
                        self.column = 0;
                        self.line += 1;
                    }
                    _ => self.column += 1,
                }
                Some(item)
            }
            None => None,
        }
    }
}