

pub struct MementoIterator {
    buffer: Vec<char>,
    index: usize
}

impl MementoIterator {
    pub fn memorize(&self) -> usize {
        self.index
    }

    pub fn reset_to(&mut self, index: usize) {
        self.index = index;
    }

    pub fn len(&self) -> usize {
        self.buffer.len()
    }
}

impl Iterator for MementoIterator {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.buffer.len() {
            None
        } else {
            let res = self.buffer[self.index];
            self.index += 1;
            Some(res)
        }
    }
}

impl From<Vec<char>> for MementoIterator {
    fn from(v: Vec<char>) -> Self {
        MementoIterator { buffer: v, index: 0 }
    }
}