pub struct ParserError {
    location: ErrorLocation,
    error: String,
}

impl ParserError {
    pub fn location(&self) -> ErrorLocation {
        self.location
    }

    pub fn from_message(error: String) -> ParserError {
        return ParserError {
            location: ErrorLocation::None,
            error,
        };
    }

    pub fn from_point(code_point: CodePoint, error: String) -> ParserError {
        return ParserError {
            location: ErrorLocation::Point(code_point),
            error,
        };
    }

    pub fn from_range(from: CodePoint, to: CodePoint, error: String) -> ParserError {
        return ParserError {
            location: ErrorLocation::Range(from, to),
            error,
        }; 
    }

    pub fn error(self, message: &str) -> Self {
        ParserError { location: self.location, error: message.to_owned() }
    }
}

impl ToString for ParserError {
    fn to_string(&self) -> String {
        match self.location {
            ErrorLocation::Point(point) => format!(
                "{} on line {} column {}",
                self.error, point.line, point.column
            ),
            ErrorLocation::Range(begin, end) => format!(
                "{} from line {} column {} to line {} column {}",
                self.error, begin.line, begin.column, end.line, end.column
            ),
            ErrorLocation::None => self.error.to_owned()
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct CodePoint {
    line: u32,
    column: u32,
}

impl CodePoint {
    pub fn line(&self) -> u32 {
        self.line
    }

    pub fn column(&self) -> u32 {
        self.column
    }

    pub fn from(line: u32, column: u32) -> CodePoint {
        return CodePoint { line, column };
    }
}

#[derive(Clone, Copy)]
pub enum ErrorLocation {
    None,
    Point(CodePoint),
    Range(CodePoint, CodePoint),
}