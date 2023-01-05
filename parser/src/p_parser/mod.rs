use std::{iter::{Peekable, Enumerate}, str::Chars, collections::HashMap};

mod codepoint_iterator;
mod parser_error;
mod optional_result;
mod memento_iterator;

use serde::{Serialize, Deserialize};

use self::{parser_error::{ParserError, CodePoint}, optional_result::OptionalResult, codepoint_iterator::CodePointIterator, memento_iterator::MementoIterator};

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
pub struct ReferenceName { v: String }
impl<T> From<T> for ReferenceName 
    where T: Into<String> {
        
    fn from(v: T) -> Self {
        ReferenceName { v: v.into() }
    }
}

impl ToString for ReferenceName {
    fn to_string(&self) -> String {
        self.v.to_owned()
    }
}

type CharStream<'a> = codepoint_iterator::CodePointIterator<Peekable<Enumerate<Chars<'a>>>>;
impl From<&mut CharStream<'_>> for ParserError {
    fn from(c: &mut CharStream<'_>) -> Self {
        ParserError::from_point(CodePoint::from(c.line(), c.column()), String::from(""))
    }
}
impl<'a> From<&'a str> for CharStream<'a> {
    fn from(s: &'a str) -> Self {
        CodePointIterator::new(s.chars().enumerate().peekable())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    Identifier(ReferenceName),
    Assignment,
    Reference(ReferenceName),
    InverseReference(ReferenceName),
    Or,
    Constant(String),
    Concat,
}

pub type Line = Vec<Token>;

#[derive(Clone, Debug, PartialEq)]
pub enum TreeNode {
    Reference(ReferenceName),
    InverseReference(ReferenceName),
    Or(Vec<TreeNode>),
    Concat(Vec<TreeNode>),
    Constant(String),
}

#[derive(Debug)]
struct SyntaxTree {
    references: HashMap<ReferenceName, TreeNode>
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ParsedContent {
    pub content: String,
    pub siblings: Vec<ParsedContent>,
    pub name: String,
    pub begin_index: usize,
    pub end_index: usize,
}

impl ParsedContent {
    pub fn new() -> Self {
        ParsedContent { content: "".into(), siblings: Vec::new(), name: "".into(), begin_index: 0, end_index: 0 }
    }
}

impl From<String> for ParsedContent {
    fn from(s: String) -> Self {
        ParsedContent { content: s, siblings: Vec::new(), name: "".into(), begin_index: 0, end_index: 0 }
    }
}

impl SyntaxTree {
    pub fn new() -> SyntaxTree {
        SyntaxTree { references: HashMap::new() }
    }

    pub fn get_reference(&self, name: &ReferenceName) -> Option<&TreeNode> {
        self.references.get(name)
    }

    pub fn insert(&mut self, ref_name: ReferenceName, node: TreeNode) -> Result<(), ParserError> {
        let name = ref_name.to_string();
        match self.references.insert(ref_name, node) {
            None => Ok(()),
            Some(_) => {
                Err(ParserError::from_message(format!("{} already defined", name)))
            }
        }
    }

    pub fn matches(&self, c: &mut MementoIterator, node: &TreeNode) -> Result<Option<ParsedContent>, ParserError> {
        match node {
            TreeNode::Reference(ref_name) => {
                if self.references.contains_key(ref_name) {
                    let backup = c.memorize();
                    if let Some(mut res) = self.matches(c, &self.references[ref_name])? {
                        res.name = ref_name.to_string();
                        res.begin_index = backup;
                        res.end_index = c.memorize();
                        Ok(Some(res))
                    } else {
                        c.reset_to(backup);
                        Ok(None)
                    }
                } else {
                    Err(ParserError::from_message(format!("unresolved reference {}", ref_name.to_string())))
                }
            },
            TreeNode::InverseReference(_) => {
                panic!("nooooo");
            },
            TreeNode::Or(nodes) => {
                let backup = c.memorize();
                for node in nodes {
                    if let Some(res) = self.matches(c, node)? {
                        return Ok(Some(res))
                    } else {
                        c.reset_to(backup);
                    }
                }

                Ok(None)
            },
            TreeNode::Concat(nodes) => {
                let mut result = ParsedContent::new();
                result.begin_index = c.memorize();
                for node in nodes {
                    let backup = c.memorize();
                    if let Some(res) = self.matches(c, node)? {
                        result.content.push_str(&res.content);
                        result.siblings.push(res);
                    } else {
                        c.reset_to(backup);
                        return Ok(None);
                    }
                }
                result.end_index = c.memorize();

                Ok(Some(result))
            },
            TreeNode::Constant(constant) => {
                if c.len() < constant.len() {
                    return Ok(None);
                }

                if constant.len() == 0 {
                    return Ok(None);
                }

                let constant_chars: Vec<char> = constant.chars().collect();
                let backup = c.memorize();
                for i in 0..constant.len() {
                    if let Some(read_char) = c.next() {
                        if read_char != constant_chars[i] {
                            c.reset_to(backup);
                            return Ok(None);
                        }
                    } else {
                        c.reset_to(backup);
                        return Ok(None);
                    }
                }

                let mut res = ParsedContent::from(constant.to_owned());
                res.begin_index = backup;
                res.end_index = c.memorize();
                Ok(Some(res))
            },
        }
    }
}

pub fn parse_code_file(content: String, definition: String, root: ReferenceName) -> Result<Option<ParsedContent>, ParserError> {
    let definition = parse_definition(definition)?;

    if definition.get_reference(&root) == None {
        return Err(ParserError::from_message(format!("reference {} not found", root.to_string())))
    }

    let mut char_stream = MementoIterator::from(content.chars().collect::<Vec<char>>());
    if let Some(mut res) = definition.matches(&mut char_stream, &definition.get_reference(&root).unwrap())? {
        res.name = root.to_string();
        Ok(Some(res))
    } else {
        Ok(None)
    }
}

fn parse_definition(content: String) -> Result<SyntaxTree, ParserError> {
    let lines = walk_file(&mut CodePointIterator::new(content.chars().enumerate().peekable()))?;
    create_syntax_tree(lines)
}

fn create_syntax_tree(lines: Vec<Line>) -> Result<SyntaxTree, ParserError> {
    let mut tree = SyntaxTree::new();
    

    for line in lines {
        if line.len() == 0 {
            continue;
        }

        let name = match line.first().expect("should not happen") {
            Token::Identifier(ident) => ident.clone(),
            _ => return Err(ParserError::from_message(String::from("expected left side assignment"))),
        };

        let mut token_stream = line.iter().peekable();

        loop { //
            match token_stream.next() {
                Some(Token::Assignment) => {
                    break;
                },
                None => return Err(ParserError::from_message(String::from("expected assignment, found none"))),
                _ => {},
            }
        }

        let grouped: Vec<Token> = token_stream
            .map(|v| v.clone())
            .collect();

        let token_to_tree_node = |token: &Token| match token {
            Token::Reference(ref_name) => TreeNode::Reference(ref_name.to_owned()),
            Token::InverseReference(ref_name) => TreeNode::InverseReference(ref_name.to_owned()),
            Token::Constant(constant) => TreeNode::Constant(constant.to_owned()),
            _ => panic!("ahhhhh!"),
        };

        let by_token = |by: Token| move |token: &Token| *token == by;

        // a b c | d e
        // [a b c, d e]
        // [[a,b,c], [d,e]]
        
        let grouped = grouped
            .split(by_token(Token::Or))
            .map(|g| g.split(by_token(Token::Concat)));
        
        let node = TreeNode::Or(grouped.map(|or_operands| {
            TreeNode::Concat(or_operands.map(|concat_operands| {
                token_to_tree_node(concat_operands.first().unwrap())
            }).collect())
        }).collect());

        tree.insert(name, node)?;
    }

    Ok(tree)
}


fn walk_file(c: &mut CharStream) -> Result<Vec<Line>, ParserError> {
    let mut lines = vec![];

    loop {
        if c.peek() == None {
            break;
        }

        match walk_line(c) {
            Ok(tokens) => lines.push(tokens),
            Err(e) => return Err(e),
        }
    }

    return Ok(lines);
}

fn walk_line(c: &mut CharStream) -> Result<Vec<Token>, ParserError> {
    let mut tokens = vec![];
    let mut prev_token;

    loop {
        prev_token = tokens.last();
        walk_whitespace(c);

        if let Some((_, char)) = c.peek() {
            match char {
                '\n' => {
                    c.next();
                    break;
                },
                _ => {}
            }
        } else {
            break
        }

        if let Some(ident) = walk_identifier(c) {
            tokens.push(Token::Identifier(ident));
            continue;
        }

        if walk_single(c, '=') != None {
            tokens.push(Token::Assignment);
            continue;
        }

        if walk_single(c, '|') != None {
            tokens.push(Token::Or);
            continue;
        }

        if let Some(ident) = walk_reference(c) {
            match prev_token {
                Some(Token::Reference(_)) | 
                Some(Token::InverseReference(_)) | 
                Some(Token::Constant(_)) => {
                    tokens.push(Token::Concat);
                },
                _ => {}
            }

            tokens.push(ident);
            continue;
        }

        if let OptionalResult::Ok(constant) = walk_constant(c) {
            match prev_token {
                Some(Token::Reference(_)) | 
                Some(Token::InverseReference(_)) | 
                Some(Token::Constant(_)) => {
                    tokens.push(Token::Concat);
                },
                _ => {}
            }

            tokens.push(Token::Constant(constant));
            continue;
        }

        if let Some(_) = walk_comment(c) {
            break;
        }

        return Err(ParserError::from_point(CodePoint::from(c.line(), c.column()), "unknown expression found".into()))

    }

    return Ok(tokens);
}

fn walk_comment(c: &mut CharStream) -> Option<()> {
    if let Some((_, char)) =  c.peek() {
        match char {
            '#' => {},
            _ => return None
        }
    }

    loop {
        if let Some((_, char)) = c.peek() {
            match char {
                '\n' => return Some(()),
                _ => c.next()
            };
        } else {
            return Some(())
        }
    }
}

fn walk_reference(c: &mut CharStream) -> Option<Token> {
    if let Some((_, open_bracket)) = c.peek() {
        match open_bracket {
            '<' => {
                c.next();
                let mut is_inverse = false;
                if let Some((_, inverse)) = c.peek() {
                    match inverse {
                        '!' => {
                            is_inverse = true;
                            c.next();
                        },
                        _ => {}
                    };
                }


                if let Some(ref_name) = walk_identifier(c) {
                    if let Some((_, close_bracket)) = c.peek() {
                        match close_bracket {
                            '>' => {
                                c.next();
                                if is_inverse {
                                    return Some(Token::InverseReference(ref_name))
                                } else {
                                    return Some(Token::Reference(ref_name))
                                }
                            },
                            _ => panic!("expected >")
                        }
                    } else {
                        panic!("expected >, got EOF")
                    }
                } else {
                    panic!("ref_name is invalid");
                }
            },
            _ => return None
        }
    } else {
        None
    }
}

fn walk_constant(c: &mut CharStream) -> OptionalResult<String, ParserError> {
    let begin = CodePoint::from(c.line(), c.column());
    if let Some((_, next)) = c.peek() {
        if *next == '"' {
            c.next();
        } else {
            return OptionalResult::None;
        }
    } else {
        return OptionalResult::None;
    }
    let mut buffer = String::from("");
    
    loop {
        if let Some((_, next)) = c.next() {
            match next {
                '"' => {
                    return OptionalResult::Ok(buffer)
                },
                '\\' => match c.next() {
                    None => {
                        return OptionalResult::Err(ParserError::from_range(
                            begin,
                            CodePoint::from(c.line(), c.column()),
                            String::from("unexpected end of file"),
                        ))
                    }
                    Some((_, escaping)) => {
                        if let Some(escaped) = escapeable(&escaping) {
                            buffer.push(escaped);
                        } else if escaping == 'u' {
                            if let Some(utf_codepoint) = unicode_char_from_hex(c) {
                                buffer.push(utf_codepoint);
                            }
                        } else {
                            return OptionalResult::Err(ParserError::from_point(
                                CodePoint::from(c.line(), c.column()),
                                format!("unknown escaped character {}", escaping),
                            ));
                        }
                    }
                },
                other => buffer.push(other),
            }
        } else {
            return OptionalResult::Err(ParserError::from_range(
                begin,
                CodePoint::from(c.line(), c.column()),
                String::from("not closed string"),
            ));
        }
    }
}

fn escapeable(c: &char) -> Option<char> {
    match c {
        '"' => Some('"'),
        '\\' => Some('\\'),
        'b' => Some(8u8 as char),
        'f' => Some(12u8 as char),
        'n' => Some('\n'),
        'r' => Some('\r'),
        't' => Some('\t'),
        _ => None,
    }
}

fn unicode_char_from_hex(c: &mut CharStream) -> Option<char> {
    let mut codepoints = ['0', '0', '0', '0'];
    let mut taken = 0;
    for (_, digit) in c.take(4) {
        codepoints[taken] = digit;

        taken += 1
    }

    if taken != 4 {
        None
    } else {
        let digits_string = String::from_iter(codepoints);
        let unicode_codepoint =
            u16::from_str_radix(&digits_string, 16).expect("wrong utf8-codepoint");
        char::from_u32(unicode_codepoint as u32)
    }
}

fn walk_single(c: &mut CharStream, matching: char) -> Option<()> {
    if let Some((_, char)) = c.peek() {
        if *char == matching {
            c.next();
            return Some(())
        }
    }

    return None
}

fn walk_whitespace(c: &mut CharStream) {
    loop {
        match c.peek() {
            Some((_, ' ')) |Some((_, '\r')) |Some((_, '\t')) => c.next(),
            _ => return 
        };
    }
}

fn walk_identifier(c: &mut CharStream) -> Option<ReferenceName> {
    let mut ident = String::from("");
    loop {
        if let Some((_, character)) = c.peek() {
            match character {
                '0'..='9' => ident.push(*character),
                'a'..='z' => ident.push(*character),
                'A'..='Z' => ident.push(*character),
                '_' => ident.push(*character),
                _ => break
            }
            c.next();
        } else {
            break
        }
    }

    if ident.len() == 0 {
        None
    } else {
        Some(ident.into())
    }
}


#[cfg(test)]
mod tests {
    use super::{*, parse_definition};

    #[test]
    fn identifier() {
        let result = walk_identifier(&mut CharStream::from("abc"));
        match result {
            None => panic!("expected identifier, got None"),
            Some(r) => assert_eq!(r,  "abc".into())

        }
    }

    #[test]
    fn constant() {
        let result = walk_constant(&mut CharStream::from("\"Hello\n\\\" World!\""));
        match result {
            OptionalResult::None => panic!("expected constant, got None"),
            OptionalResult::Ok(r) => assert_eq!(r,  "Hello\n\" World!"),
            OptionalResult::Err(e) => panic!("{}", e.to_string()),
        }
    }

    #[test]
    fn reference() {
        let result = walk_reference(&mut CharStream::from("<test>"));
        match result {
            None => panic!("expected referemce, got None"),
            Some(r) => assert_eq!(r, Token::Reference("test".into()))
        }
    }

    #[test]
    fn inverse_reference() {
        let result = walk_reference(&mut CharStream::from("<!test>"));
        match result {
            None => panic!("expected referemce, got None"),
            Some(r) => assert_eq!(r, Token::InverseReference("test".into()))
        }
    }

    #[test]
    fn line() {
        let result = walk_line(&mut CharStream::from("left  =<ref1> \"-\" <!ref2> | \"+\""));
        match result {
            Err(e) => panic!("{}", e.to_string()),
            Ok(vec) => {
                assert_eq!(vec, vec![
                    Token::Identifier("left".into()),
                    Token::Assignment,
                    Token::Reference("ref1".into()),
                    Token::Concat,
                    Token::Constant("-".into()),
                    Token::Concat,
                    Token::InverseReference("ref2".into()),
                    Token::Or,
                    Token::Constant("+".into())
                ]);
            }
        };
    }

    #[test]
    fn parse_definition_hello_word() {
        let definition = String::from("helloWorld = \"Hello World!\"");
        let res = parse_definition(definition);
        match res {
            Err(e) => panic!("{}", e.to_string()),
            Ok(tree) => {
                assert_eq!(tree.references.len(), 1);
                assert_eq!(tree.get_reference(&"helloWorld".into()), Some(&TreeNode::Or(vec![TreeNode::Concat(vec![TreeNode::Constant("Hello World!".into())])])));
            }
        }
    }

    #[test]
    fn simple_key() {
        let content = String::from("Hello World!");
        let definition = String::from("helloWorld = \"Hello World!\"");
        let root = "helloWorld".into();

        let parsed_result = parse_code_file(content, definition, root);
        match parsed_result {
            Err(e) => panic!("{}", e.to_string()),
            Ok(None) => panic!("expected Some result. got None"),
            Ok(Some(res)) => {
                assert_eq!(res.name.to_string(), "helloWorld");
                assert_eq!(res.content, "Hello World!");
                assert_eq!(res.siblings.len(), 1);
            }
        }
    }

    #[test]
    fn parse_reference() {
        let content = String::from("Hello World!");
        let definition = String::from("hello = \"Hello\"\nworld = \"World!\"\nhelloWorld = <hello> \" \" <world>");
        let root = "helloWorld".into();

        let parsed_result = parse_code_file(content, definition, root);
        match parsed_result {
            Err(e) => panic!("{}", e.to_string()),
            Ok(None) => panic!("expected Some result. got None"),
            Ok(Some(res)) => {
                assert_eq!(res.name.to_string(), "helloWorld");
                assert_eq!(res.content, "Hello World!");
                assert_eq!(res.siblings.len(), 3);
                assert_eq!(res.siblings[0].name, "hello");
                assert_eq!(res.siblings[0].content, "Hello");
                assert_eq!(res.siblings[1].name, "");
                assert_eq!(res.siblings[1].content, " ");
                assert_eq!(res.siblings[2].name, "world");
                assert_eq!(res.siblings[2].content, "World!");
            }
        }
    }
}

