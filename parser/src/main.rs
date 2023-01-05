use std::{env, fs};




mod p_parser;


fn main() {
    let mut a = env::args();
    a.next();
    let definition_content = if let Some(file_path) = a.next() {
        match fs::read_to_string(file_path) {
            Err(e) => panic!("{}", e),
            Ok(c) => c,
        }
    } else {
        panic!("missing definition file path as first argument.");
    };

    let code_content = if let Some(file_path) = a.next() {
        match fs::read_to_string(file_path) {
            Err(e) => panic!("{}", e),
            Ok(c) => c,
        }
    } else {
        panic!("missing definition file path as second argument.");
    };

    let root = if let Some(root) = a.next() {
        root
    } else {
        panic!("missing root reference as third argument.");
    };

    let res = match p_parser::parse_code_file(code_content, definition_content, root.into()) {
        Err(e) => panic!("{}", e.to_string()),
        Ok(None) => panic!("code doesn't match definition"),
        Ok(Some(r)) => r,
    };

    let json_content = match serde_json::to_string(&res) {
        Err(e) => panic!("{}", e),
        Ok(r) => r,
    };

    print!("{}", json_content);
    

    
}