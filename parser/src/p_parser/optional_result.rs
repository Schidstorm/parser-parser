

#[derive(PartialEq)]
pub enum OptionalResult<T, E> {
    None,
    Ok(T),
    Err(E),
}

impl<T, E> OptionalResult<T, E> {
    pub fn is_none(&self) -> bool {
        match self {
            OptionalResult::None => true,
            _ => false
        }
    }

    pub fn is_ok(&self) -> bool {
        match self {
            OptionalResult::Ok(_) => true,
            _ => false
        }
    }

    pub fn is_err(&self) -> bool {
        match self {
            OptionalResult::Err(_) => true,
            _ => false
        }
    }
}