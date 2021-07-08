pub mod backend;
pub(crate) mod error;
pub mod frontend;

#[macro_export]
macro_rules! hashmap {
    ( $( $key: expr => $value: expr ),+ ) => {
      {
          let mut map = std::collections::HashMap::new();
          $(
              map.insert($key, $value);
          )+
          map
      }
    };
}

#[macro_export]
macro_rules! ptr {
    ( $val: expr ) => {
        Rc::new(RefCell::new($val))
    };
}
