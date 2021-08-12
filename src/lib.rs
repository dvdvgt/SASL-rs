use std::{
    env, fs,
    io::{self, Read},
    path::Path,
};

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

/// Helper function for getting the content of a file.
pub fn load_source_file(path: &Path) -> Result<String, io::Error> {
    let mut absolute_path = env::current_dir()?.join(path);
    absolute_path.set_extension("sasl");
    let mut file = fs::File::open(absolute_path)?;
    let mut src = String::new();
    file.read_to_string(&mut src)?;
    Ok(src)
}
