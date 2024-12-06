use std::io;
use std::io::Read;

use aber::lex::WithPosition;

fn main() {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .expect("failed to read from stdin");

    let res = aber::lex::Lex::new(&input);
    let res: Vec<_> = res.collect();

    println!("{res:#?}");

    if let Some(WithPosition {
        start,
        end,
        value: Err(e),
    }) = res.iter().find(|v| v.value.is_err())
    {
        let line = input
            .lines()
            .nth(start.line as usize - 1_usize)
            .expect("line");
        println!("{line}");
        print!("{}^", " ".repeat(start.char as usize));
        if let Some(end) = end {
            let c_end = if start.line == end.line {
                end.char as usize
            } else {
                line.len()
            };
            print!("{}", "~".repeat(c_end));
        }
        println!(" {e}");
    }
}
