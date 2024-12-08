use std::io;
use std::io::Read;

use aber::lex::{WithLinearPosition, WithPosition};

fn main() {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .expect("failed to read from stdin");

    let res = aber::lex::Lex::new(&input);
    let res: Vec<_> = res.collect();

    if let Some(WithLinearPosition {
        offset_start,
        offset_end: _,
        value:
            WithPosition {
                start,
                end,
                value: Err(e),
            },
    }) = res.iter().find(|v| v.value.value.is_err())
    {
        let line = &input[*offset_start..];
        println!("{:3} | {line}", start.line);
        print!("    | {}^", " ".repeat(start.char as usize));
        if let Some(end) = end {
            let c_end = if start.line == end.line {
                end.char as usize
            } else {
                line.len()
            };
            print!("{}", "~".repeat(c_end));
        }
        println!(" {e}");

        std::process::exit(1);
    }

    let res = res.into_iter().map(|v| v.map(Result::unwrap));

    let res = aber::ast::parse(&input, res);
    println!("{res:#?}");

    if let Err(WithLinearPosition {
        offset_start,
        offset_end: _,
        value: WithPosition {
            start,
            end,
            value: e,
        },
    }) = &res
    {
        let line = input[*offset_start..].split('\n').next().unwrap();
        println!("    |");
        println!("{:3} | {line}", start.line);
        print!("    | {}^", " ".repeat(start.char as usize));
        if let Some(end) = end {
            let c_end = if start.line == end.line {
                end.char as usize
            } else {
                line.len()
            };
            print!("{}", "~".repeat(c_end));
        }
        println!(" {e:?}");

        std::process::exit(1);
    }
}
