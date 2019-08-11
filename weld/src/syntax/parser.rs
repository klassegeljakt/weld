//! Top-down recursive descent parser for Weld.
//!
//! Weld is designed to be parseable in one left-to-right pass through the input, without
//! backtracking, so we simply track a position as we go and keep incrementing it.

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar);

use crate::ast::*;
use crate::error::*;

use super::program::*;

#[cfg(test)]
use crate::tests::{print_expr_without_indent, print_typed_expr_without_indent};

// TODO: Write custom tokenizer
fn strip_comments(input: &str) -> String {
    let mut new = String::with_capacity(input.len());
    for line in input.lines() {
        new += line.split("#").next().unwrap();
        new += "\n";
    }
    new
}

/// Parse the complete input string as a Weld program (optional macros plus one expression).
pub fn parse_program(input: &str) -> WeldResult<Program> {
    let input = strip_comments(input);
    grammar::ProgramParser::new().parse(&input).map_err(|e| WeldCompileError::new(e.to_string()))
}

/// Parse the complete input string as a list of macros.
pub fn parse_macros(input: &str) -> WeldResult<Vec<Macro>> {
    let input = strip_comments(input);
    grammar::MacrosParser::new().parse(&input).map_err(|e| WeldCompileError::new(e.to_string()))
}

/// Parse the complete input string as a list of type aliases.
pub fn parse_type_aliases(input: &str) -> WeldResult<Vec<TypeAlias>> {
    let input = strip_comments(input);
    grammar::TypeAliasesParser::new().parse(&input).map_err(|e| WeldCompileError::new(e.to_string()))
}

/// Parse the complete input string as an expression.
pub fn parse_expr(input: &str) -> WeldResult<Expr> {
    let input = strip_comments(input);
    grammar::ExprParser::new().parse(&input).map_err(|e| WeldCompileError::new(e.to_string()))
}

/// Parse the complete input string as a Type.
pub fn parse_type(input: &str) -> WeldResult<Type> {
    let input = strip_comments(input);
    grammar::TypeParser::new().parse(&input).map_err(|e| WeldCompileError::new(e.to_string()))
}

#[test]
fn basic_parsing() {
    let e = parse_expr("10 - 2 - 3 + 1").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(((10-2)-3)+1)");

    let e = parse_expr("10 * 2 - 4 - 3 / 1").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(((10*2)-4)-(3/1))");

    let e = parse_expr("i32(10 + 3 + 2)").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(i32(((10+3)+2)))");

    let e = parse_expr("10 + 64 + i32(10.0)").unwrap();
    assert_eq!(print_expr_without_indent(&e), "((10+64)+(i32(10.0)))");

    let e = parse_expr("10 + 64 + f32(bool(19))").unwrap();
    assert_eq!(print_expr_without_indent(&e), "((10+64)+(f32((bool(19)))))");

    let e = parse_expr("1L:i64 + i64(1)").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(1L+(i64(1)))");

    let e = parse_expr("i64(1L:i64)").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(i64(1L))");

    let e = parse_expr("[1, 2+3, 2]").unwrap();
    assert_eq!(print_expr_without_indent(&e), "[1,(2+3),2]");

    let e = parse_expr("let a = 3+2; let b = (let c=a; c); b").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "(let a=((3+2));(let b=((let c=(a);c));b))"
    );

    let e = parse_expr("let a: vec[i32] = [2, 3]; a").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(let a=([2,3]);a)");

    let e = parse_expr("|a, b:i32| a+b").unwrap();
    assert_eq!(print_typed_expr_without_indent(&e), "|a:?,b:i32|(a:?+b:?)");

    let e = parse_expr("|| a||b").unwrap();
    assert_eq!(print_expr_without_indent(&e), "||(a||b)");

    let e = parse_expr("a.$0.$1").unwrap();
    assert_eq!(print_expr_without_indent(&e), "a.$0.$1");

    let e = parse_expr("a(0,1).$0").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(a)(0,1).$0");

    let e = parse_expr("a.$0(0,1).$1()").unwrap();
    assert_eq!(print_expr_without_indent(&e), "((a.$0)(0,1).$1)()");

    let e = parse_expr("a>b==c").unwrap();
    assert_eq!(print_expr_without_indent(&e), "((a>b)==c)");

    assert!(parse_expr("a>b>c").is_err());
    assert!(parse_expr("a==b==c").is_err());

    let e = parse_expr("appender[?]").unwrap();
    assert_eq!(print_expr_without_indent(&e), "appender[?]");

    let e = parse_expr("appender[i32]").unwrap();
    assert_eq!(print_expr_without_indent(&e), "appender[i32]");

    let e = parse_expr("appender[i32](1000L)").unwrap();
    assert_eq!(print_expr_without_indent(&e), "appender[i32](1000L)");

    let e = parse_expr("@(impl:local) dictmerger[i32,i32,+]").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "@(impl:local)dictmerger[i32,i32,+]"
    );

    let e = parse_expr("@(impl:local, num_keys:12l) dictmerger[i32,i32,+]").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "@(impl:local,num_keys:12)dictmerger[i32,i32,+]"
    );

    let e = parse_expr("a: i32 + b").unwrap();
    assert_eq!(print_typed_expr_without_indent(&e), "(a:i32+b:?)");

    let e = parse_expr("|a:i8| a").unwrap();
    assert_eq!(print_typed_expr_without_indent(&e), "|a:i8|a:?");

    assert!(parse_expr("10 * * 2").is_err());

    let p = parse_program("macro a(x) = x+x; macro b() = 5; a(b)").unwrap();
    assert_eq!(p.macros.len(), 2);
    assert_eq!(print_expr_without_indent(&p.body), "(a)(b)");
    assert_eq!(print_expr_without_indent(&p.macros[0].body), "(x+x)");
    assert_eq!(print_expr_without_indent(&p.macros[1].body), "5");

    let t = &parse_type("{i32, vec[vec[?]], ?}").unwrap().to_string();
    assert_eq!(t, "{i32,vec[vec[?]],?}");

    let t = &parse_type("{}").unwrap().to_string();
    assert_eq!(t, "{}");
}

#[test]
fn operator_precedence() {
    let e = parse_expr("a - b - c - d").unwrap();
    assert_eq!(print_expr_without_indent(&e), "(((a-b)-c)-d)");

    let e = parse_expr("a || b && c | d ^ e & f == g > h + i * j").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "(a||(b&&(c|(d^(e&(f==(g>(h+(i*j)))))))))"
    );

    let e = parse_expr("a * b + c > d == e & f ^ g | h && i || j").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "(((((((((a*b)+c)>d)==e)&f)^g)|h)&&i)||j)"
    );

    let e = parse_expr("a / b - c <= d != e & f ^ g | h && i || j").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "(((((((((a/b)-c)<=d)!=e)&f)^g)|h)&&i)||j)"
    );

    let e = parse_expr("a % b - c >= d != e & f ^ g | h && i || j").unwrap();
    assert_eq!(
        print_expr_without_indent(&e),
        "(((((((((a%b)-c)>=d)!=e)&f)^g)|h)&&i)||j)"
    );
}

#[test]
fn read_to_end_of_input() {
    assert!(parse_expr("a + b").is_ok());
    assert!(parse_expr("a + b macro").is_err());
    assert!(parse_type("vec[i32]").is_ok());
    assert!(parse_expr("vec[i32] 1").is_err());
    assert!(parse_program("macro a() = b; a() + b").is_ok());
    assert!(parse_program("macro a() = b; a() + b;").is_err());
}

#[test]
fn parse_and_print_literal_expressions() {
    let tests = vec![
        // i32 literal expressions
        ("23", "23"),
        ("0b111", "7"),
        ("0xff", "255"),
        // i64 literal expressions
        ("23L", "23L"),
        ("7L", "7L"),
        ("0xffL", "255L"),
        // f64 literal expressions
        ("23.0", "23.0"),
        ("23.5", "23.5"),
        ("23e5", "2300000.0"),
        ("23.5e5", "2350000.0"),
        // f32 literal expressions
        ("23.0f", "23.0F"),
        ("23.5f", "23.5F"),
        ("23e5f", "2300000.0F"),
        ("23.5e5f", "2350000.0F"),
        // bool literal expressions
        ("true", "true"),
        ("false", "false"),
    ];

    for test in tests {
        let e = parse_expr(test.0).unwrap();
        assert_eq!(print_expr_without_indent(&e).as_str(), test.1);
    }

    // Test overflow of integer types
    assert!(parse_expr("999999999999999").is_err()); // i32 literal too big
    assert!(parse_expr("999999999999999L").is_ok());
    assert!(parse_expr("999999999999999999999999999999L").is_err()); // i64 literal too big
}

#[test]
fn parse_and_print_simple_expressions() {
    let e = parse_expr("23 + 32").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "(23+32)");

    let e = parse_expr("2 - 3 - 4").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "((2-3)-4)");

    let e = parse_expr("2 - (3 - 4)").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "(2-(3-4))");

    let e = parse_expr("a").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "a");

    let e = parse_expr("let a = 2; a").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "(let a=(2);a)");

    let e = parse_expr("let a = 2.0; a").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "(let a=(2.0);a)");

    let e = parse_expr("[1, 2, 3]").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "[1,2,3]");

    let e = parse_expr("[1.0, 2.0, 3.0]").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "[1.0,2.0,3.0]");

    let e = parse_expr("|a, b| a + b").unwrap();
    assert_eq!(print_expr_without_indent(&e).as_str(), "|a:?,b:?|(a+b)");

    let e = parse_expr("for(d, appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(d,appender[?],|e|(e+1))"
    );
}

#[test]
fn parse_and_print_for_expressions() {
    let e = parse_expr("for(d, appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(d,appender[?],|e|(e+1))"
    );

    let e = parse_expr("for(iter(d), appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(d,appender[?],|e|(e+1))"
    );

    let e = parse_expr("for(iter(d,0L,4L,1L), appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(iter(d,0L,4L,1L),appender[?],|e|(e+1))"
    );

    let e = parse_expr("for(zip(d), appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(d,appender[?],|e|(e+1))"
    );

    let e = parse_expr("for(zip(d,e), appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(zip(d,e),appender[?],|e|(e+1))"
    );

    let e = parse_expr("for(zip(a,b,iter(c,0L,4L,1L),iter(d)), appender, |e| e+1)").unwrap();
    assert_eq!(
        print_expr_without_indent(&e).as_str(),
        "for(zip(a,b,iter(c,0L,4L,1L),d),appender[?],|e|(e+1))"
    );
}
