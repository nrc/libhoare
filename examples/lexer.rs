// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This is a very simple lexer. It is not great code, but illustrates the use
// of conditions and invariants in a realistic-ish bit of code (in particular,
// note that we pretend that unicode doesn't exist and strings are ascii, which
// is bad).

// Only lexes string literals and returns slices into the initial string which
// are the output 'token'.

// The coding style is a bit weird, because I have to avoid using methods.

// The lexing rules are that a token is separated by whitespace (not returned)
// or a symbol (returned as a single token). Quotes can be used and everything
// inside the quotes and the quotes themselves are a single token (including
// symbols and whitespace).

#![feature(plugin)]

#![plugin(hoare)]

use std::collections::HashSet;

// Symbols with special meaning
const COMMA: &'static str = ",";
const OR: &'static str = "|";
const COLON: &'static str = ":";
const ARROW: &'static str = "::=";
const TICK: &'static str = "`";

static TS: &'static [&'static str] = &[COMMA, OR, COLON, ARROW, TICK];
static INDEXES: &'static [usize] = &[0, 1, 2, 3, 4];

static QUOTE: char = '\'';

// Lex input into a Vec of tokens.
pub fn tokenise(input: &'static str) -> Vec<&'static str> {
    let mut result = Vec::with_capacity(32);
    let mut lex = new_lexer(input);
    loop {
        let next = next(&mut lex);
        if next.is_none() {
            break;
        }
        result.push(next.unwrap());
    }
    result
}

struct Lexer {
    input: &'static str,
    start: usize,
    end: usize,
}

#[postcond="__result.start == __result.end"]
fn new_lexer(input: &'static str) -> Lexer {
    Lexer {
        input: input,
        start: 0,
        end: 0,
    }
}

// Returns the next token or None if EOF.
#[invariant="this.start == this.end"]
fn next(this: &mut Lexer) -> Option<&'static str> {
    assert!(this.start == this.end);

    scan_to_token(this);
    if this.start >= this.input.len() {
        return None;
    }
    scan_token(this);

    let tok = cur_token(this);
    this.start = this.end;
    return Some(tok);
}

// Returns the current token.
#[precond="this.end > this.start"]
fn cur_token(this: &Lexer) -> &'static str {
    &this.input[this.start..this.end]
}

// Advance start to next non-whitespace char, or EOF.
#[postcond="this.start == this.end"]
fn scan_to_token(this: &mut Lexer) {
    while this.start < this.input.len() && is_space(this, this.start) {
        this.start += 1;
    }
    this.end = this.start;
}

// Advance this.end to the end of the current token or EOF
#[precond="this.start < this.input.len() && !is_space(this, this.start) && this.start == this.end"]
#[postcond="this.end - this.start > 0 && !is_space(this, this.end-1)"]
fn scan_token(this: &mut Lexer) {
    // The set of possible terminals we could be lexing.
    let mut terminals: HashSet<usize> = HashSet::new();

    // If the token is quoted, eat the opening quote and remember to eat the
    // closing quote at the end.
    let (quoted, in_term) = if is_quote(this, this.start) {
        this.end += 2;
        (true, false)
    } else {
        terminals.extend(INDEXES.iter().map(|i| *i));
        // See if the first char matches any terminal. Means we'll match the
        // first char twice, but no biggie.
        terminals = terminals.into_iter().filter(
            |t| this.input.as_bytes()[this.start] == TS[*t].as_bytes()[0]).collect();
        this.end += 1;
        (false, terminals.len() > 0)
    };

    while this.end < this.input.len() {
        // End of token - quote
        if is_quote(this, this.end) {
            if quoted {
                this.end += 1;
            }
            return;
        }

        if quoted {
            this.end += 1;
            continue;
        }
        // End of token - whitespace
        if is_space(this, this.end) {
            return;
        }

        if in_term {
            // Lexing a terminal, check we're still lexing one.
            assert!(terminals.len() > 0);
            // winner is true if there is exactly one possibile terminal which
            // could be selected.
            let winner = if terminals.iter().filter(
                |t| TS[**t].len() == this.end - this.start).count() == 1 {
                true
            } else {
                false
            };
            terminals = terminals.into_iter().filter(|t| {
                let offset = this.end - this.start;
                offset < TS[*t].len()
                    && this.input.as_bytes()[this.end] == TS[*t].as_bytes()[offset]
            }).collect();
            if terminals.len() == 0 {
                // Got to the end of the only possibility.
                assert!(winner, "WHOOPS! Went from >1 to 0 possibilities to lex");
                return;
            }
        } else {
            // Not matching a terminal, so if we start to match one, then
            // we're at the end of the current terminal.
            for t in TS.iter() {
                if this.input.as_bytes()[this.end] == t.as_bytes()[0] {
                    return;
                }
            }
        }
        this.end += 1;
    }
}

// true if self.start points to whitespace (space or newline)
#[precond="index < this.input.as_bytes().len()"]
fn is_space(this: &Lexer, index: usize) -> bool {
    this.input.as_bytes()[index] == ' ' as u8 || this.input.as_bytes()[index] == '\n' as u8
}

// true if self.start points to '
#[precond="index < this.input.as_bytes().len()"]
fn is_quote(this: &Lexer, index: usize) -> bool {
    this.input.as_bytes()[index] == QUOTE as u8
}

fn main() {
    let toks = tokenise("hello there: 'mr |world'");
    for t in toks.iter() {
        println!("{}", t);
    }
}
