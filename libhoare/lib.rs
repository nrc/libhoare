// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// See ../readme.md for an overview.

#![feature(plugin_registrar, quote, rustc_private)]

extern crate rustc;
extern crate syntax;

use syntax::ast;
use syntax::ast::{Item, MetaItem};
use syntax::codemap::{Span,Spanned};
use syntax::ext::base::{ExtCtxt, Modifier};
use syntax::ext::quote::rt::ExtParseUtils;
use syntax::parse::token;
use syntax::ptr::P;
use rustc::plugin::Registry;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(token::intern("precond"),
                                  Modifier(Box::new(precond)));
    reg.register_syntax_extension(token::intern("postcond"),
                                  Modifier(Box::new(postcond)));
    reg.register_syntax_extension(token::intern("invariant"),
                                  Modifier(Box::new(invariant)));
    reg.register_syntax_extension(token::intern("debug_precond"),
                                  Modifier(Box::new(debug_precond)));
    reg.register_syntax_extension(token::intern("debug_postcond"),
                                  Modifier(Box::new(debug_postcond)));
    reg.register_syntax_extension(token::intern("debug_invariant"),
                                  Modifier(Box::new(debug_invariant)));
}

fn precond(cx: &mut ExtCtxt,
           sp: Span,
           attr: &MetaItem,
           item: P<Item>) -> P<Item> {
    match &item.node {
        &ast::ItemFn(ref decl, style, abi, ref generics, _) => {
            // Parse out the predicate supplied to the syntax extension.
            let pred = match make_predicate(cx, sp, attr, "precond") {
                Some(pred) => pred,
                None => return item.clone()
            };
            let pred_str = &pred;
            let pred = cx.parse_expr(pred_str.to_string());

            // Construct the wrapper function.
            let fn_name = token::get_ident(item.ident);

            let mut stmts = Vec::new();
            stmts.push(assert(&*cx, "precondition of", &fn_name, pred.clone(), pred_str));

            let fn_name = ast::Ident::new(token::intern(&format!("__inner_fn_{}", fn_name)));
            // Construct the inner function.
            let inner_item = P(Item { attrs: Vec::new(), vis: ast::Inherited, .. (*item).clone() });
            stmts.push(fn_decl(sp, fn_name, inner_item));

            // Construct the function call.
            let args = match args(cx, &**decl, sp) {
                Some(args) => args,
                None => { return item.clone(); }
            };
            let ty_args = ty_args(generics, sp);
            stmts.push(assign_expr(&*cx, fn_name, args, ty_args));

            let body = fn_body(cx, stmts, sp);
            P(Item { node: ast::ItemFn(decl.clone(), style, abi, generics.clone(), body),
                     .. (*item).clone() })
        }
        _ => {
            cx.span_err(sp, "Precondition on non-function item");
            item.clone()
        }
    }
}

fn postcond(cx: &mut ExtCtxt,
            sp: Span,
            attr: &MetaItem,
            item: P<Item>) -> P<Item> {
    match &item.node {
        &ast::ItemFn(ref decl, style, abi, ref generics, _) => {
            // Parse out the predicate supplied to the syntax extension.
            let pred = match make_predicate(cx, sp, attr, "postcond") {
                Some(pred) => pred,
                None => return item.clone()
            };
            let pred_str = &pred;
            // Rename `return` to `__result`
            let pred_str = pred_str.replace("return", "__result");
            let pred = cx.parse_expr(pred_str.clone());

            // Construct the wrapper function.
            let fn_name = token::get_ident(item.ident);

            let mut stmts = Vec::new();
            let fn_ident = ast::Ident::new(token::intern(&format!("__inner_{}", fn_name)));
            // Construct the inner function.
            let inner_item = P(Item { attrs: Vec::new(), vis: ast::Inherited, .. (*item).clone() });
            stmts.push(fn_decl(sp, fn_ident, inner_item));

            // Construct the function call.
            let args = match args(cx, &**decl, sp) {
                Some(args) => args,
                None => { return item.clone(); }
            };
            let ty_args = ty_args(generics, sp);
            stmts.push(assign_expr(&*cx, fn_ident, args, ty_args));

            stmts.push(assert(&*cx, "postcondition of", &fn_name, pred, &pred_str[..]));

            let body = fn_body(cx, stmts, sp);
            P(Item { node: ast::ItemFn(decl.clone(), style, abi, generics.clone(), body),
                     .. (*item).clone() })
        }
        _ => {
            cx.span_err(sp, "Postcondition on non-function item");
            item.clone()
        }
    }
}

fn invariant(cx: &mut ExtCtxt,
             sp: Span,
             attr: &MetaItem,
             item: P<Item>) -> P<Item> {
    match &item.node {
        &ast::ItemFn(ref decl, style, abi, ref generics, _) => {
            // Parse out the predicate supplied to the syntax extension.
            let pred = match make_predicate(cx, sp, attr, "invariant") {
                Some(pred) => pred,
                None => return item.clone()
            };
            let pred_str = &pred;
            let pred = cx.parse_expr(pred_str.to_string());

            // Construct the wrapper function.
            let fn_name = token::get_ident(item.ident);

            let mut stmts = Vec::new();
            stmts.push(assert(&*cx, "invariant entering", &fn_name, pred.clone(), pred_str));

            let fn_ident = ast::Ident::new(token::intern(&format!("__inner_{}", fn_name)));
            // Construct the inner function.
            let inner_item = P(Item { attrs: Vec::new(), vis: ast::Inherited, .. (*item).clone() });
            stmts.push(fn_decl(sp, fn_ident, inner_item));

            // Construct the function call.
            let args = match args(cx, &**decl, sp) {
                Some(args) => args,
                None => { return item.clone(); }
            };
            let ty_args = ty_args(generics, sp);
            stmts.push(assign_expr(&*cx, fn_ident, args, ty_args));

            stmts.push(assert(&*cx, "invariant leaving", &fn_name, pred, pred_str));

            let body = fn_body(cx, stmts, sp);
            P(Item { node: ast::ItemFn(decl.clone(), style, abi, generics.clone(), body),
                     .. (*item).clone() })
        }
        _ => {
            cx.span_err(sp, "Invariant on non-function item");
            item.clone()
        }
    }
}

fn debug_precond(cx: &mut ExtCtxt,
                 sp: Span,
                 attr: &MetaItem,
                 item: P<Item>) -> P<Item> {
    if_debug(cx, |cx| precond(cx, sp, attr, item.clone()), item.clone())
}
fn debug_postcond(cx: &mut ExtCtxt,
                  sp: Span,
                  attr: &MetaItem,
                  item: P<Item>) -> P<Item> {
    if_debug(cx, |cx| postcond(cx, sp, attr, item.clone()), item.clone())
}
fn debug_invariant(cx: &mut ExtCtxt,
                   sp: Span,
                   attr: &MetaItem,
                   item: P<Item>) -> P<Item> {
    if_debug(cx, |cx| invariant(cx, sp, attr, item.clone()), item.clone())
}

// Executes f if we are compiling in debug mode, returns item otherwise.
fn if_debug<F>(cx: &mut ExtCtxt, f: F, item: P<Item>) -> P<Item>
    where F: Fn(&mut ExtCtxt) -> P<Item> {
    if !cx.cfg().iter().any(
        |item| item.node == ast::MetaWord(token::get_name(token::intern("ndebug")))) {
        f(cx)
    } else {
        item
    }
}

// Takes the predicate passed to the syntax extension, checks it and turns it
// into a string.
fn make_predicate(cx: &ExtCtxt,
                  sp: Span,
                  attr: &MetaItem,
                  cond_name: &str) -> Option<token::InternedString> {
    fn debug_name(cond_name: &str) -> String {
        let mut result = "debug_".to_string();
        result.push_str(cond_name);
        result
    }

    match &attr.node {
        &ast::MetaNameValue(ref name, ref lit) => {
            if name == &token::get_name(token::intern(cond_name)) ||
               name == &token::get_name(token::intern(&debug_name(cond_name)[..])) {
                match &lit.node {
                    &ast::LitStr(ref lit, _) => {
                        Some(lit.clone())
                    }
                    _ => {
                        cx.span_err(sp, "unexpected kind of predicate for condition");
                        None
                    }
                }
            } else {
                cx.span_err(sp, &format!("unexpected name in condition: {}", name)[..]);
                None
            }
        },
        _ => {
            cx.span_err(sp, "unexpected format of condition");
            None
        }
    }
}

// Make an assertion. cond_type should be the kind of assertion (precondition
// postcondition, etc.). fn_name is the name of the function we are operating on.
fn assert(cx: &ExtCtxt,
          cond_type: &str,
          fn_name: &token::InternedString,
          pred: P<ast::Expr>,
          pred_str: &str) -> P<ast::Stmt> {
    let label = format!("\"{} {} ({})\"", cond_type, fn_name,
                        pred_str.replace("\"", "\\\""));
    let label = cx.parse_expr(label);
    quote_stmt!(&*cx, assert!($pred, $label);).unwrap()
}

// Check that a pattern can trivially be used to instantiate that pattern.
// For example if we have `fn foo((x, y): ...) {...}` we can call `foo((x, y))`
// (assuming x and y are in scope and have the correct type) with the exact same
// syntax as the pattern is declared. But if the pattern is `z @ (x,y)` we cannot
// (we need to use `(x, y)`).
//
// Ideally we would just translate the pattern to the correct one. But in for now
// we just check if we can skip the translation phase and fail otherwise (FIXME).
fn is_sane_pattern(pat: &ast::Pat) -> bool {
    match &pat.node {
        &ast::PatWild(_) | &ast::PatMac(_) | &ast::PatStruct(..) |
        &ast::PatLit(_) | &ast::PatRange(..) | &ast::PatVec(..) => false,
        &ast::PatIdent(ast::BindByValue(ast::MutImmutable), _, _) => true,
        &ast::PatIdent(..) => false,
        &ast::PatEnum(_, Some(ref ps)) | &ast::PatTup(ref ps) =>
            ps.iter().all(|p| is_sane_pattern(&**p)),
        &ast::PatEnum(..) => false,
        &ast::PatBox(ref p) | &ast::PatRegion(ref p, _) => is_sane_pattern(&**p)
    }
}

fn args(cx: &ExtCtxt, decl: &ast::FnDecl, sp: Span) -> Option<Vec<ast::TokenTree>> {
    if !decl.inputs.iter().map(|a| &*a.pat).all(is_sane_pattern) {
        return None;
    }

    let cm = &cx.parse_sess.span_diagnostic.cm;
    Some(decl.inputs
        .iter()
        // span_to_snippet really shouldn't return None, so I hope the
        // unwrap is OK. Not sure we can do anything it is does in any case.
        .map(|a| cx.parse_tts(cm.span_to_snippet(a.pat.span).unwrap()))
        .collect::<Vec<_>>()
        .connect(&ast::TtToken(sp, token::Comma)))
}

fn ty_args(generics: &ast::Generics, sp: Span) -> Vec<ast::TokenTree> {
    generics.ty_params
        .iter()
        .map(|tp| tp.ident)
        .map(|ident| vec![token::Ident(ident, token::Plain)])
        .collect::<Vec<_>>()
        .connect(&token::Comma)
        .into_iter()
        .map(|t| ast::TtToken(sp, t))
        .collect()
}

// Creates the inner function, which is the original item (which must be an
// ast::ItemFn) with the new name fn_name.
fn fn_decl(sp: Span,
           fn_name: ast::Ident,
           item: P<Item>) -> P<ast::Stmt> {
    match &item.node {
        &ast::ItemFn(ref decl, style, abi, ref generics, ref body) => {
            let inner = Item {
                ident: fn_name,
                node: ast::ItemFn(decl.clone(), style, abi, generics.clone(), body.clone()),
                .. (*item).clone() };

            let inner = ast::DeclItem(P(inner));
            let inner = P(Spanned{ node: inner, span: sp });

            let stmt = ast::StmtDecl(inner, ast::DUMMY_NODE_ID);
            P(Spanned{ node: stmt, span: sp })
        }
        _ => panic!("This should be checked by the caller")
    }
}

fn fn_body(cx: &ExtCtxt,
           stmts: Vec<P<ast::Stmt>>,
           sp: Span) -> P<ast::Block> {
    P(ast::Block {
        stmts: stmts,
        expr: Some(result_expr(&*cx)),
        id: ast::DUMMY_NODE_ID,
        rules: ast::DefaultBlock,
        span: sp
    })
}

fn assign_expr(cx: &ExtCtxt,
               fn_name: ast::Ident,
               arg_toks: Vec<ast::TokenTree>,
               ty_arg_toks: Vec<ast::TokenTree>) -> P<ast::Stmt> {
    if ty_arg_toks.len() > 0 {
        quote_stmt!(cx, let __result = $fn_name::<$ty_arg_toks>($arg_toks);).unwrap()
    } else {
        quote_stmt!(cx, let __result = $fn_name($arg_toks);).unwrap()
    }
}

// The return expr for our wrapper function, just returns __result.
fn result_expr(cx: &ExtCtxt) -> P<ast::Expr> {
    quote_expr!(cx, __result)
}
