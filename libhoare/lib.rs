// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
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
use syntax::codemap::{self, Span};
use syntax::ext::base::{ExtCtxt, MultiModifier, Annotatable};
use syntax::ext::quote::rt::{ExtParseUtils, ToTokens};
use syntax::ext::build::AstBuilder;
use syntax::fold::{Folder, noop_fold_expr, noop_fold_mac};
use syntax::parse::token;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;
use rustc::plugin::Registry;

// Assuming this is going to be Ok because syntax extensions can't be used
// concurrently. What could go wrong?
static mut RUN_COUNT: u32 = 0;

fn inc_run_count() {
    unsafe {
        RUN_COUNT += 1;
    }
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(token::intern("precond"),
                                  MultiModifier(Box::new(precond)));
    reg.register_syntax_extension(token::intern("postcond"),
                                  MultiModifier(Box::new(postcond)));
    reg.register_syntax_extension(token::intern("invariant"),
                                  MultiModifier(Box::new(invariant)));
    reg.register_syntax_extension(token::intern("debug_precond"),
                                  MultiModifier(Box::new(debug_precond)));
    reg.register_syntax_extension(token::intern("debug_postcond"),
                                  MultiModifier(Box::new(debug_postcond)));
    reg.register_syntax_extension(token::intern("debug_invariant"),
                                  MultiModifier(Box::new(debug_invariant)));
}

fn precond(cx: &mut ExtCtxt,
           sp: Span,
           attr: &MetaItem,
           item: Annotatable)
    -> Annotatable
{
    inc_run_count();
    map_annotatble(cx, sp, attr, item, Contract::Precond)
}

fn postcond(cx: &mut ExtCtxt,
            sp: Span,
            attr: &MetaItem,
            item: Annotatable)
    -> Annotatable
{
    inc_run_count();
    map_annotatble(cx, sp, attr, item, Contract::Postcond)
}

fn invariant(cx: &mut ExtCtxt,
             sp: Span,
             attr: &MetaItem,
             item: Annotatable)
    -> Annotatable
{
    inc_run_count();
    map_annotatble(cx, sp, attr, item, Contract::Invariant)
}


fn contract_body(ident: ast::Ident,
                 decl: &ast::FnDecl,
                 body: &ast::Block,
                 cx: &mut ExtCtxt,
                 sp: Span,
                 attr: &MetaItem,
                 contract: Contract)
    -> Result<P<ast::Block>, ()>
{
    // Parse out the predicate supplied to the syntax extension.
    let pred = try!(make_predicate(cx, sp, attr, contract.short_str()));
    let mut pred_str = pred.to_string();

    // Rename `return` to `__result`
    let result_name = result_name();
    if contract.checks_return() {
        pred_str = pred_str.replace("return", &result_name.to_string());
    }

    let pred = cx.parse_expr(pred_str.clone());

    // Construct the new function.
    let fn_name = ident.name.as_str();

    let mut stmts = Vec::new();

    // Check precondition.
    if contract.has_precond() {
        stmts.push(assert(cx, contract.pre_str(), &fn_name, pred.clone(), &pred_str));
    }

    let init_stmt = quote_stmt!(cx, let mut $result_name = None;).unwrap();
    stmts.push(init_stmt);

    stmts.push(make_body(cx, (*body).clone(), sp, &decl.output));

    let unwrap = quote_stmt!(cx, let $result_name = $result_name.unwrap();).unwrap();
    stmts.push(unwrap);

    // Check postcondition.
    if contract.has_postcond() {
        stmts.push(assert(cx, contract.post_str(), &fn_name, pred, &pred_str));
    }

    Ok(fn_body(cx, stmts, sp))
}

enum Contract {
    Precond,
    Postcond,
    Invariant,
}

impl Contract {
    fn short_str(&self) -> &'static str {
        match self {
            &Contract::Precond => "precond",
            &Contract::Postcond => "postcond",
            &Contract::Invariant => "invariant",
        }
    }

    fn long_str(&self) -> &'static str {
        match self {
            &Contract::Precond => "Precondition",
            &Contract::Postcond => "Postcondition",
            &Contract::Invariant => "Invariant",
        }
    }

    fn pre_str(&self) -> &'static str {
        match self {
            &Contract::Precond => "precondition of",
            &Contract::Postcond => panic!(),
            &Contract::Invariant => "invariant entering",
        }
    }

    fn post_str(&self) -> &'static str {
        match self {
            &Contract::Precond => panic!(),
            &Contract::Postcond => "postcondition of",
            &Contract::Invariant => "invariant leaving",
        }
    }

    fn has_precond(&self) -> bool {
        match self {
            &Contract::Precond => true,
            &Contract::Postcond => false,
            &Contract::Invariant => true,
        }
    }

    fn has_postcond(&self) -> bool {
        match self {
            &Contract::Precond => false,
            &Contract::Postcond => true,
            &Contract::Invariant => true,
        }
    }

    fn checks_return(&self) -> bool {
        match self {
            &Contract::Postcond => true,
            _ => false,
        }
    }
}

// Maps contract_body over item, which must be a function-like item-like-thing.
fn map_annotatble(cx: &mut ExtCtxt,
                  sp: Span,
                  attr: &MetaItem,
                  item: Annotatable,
                  contract: Contract)
    -> Annotatable
{
    match item {
        Annotatable::Item(item) => {
            match &item.node {
                &ast::ItemFn(ref decl, unsafety, constness, abi, ref generics, ref body) => {
                    match contract_body(item.ident, decl, body, cx, sp, attr, contract) {
                        Ok(body) => Annotatable::Item(P(Item { node: ast::ItemFn(decl.clone(),
                                                                                 unsafety,
                                                                                 constness,
                                                                                 abi,
                                                                                 generics.clone(),
                                                                                 body),
                                                               .. (*item).clone() })),
                        Err(_) => Annotatable::Item(item.clone()),
                    }
                }
                _ => {
                    cx.span_err(sp, &format!("{} on non-function item", contract.long_str()));
                    Annotatable::Item(item.clone())
                }
            }
        }
        Annotatable::ImplItem(item) => {
            match item.node {
                ast::ImplItem_::MethodImplItem(ref sig, ref body) => {
                    match contract_body(item.ident, &sig.decl, body, cx, sp, attr, contract) {
                        Ok(body) => Annotatable::ImplItem(P(ast::ImplItem {
                            node: ast::ImplItem_::MethodImplItem(sig.clone(), body),
                            .. (*item).clone()
                        })),
                        Err(_) => Annotatable::ImplItem(item.clone()),
                    }
                }
                _ => {
                    cx.span_err(sp, &format!("{} on non-function impl item", contract.long_str()));
                    Annotatable::ImplItem(item.clone())
                }
            }
        }
        Annotatable::TraitItem(item) => {
            match item.node {
                ast::TraitItem_::MethodTraitItem(ref sig, Some(ref body)) => {
                    match contract_body(item.ident, &sig.decl, body, cx, sp, attr, contract) {
                        Ok(body) => Annotatable::TraitItem(P(ast::TraitItem {
                            node: ast::TraitItem_::MethodTraitItem(sig.clone(), Some(body)),
                            .. (*item).clone()
                        })),
                        Err(_) => Annotatable::TraitItem(item.clone()),
                    }
                }
                _ => {
                    cx.span_err(sp, &format!("{} on non-function trait item", contract.long_str()));
                    Annotatable::TraitItem(item.clone())
                }
            }
        }
    }
}

fn debug_precond(cx: &mut ExtCtxt,
                 sp: Span,
                 attr: &MetaItem,
                 item: Annotatable) -> Annotatable {
    if_debug(cx, |cx| precond(cx, sp, attr, item.clone()), item.clone())
}
fn debug_postcond(cx: &mut ExtCtxt,
                  sp: Span,
                  attr: &MetaItem,
                  item: Annotatable) -> Annotatable {
    if_debug(cx, |cx| postcond(cx, sp, attr, item.clone()), item.clone())
}
fn debug_invariant(cx: &mut ExtCtxt,
                   sp: Span,
                   attr: &MetaItem,
                   item: Annotatable) -> Annotatable {
    if_debug(cx, |cx| invariant(cx, sp, attr, item.clone()), item.clone())
}

// Executes f if we are compiling in debug mode, returns item otherwise.
fn if_debug<F>(cx: &mut ExtCtxt, f: F, item: Annotatable) -> Annotatable
    where F: Fn(&mut ExtCtxt) -> Annotatable
{
    if cfg!(debug_assertions) {
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
                  cond_name: &str) -> Result<token::InternedString, ()> {
    fn debug_name(cond_name: &str) -> String {
        let mut result = "debug_".to_string();
        result.push_str(cond_name);
        result
    }

    match &attr.node {
        &ast::MetaNameValue(ref name, ref lit) => {
            if name.to_string() == cond_name ||
               name.to_string() == &debug_name(cond_name)[..] {
                match &lit.node {
                    &ast::LitStr(ref lit, _) => {
                        Ok(lit.clone())
                    }
                    _ => {
                        cx.span_err(sp, "unexpected kind of predicate for condition");
                        Err(())
                    }
                }
            } else {
                cx.span_err(sp, &format!("unexpected name in condition: {}", name)[..]);
                Err(())
            }
        },
        _ => {
            cx.span_err(sp, "unexpected format of condition");
            Err(())
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
    let label = format!("{} {} ({})", cond_type, fn_name,
                        pred_str.replace("\"", "\\\""));
    let label = &label;
    quote_stmt!(cx, assert!($pred, $label);).unwrap()
}

fn fn_body(cx: &ExtCtxt,
           stmts: Vec<P<ast::Stmt>>,
           sp: Span) -> P<ast::Block> {
    P(ast::Block {
        stmts: stmts,
        expr: Some(result_expr(cx)),
        id: ast::DUMMY_NODE_ID,
        rules: ast::DefaultBlock,
        span: sp
    })
}

// The return expr for our wrapper function, just returns __result.
fn result_expr(cx: &ExtCtxt) -> P<ast::Expr> {
    let result_name = result_name();
    quote_expr!(cx, $result_name)
}

fn result_name() -> ast::Ident {
    unsafe {
        ast::Ident::new(token::intern(&format!("__result_{}", RUN_COUNT)))
    }
}

fn loop_label() -> ast::Ident {
    unsafe {
        ast::Ident::new(token::intern(&format!("'__hoare_{}", RUN_COUNT)))
    }
}

fn make_body(cx: &ExtCtxt,
             mut body: ast::Block,
             sp: Span,
             ret: &ast::FunctionRetTy)
    -> P<ast::Stmt>
{
    // Fold return expressions into breaks.
    body.stmts = fold_stmts(cx, &body.stmts);

    let loop_label = loop_label();

    // Turn the optional returned expression into an assignment
    // into __result and a break.
    body.stmts.extend(terminate_loop(cx, &body.expr, ret).into_iter());
    // FIXME Sometimes (e.g., after a return which was converted to a break) this
    // is not necessary, it will then produce unreachable code warnings. Would
    // be better not to generate this code then.
    body.stmts.push(cx.stmt_expr(cx.expr(codemap::DUMMY_SP, ast::Expr_::ExprBreak(Some(loop_label)))));
    body.expr = None;

    cx.stmt_expr(cx.expr(sp, ast::Expr_::ExprLoop(P(body), Some(loop_label))))
}

fn terminate_loop(cx: &ExtCtxt,
                  expr: &Option<P<ast::Expr>>,
                  ret: &ast::FunctionRetTy)
    -> Option<P<ast::Stmt>>
{
    let result_name = result_name();
    match expr {
        &Some(ref expr) => {
            let expr = expr.clone();
            quote_stmt!(cx, $result_name = Some($expr))
        }
        &None if is_void(ret) => quote_stmt!(cx, $result_name = Some(())),
        _ => None,
    }
}

fn is_void(ret: &ast::FunctionRetTy) -> bool {
    match ret {
        &ast::FunctionRetTy::NoReturn(_) => true,
        &ast::FunctionRetTy::DefaultReturn(_) => true,
        &ast::FunctionRetTy::Return(ref ty) => {
            if let ast::Ty_::TyTup(ref tys) = ty.node {
                tys.len() == 0
            } else {
                false
            }
        }
    }
}


// These folding functions walk the AST replacing any returns with breaks.
fn fold_stmts(cx: &ExtCtxt, stmts: &[P<ast::Stmt>]) -> Vec<P<ast::Stmt>> {
    let mut result = Vec::new();
    for s in stmts {
        result.extend(fold_stmt(cx, s.clone()).into_iter());
    }
    result
}

fn fold_stmt(cx: &ExtCtxt, stmt: P<ast::Stmt>) -> SmallVector<P<ast::Stmt>> {
    let mut ret = ReturnFolder { cx: cx };

    ret.fold_stmt(stmt)
}

struct ReturnFolder<'a, 'b: 'a> {
    cx: &'a ExtCtxt<'b>,
}

impl<'a, 'b> Folder for ReturnFolder<'a, 'b> {
    fn fold_expr(&mut self, e: P<ast::Expr>) -> P<ast::Expr> {
        let result_name = result_name();
        let loop_label = loop_label();
        match e.node {
            ast::Expr_::ExprRet(Some(ref expr)) => {
                // We should really fold expr here, but you'd have to be pretty
                // pathalogical to embed a return inside a return.
                let expr = expr.clone();
                // FIXME(#26994) broken quasi-quoting.
                // return quote_expr!(self.cx, { $result_name = Some($expr); break $loop_label; });
                let stmts = vec![quote_stmt!(self.cx, $result_name = Some($expr);).unwrap(),
                                 self.cx.stmt_expr(
                                    self.cx.expr(codemap::DUMMY_SP,
                                        ast::Expr_::ExprBreak(Some(loop_label))))];
                let expr = self.cx.expr_block(self.cx.block(stmts[0].span, stmts, None));
                return expr;
            }
            ast::Expr_::ExprRet(None) => {
                // FIXME(#26994) broken quasi-quoting.
                // return quote_expr!(self.cx, { $result_name = Some(()); break $loop_label; });
                let stmts = vec![quote_stmt!(self.cx, $result_name = Some(());).unwrap(),
                                 self.cx.stmt_expr(
                                    self.cx.expr(codemap::DUMMY_SP,
                                        ast::Expr_::ExprBreak(Some(loop_label))))];
                let expr = self.cx.expr_block(self.cx.block(stmts[0].span, stmts, None));
                return expr;
            }
            _ => {}
        }
        e.map(|e| noop_fold_expr(e, self))
    }

    fn fold_mac(&mut self, mac: ast::Mac) -> ast::Mac {
        noop_fold_mac(mac, self)
    }
}

