fn main() {
    let expr = bidirectional::Expr::Unit;
    let tcx = bidirectional::TyCtx::new();

    match tcx.synth_expr_ty(expr) {
        Ok((ty, p, _)) => println!("Type: {ty:?} {p:?}"),
        Err(msg) => println!("Error: {msg}"),
    }
}
