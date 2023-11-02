fn main() {
    let expr = bidirectional::Expr::Unit;
    let tcx = bidirectional::TyCtx::new();
    let (ty, p, _) = tcx.synth_expr_ty(expr);
    println!("{ty:?} {p:?}");
}
