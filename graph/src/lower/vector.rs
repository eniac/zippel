//! Vectors: literals, comprehensions, `reduce` and indexing.

use super::*;
use lang::ast::CExps;

impl<C: HasOpFactory> UDag<C> {
    #[inline(never)]
    pub(super) fn lower_vec(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        vs: CExps,
        expected: Option<&ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        let elem = match expected.unwrap_or(&atyp) {
            ATyp::Vec(deref!(elem), _) => Some(elem.clone()),
            _ => None,
        };
        let vec_op = GOp::vec(vs.0.traverse1(&mut |v| self.add_exp(scope, v, elem.clone()))?);
        let atyp = vec_op.typ();
        Ok(self.materialize(vec_op, scope.edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_map(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        l: ExpId,
        x: Spanned<Vid>,
        e: ExpId,
        expected: Option<&ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let map_atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        // The output body takes the expected element type; the domain stays finite.
        let elem_target = match expected {
            Some(ATyp::Vec(deref!(elem), _)) => Some(elem.clone()),
            _ => None,
        };
        // Fast path: lower to a persistent `Op::Map` when the body
        // and domain are pure. Falls back to the unroll otherwise.
        if let Some(map_op) = self.lower_loop_body_template(scope, id, &[], expected)? {
            let atyp = if expected.is_some() {
                map_op.typ()
            } else {
                map_atyp
            };
            return Ok(self.materialize(map_op, scope.edge_type, atyp, span.clone()));
        }

        let te = scope.infer(e)?;

        // Op for [e]
        let oe = self.add_exp(scope, e, None)?;

        let (ie, n) = te.into_vec();

        let input_element_typ = ATyp::from_ctyp(&ie, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &ie))?;

        let mut res = Vec::with_capacity(n.node);
        for i in 0..n.node {
            // Add oe[i] to local variable contexts; the map binder
            // shadows any same-named let binding in the body.
            let mut local_scope = scope.nested();
            let ram_op = GOp::ram(oe.clone(), GOp::index(i));
            let ram_ref = self.materialize(
                ram_op,
                local_scope.edge_type,
                input_element_typ.clone(),
                span.clone(),
            );
            local_scope.vars.insert(&x.node, &ram_ref);
            local_scope.vctx.insert(&x.node, &ie);
            // Add subexpression
            let ol = self.add_exp(&mut local_scope, l, elem_target.clone())?;
            res.push(ol);
        }
        let vec_op = GOp::vec(res);
        let atyp = if expected.is_some() {
            vec_op.typ()
        } else {
            map_atyp
        };
        Ok(self.materialize(vec_op, scope.edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_reduce(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        op: BinOp,
        v: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let reduce_map = if let CExp::Map(body, binder, domain) = scope.exprs[v].clone() {
            self.try_build_reduce_map(scope, op, body, binder.node, domain, &[])?
        } else {
            None
        };
        if let Some(rm) = reduce_map {
            let atyp = ATyp::from_ctyp(&typ, scope.kctx)
                .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
            return Ok(self.materialize(rm, scope.edge_type, atyp, span.clone()));
        }
        let ov = self.add_exp(scope, v, None)?;
        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        Ok(self.materialize(GOp::reduce(op, ov), scope.edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_ram(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        a: ExpId,
        b: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        // Add children
        let oa = self.add_exp(scope, a, None)?;
        let ob = self.add_exp(scope, b, None)?;
        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        Ok(self.materialize(GOp::ram(oa, ob), scope.edge_type, atyp, span.clone()))
    }
}
