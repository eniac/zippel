//! Vectors: literals, comprehensions, `reduce` and indexing.

use super::*;
use lang::ast::CExps;

impl<C: HasOpFactory> UDag<C> {
    #[inline(never)]
    pub(super) fn lower_vec(&mut self, step: Step<'_, C>, vs: CExps) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            expected,
            ..
        } = step;
        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        let elem = match expected.as_ref().unwrap_or(&atyp) {
            ATyp::Vec(deref!(elem), _) => Some(elem.clone()),
            _ => None,
        };
        let vec_op = GOp::vec(vs.0.traverse1(&mut |v| {
            self.add_exp(
                exprs,
                v,
                transcr,
                edge_type,
                kctx,
                fctx,
                vctx,
                vars,
                elem.clone(),
            )
        })?);
        let atyp = vec_op.typ();
        Ok(self.materialize(vec_op, edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_map(
        &mut self,
        step: Step<'_, C>,
        l: ExpId,
        x: Spanned<Vid>,
        e: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            expected,
            ..
        } = step;
        let map_atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        // The output body takes the expected element type; the domain stays finite.
        let elem_target = match expected.as_ref() {
            Some(ATyp::Vec(deref!(elem), _)) => Some(elem.clone()),
            _ => None,
        };
        // Fast path: lower to a persistent `Op::Map` when the body
        // and domain are pure. Falls back to the unroll otherwise.
        if let Some(map_op) = self.lower_loop_body_template(
            exprs,
            id,
            &[],
            kctx,
            fctx,
            vctx,
            vars,
            expected.as_ref(),
        )? {
            let atyp = if expected.is_some() {
                map_op.typ()
            } else {
                map_atyp
            };
            return Ok(self.materialize(map_op, edge_type, atyp, span.clone()));
        }

        let te = exprs.infer(e, kctx, fctx, vctx)?;

        // Op for [e]
        let oe = self.add_exp(exprs, e, transcr, edge_type, kctx, fctx, vctx, vars, None)?;

        let (ie, n) = te.into_vec();

        let input_element_typ =
            ATyp::from_ctyp(&ie, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), &ie))?;

        let mut res = Vec::with_capacity(n.node);
        for i in 0..n.node {
            // Add oe[i] to local vars and vctx; the map binder
            // shadows any same-named let binding in the body.
            let mut local_vars = vars.clone();
            let mut local_vctx = vctx.clone();
            let ram_op = GOp::ram(oe.clone(), GOp::index(i));
            let ram_ref =
                self.materialize(ram_op, edge_type, input_element_typ.clone(), span.clone());
            local_vars.insert(&x.node, &ram_ref);
            local_vctx.insert(&x.node, &ie);
            // Add subexpression
            let ol = self.add_exp(
                exprs,
                l,
                transcr,
                edge_type,
                kctx,
                fctx,
                &local_vctx,
                &local_vars,
                elem_target.clone(),
            )?;
            res.push(ol);
        }
        let vec_op = GOp::vec(res);
        let atyp = if expected.is_some() {
            vec_op.typ()
        } else {
            map_atyp
        };
        Ok(self.materialize(vec_op, edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_reduce(
        &mut self,
        step: Step<'_, C>,
        op: BinOp,
        v: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        let reduce_map = if let CExp::Map(body, binder, domain) = exprs[v].clone() {
            self.try_build_reduce_map(
                exprs,
                op,
                body,
                binder.node,
                domain,
                &[],
                kctx,
                fctx,
                vctx,
                vars,
            )?
        } else {
            None
        };
        if let Some(rm) = reduce_map {
            let atyp = ATyp::from_ctyp(typ, kctx)
                .ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
            return Ok(self.materialize(rm, edge_type, atyp, span.clone()));
        }
        let ov = self.add_exp(exprs, v, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        Ok(self.materialize(GOp::reduce(op, ov), edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_ram(
        &mut self,
        step: Step<'_, C>,
        a: ExpId,
        b: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            id,
            typ,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        // Add children
        let oa = self.add_exp(exprs, a, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        let ob = self.add_exp(exprs, b, transcr, edge_type, kctx, fctx, vctx, vars, None)?;
        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        Ok(self.materialize(GOp::ram(oa, ob), edge_type, atyp, span.clone()))
    }
}
