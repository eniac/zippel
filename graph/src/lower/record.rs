//! Records: construction, projection and field update.

use super::*;

impl<C: HasOpFactory> UDag<C> {
    #[inline(never)]
    pub(super) fn lower_record(
        &mut self,
        step: Step<'_, C>,
        fields: Ctx<Spanned<String>, ExpId>,
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
        let atyp =
            ATyp::from_ctyp(typ, kctx).ok_or_else(|| ark_error(kctx, vctx, exprs.at(id), typ))?;
        // Fields take the expected field types, else the record's own.
        let ATyp::Record(targets) = expected.as_ref().unwrap_or(&atyp).clone() else {
            unreachable!("a record expression has a record type")
        };
        let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();

        for (field_name, field_exp) in fields.iter() {
            let field_op = self.add_exp(
                exprs,
                *field_exp,
                transcr,
                edge_type,
                kctx,
                fctx,
                vctx,
                vars,
                targets.get(&field_name.node).cloned(),
            )?;
            let hop = mk::<C>(field_op);
            field_ops.insert(field_name, &hop);
        }

        let record_op = GOp::Record(field_ops);
        let atyp = if expected.is_some() {
            record_op.typ()
        } else {
            atyp
        };
        Ok(self.materialize(record_op, edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_proj(
        &mut self,
        step: Step<'_, C>,
        record_exp: ExpId,
        field_name: Spanned<String>,
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
        // For projection, we need to extract the field from the record
        // Check if the record expression is a Record literal
        match exprs[record_exp].clone() {
            CExp::Record(fields) => {
                let field_exp = fields.get(&field_name).ok_or_else(|| {
                    GraphError::from(TypeError::field_not_found(
                        kctx,
                        vctx,
                        exprs.at(record_exp),
                        field_name.as_str(),
                    ))
                })?;

                // Add the field expression to the graph
                self.add_exp(
                    exprs, *field_exp, transcr, edge_type, kctx, fctx, vctx, vars, None,
                )
            }
            CExp::Var(var) => {
                let id_clone = var.clone();
                let record_op = vars.get(&id_clone).ok_or_else(|| {
                    GraphError::from(TypeError::exp(kctx, vctx, exprs.at(record_exp)))
                })?;

                // Try to infer the record type to verify the field exists
                let record_typ = exprs.infer(record_exp, kctx, fctx, vctx)?;

                match &record_typ {
                    CTyp::Record(fields) => {
                        // Verify the field exists and get its type
                        let field_typ_ctyp = fields.get(&field_name).ok_or_else(|| {
                            GraphError::from(TypeError::field_not_found(
                                kctx,
                                vctx,
                                exprs.at(record_exp),
                                field_name.as_str(),
                            ))
                        })?;

                        // Extract the field from the record operation
                        match record_op {
                            Op::Record(record_fields) => {
                                // Direct field access from Record operation
                                record_fields
                                    .get(&field_name)
                                    .ok_or_else(|| {
                                        GraphError::from(TypeError::field_not_found(
                                            kctx,
                                            vctx,
                                            exprs.at(record_exp),
                                            field_name.as_str(),
                                        ))
                                    })
                                    .map(|op| (**op).clone())
                            }
                            Op::Ref(r, _op_typ) => {
                                // If the DAG node stores a Record, extract the
                                // field directly (avoiding an unnecessary Proj node).
                                if let Some(inner) = self[r.node()].op()
                                    && let Op::Record(fields) = inner.get()
                                    && let Some(field_op) = fields.get(&field_name)
                                {
                                    return Ok(field_op.get().clone());
                                }
                                // Record produced by a node (e.g. a record-typed op); add Proj node
                                let field_typ_atyp = ATyp::from_ctyp(field_typ_ctyp, kctx)
                                    .ok_or_else(|| {
                                        GraphError::from(TypeError::located(
                                            exprs.span(id),
                                            TypeError::ark(
                                                kctx,
                                                vctx,
                                                exprs.at(record_exp),
                                                field_typ_ctyp,
                                            ),
                                        ))
                                    })?;
                                // If the record source is an Arg node we don't need
                                // to materialise a Proj node — the field is selected
                                // directly off the typed reference.
                                if self[r.node()].is_arg() {
                                    return Ok(Op::Ref(Ref(r.node()), field_typ_atyp));
                                }
                                let proj_node = self.add_node(
                                    Node::proj(record_op, &field_name, &field_typ_atyp),
                                    span.clone(),
                                );
                                self.add_edges(edge_type, proj_node, record_op.clone());
                                Ok(Op::Ref(Ref(proj_node), field_typ_atyp))
                            }
                            _ => Err(GraphError::from(TypeError::not_a_record(
                                kctx,
                                vctx,
                                exprs.at(record_exp),
                                &record_typ,
                            ))),
                        }
                    }
                    _ => Err(GraphError::from(TypeError::not_a_record(
                        kctx,
                        vctx,
                        exprs.at(record_exp),
                        &record_typ,
                    ))),
                }
            }
            _ => {
                // For other expressions, try to infer the record type
                let record_typ = exprs.infer(record_exp, kctx, fctx, vctx)?;

                match record_typ {
                    CTyp::Record(fields) => {
                        // Get the field type
                        let _field_typ = fields.get(&field_name).ok_or_else(|| {
                            GraphError::from(TypeError::field_not_found(
                                kctx,
                                vctx,
                                exprs.at(record_exp),
                                field_name.as_str(),
                            ))
                        })?;

                        // For complex expressions, we'd need to evaluate them first
                        // For now, return an error indicating this isn't fully supported
                        Err(GraphError::from(ark_error(kctx, vctx, exprs.at(id), typ)))
                    }
                    _ => Err(GraphError::from(TypeError::not_a_record(
                        kctx,
                        vctx,
                        exprs.at(record_exp),
                        &record_typ,
                    ))),
                }
            }
        }
    }

    #[inline(never)]
    pub(super) fn lower_set_record(
        &mut self,
        step: Step<'_, C>,
        record_exp: ExpId,
        field_name: Spanned<String>,
        value_exp: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let Step {
            exprs,
            span,
            transcr,
            edge_type,
            kctx,
            fctx,
            vctx,
            vars,
            ..
        } = step;
        // The new record keeps the original record's type: every field is taken
        // from `record_exp` except `field_name`, whose value takes the field's
        // declared type (an integer stored into a field element is embedded).
        let record_typ = exprs.infer(record_exp, kctx, fctx, vctx)?;
        if !matches!(record_typ, CTyp::Record(_)) {
            return Err(GraphError::from(TypeError::not_a_record(
                kctx,
                vctx,
                exprs.at(record_exp),
                &record_typ,
            )));
        }
        let record_atyp = ATyp::from_ctyp(&record_typ, kctx)
            .ok_or_else(|| ark_error(kctx, vctx, exprs.at(record_exp), &record_typ))?;
        let ATyp::Record(field_atyps) = &record_atyp else {
            unreachable!("a record type converts to a record ATyp")
        };
        let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();
        for (fname, fatyp) in field_atyps.iter() {
            let field_exp = if *fname == field_name.node {
                value_exp
            } else {
                exprs.push(
                    CExp::Proj(record_exp, Spanned::dummy(fname.clone())),
                    span.clone(),
                )
            };
            let field_op = self.add_exp(
                exprs,
                field_exp,
                transcr,
                edge_type,
                kctx,
                fctx,
                vctx,
                vars,
                Some(fatyp.clone()),
            )?;
            field_ops.insert(fname, &mk::<C>(field_op));
        }
        Ok(self.materialize(GOp::Record(field_ops), edge_type, record_atyp, span.clone()))
    }
}
