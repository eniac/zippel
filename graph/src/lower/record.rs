//! Records: construction, projection and field update.

use super::*;

impl<C: HasOpFactory> UDag<C> {
    #[inline(never)]
    pub(super) fn lower_record(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        fields: Ctx<Spanned<String>, ExpId>,
        expected: Option<&ATyp>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        let atyp = ATyp::from_ctyp(&typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(id), &typ))?;
        // Fields take the expected field types, else the record's own.
        let ATyp::Record(targets) = expected.unwrap_or(&atyp).clone() else {
            unreachable!("a record expression has a record type")
        };
        let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();

        for (field_name, field_exp) in fields.iter() {
            let field_op =
                self.add_exp(scope, *field_exp, targets.get(&field_name.node).cloned())?;
            let hop = mk::<C>(field_op);
            field_ops.insert(field_name, &hop);
        }

        let record_op = GOp::Record(field_ops);
        let atyp = if expected.is_some() {
            record_op.typ()
        } else {
            atyp
        };
        Ok(self.materialize(record_op, scope.edge_type, atyp, span.clone()))
    }

    #[inline(never)]
    pub(super) fn lower_proj(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        record_exp: ExpId,
        field_name: Spanned<String>,
    ) -> Result<GOp<C>, GraphError> {
        let typ = scope.infer(id)?;
        let span = scope.exprs.span(id).clone();
        // For projection, we need to extract the field from the record
        // Check if the record expression is a Record literal
        match scope.exprs[record_exp].clone() {
            CExp::Record(fields) => {
                let field_exp = fields.get(&field_name).ok_or_else(|| {
                    GraphError::from(TypeError::FieldNotFound((field_name.as_str()).to_string()))
                })?;

                // Add the field expression to the graph
                self.add_exp(scope, *field_exp, None)
            }
            CExp::Var(var) => {
                let id_clone = var.clone();
                let record_op = scope
                    .vars
                    .get(&id_clone)
                    .ok_or_else(|| GraphError::from(TypeError::IllTyped))?;

                // Try to infer the record type to verify the field exists
                let record_typ = scope.exprs.infer(record_exp, scope.kctx, &scope.vctx)?;

                match &record_typ {
                    CTyp::Record(fields) => {
                        // Verify the field exists and get its type
                        let field_typ_ctyp = fields.get(&field_name).ok_or_else(|| {
                            GraphError::from(TypeError::FieldNotFound(
                                (field_name.as_str()).to_string(),
                            ))
                        })?;

                        // Extract the field from the record operation
                        match record_op {
                            Op::Record(record_fields) => {
                                // Direct field access from Record operation
                                record_fields
                                    .get(&field_name)
                                    .ok_or_else(|| {
                                        GraphError::from(TypeError::FieldNotFound(
                                            (field_name.as_str()).to_string(),
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
                                let field_typ_atyp = ATyp::from_ctyp(field_typ_ctyp, scope.kctx)
                                    .ok_or_else(|| {
                                        GraphError::from(TypeError::located(
                                            scope.exprs.span(id),
                                            TypeError::Ark(
                                                (scope.kctx).clone(),
                                                field_typ_ctyp.node.clone(),
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
                                self.add_edges(scope.edge_type, proj_node, record_op.clone());
                                Ok(Op::Ref(Ref(proj_node), field_typ_atyp))
                            }
                            _ => Err(GraphError::from(TypeError::NotARecord(
                                (scope.kctx).clone(),
                                record_typ.clone(),
                            ))),
                        }
                    }
                    _ => Err(GraphError::from(TypeError::NotARecord(
                        (scope.kctx).clone(),
                        record_typ.clone(),
                    ))),
                }
            }
            _ => {
                // For other expressions, try to infer the record type
                let record_typ = scope.infer(record_exp)?;

                match record_typ {
                    CTyp::Record(fields) => {
                        // Get the field type
                        let _field_typ = fields.get(&field_name).ok_or_else(|| {
                            GraphError::from(TypeError::FieldNotFound(
                                (field_name.as_str()).to_string(),
                            ))
                        })?;

                        // For complex expressions, we'd need to evaluate them first
                        // For now, return an error indicating this isn't fully supported
                        Err(GraphError::from(ark_error(
                            scope.kctx,
                            scope.exprs.at(id),
                            &typ,
                        )))
                    }
                    _ => Err(GraphError::from(TypeError::NotARecord(
                        (scope.kctx).clone(),
                        record_typ.clone(),
                    ))),
                }
            }
        }
    }

    #[inline(never)]
    pub(super) fn lower_set_record(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        record_exp: ExpId,
        field_name: Spanned<String>,
        value_exp: ExpId,
    ) -> Result<GOp<C>, GraphError> {
        let span = scope.exprs.span(id).clone();
        // The new record keeps the original record's type: every field is taken
        // from `record_exp` except `field_name`, whose value takes the field's
        // declared type (an integer stored into a field element is embedded).
        let record_typ = scope.infer(record_exp)?;
        if !matches!(record_typ, CTyp::Record(_)) {
            return Err(GraphError::from(TypeError::NotARecord(
                (scope.kctx).clone(),
                record_typ.clone(),
            )));
        }
        let record_atyp = ATyp::from_ctyp(&record_typ, scope.kctx)
            .ok_or_else(|| ark_error(scope.kctx, scope.exprs.at(record_exp), &record_typ))?;
        let ATyp::Record(field_atyps) = &record_atyp else {
            unreachable!("a record type converts to a record ATyp")
        };
        let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();
        for (fname, fatyp) in field_atyps.iter() {
            let field_exp = if *fname == field_name.node {
                value_exp
            } else {
                scope.exprs.push(
                    CExp::Proj(record_exp, Spanned::dummy(fname.clone())),
                    span.clone(),
                )
            };
            let field_op = self.add_exp(scope, field_exp, Some(fatyp.clone()))?;
            field_ops.insert(fname, &mk::<C>(field_op));
        }
        Ok(self.materialize(
            GOp::Record(field_ops),
            scope.edge_type,
            record_atyp,
            span.clone(),
        ))
    }
}
