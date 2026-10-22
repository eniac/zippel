//! Records: construction, projection and field update.

use super::*;

impl<C: HasOpFactory> UDag<C> {
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

    /// `record.field`. The record is lowered whole, so every field's effects happen once, and the
    /// field is taken from its operation ([`Self::field_of`]). A record literal's fields are
    /// lowered without building the record, which nothing else would read.
    pub(super) fn lower_proj(
        &mut self,
        scope: &mut Scope<'_, C>,
        id: ExpId,
        record_exp: ExpId,
        field_name: Spanned<String>,
    ) -> Result<GOp<C>, GraphError> {
        let span = scope.exprs.span(id).clone();
        if let CExp::Record(fields) = scope.exprs[record_exp].clone() {
            let mut field = None;
            for (name, exp) in fields.iter() {
                let op = self.add_exp(scope, *exp, None)?;
                if *name == field_name {
                    field = Some(op);
                }
            }
            return field.ok_or_else(|| {
                GraphError::from(TypeError::FieldNotFound((field_name.as_str()).to_string()))
            });
        }
        let record_typ = scope.infer(record_exp)?;
        let CTyp::Record(fields) = &record_typ else {
            return Err(GraphError::from(TypeError::NotARecord(
                (scope.kctx).clone(),
                record_typ.clone(),
            )));
        };
        let field_typ = fields.get(&field_name).ok_or_else(|| {
            GraphError::from(TypeError::FieldNotFound((field_name.as_str()).to_string()))
        })?;
        let field_atyp = ATyp::from_ctyp(field_typ, scope.kctx).ok_or_else(|| {
            GraphError::from(TypeError::located(
                scope.exprs.span(id),
                TypeError::Ark((scope.kctx).clone(), field_typ.node.clone()),
            ))
        })?;
        let record_op = self.add_exp(scope, record_exp, None)?;
        self.field_of(
            scope,
            &record_op,
            &record_typ,
            &field_name,
            field_atyp,
            span,
        )
    }

    /// The field `field_name`, of type `field_atyp`, of `record_op`, a lowered record of type
    /// `record_typ`: read straight from a record operation or node, a typed reference for an
    /// argument, else a new `Proj` node.
    fn field_of(
        &mut self,
        scope: &Scope<'_, C>,
        record_op: &GOp<C>,
        record_typ: &CTyp,
        field_name: &Spanned<String>,
        field_atyp: ATyp,
        span: std::ops::Range<usize>,
    ) -> Result<GOp<C>, GraphError> {
        let not_found =
            || GraphError::from(TypeError::FieldNotFound((field_name.as_str()).to_string()));
        match record_op {
            Op::Record(record_fields) => record_fields
                .get(field_name)
                .map(|op| (**op).clone())
                .ok_or_else(not_found),
            Op::Ref(r, _) => {
                // A node that stores a record: take the field directly (no `Proj` node).
                if let Some(inner) = self[r.node()].op()
                    && let Op::Record(fields) = inner.get()
                {
                    return fields
                        .get(field_name)
                        .map(|op| op.get().clone())
                        .ok_or_else(not_found);
                }
                // An argument: the field is selected directly off the typed reference.
                if self[r.node()].is_arg() {
                    return Ok(Op::Ref(Ref(r.node()), field_atyp));
                }
                let proj_node = self.add_node(Node::proj(record_op, field_name, &field_atyp), span);
                self.add_edges(scope.edge_type, proj_node, record_op.clone());
                Ok(Op::Ref(Ref(proj_node), field_atyp))
            }
            _ => Err(GraphError::from(TypeError::NotARecord(
                (scope.kctx).clone(),
                record_typ.clone(),
            ))),
        }
    }

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
        // The record is lowered once; every field but the updated one is taken from it.
        let record_op = self.add_exp(scope, record_exp, None)?;
        let mut field_ops: Ctx<String, HOp<C>> = Ctx::new();
        for (fname, fatyp) in field_atyps.iter() {
            let field_op = if *fname == field_name.node {
                self.add_exp(scope, value_exp, Some(fatyp.clone()))?
            } else {
                let name = Spanned::new(fname.clone(), span.clone());
                let op = self.field_of(
                    scope,
                    &record_op,
                    &record_typ,
                    &name,
                    fatyp.clone(),
                    span.clone(),
                )?;
                self.coerce(op, fatyp, scope.edge_type, span.clone())
            };
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
