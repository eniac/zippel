//! Records: construction, projection and field update.

use super::*;

impl CExp {
    #[inline(never)]
    pub(super) fn infer_record(
        &self,
        fields: &Ctx<Spanned<String>, Spanned<CExp>>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        let mut field_types = Ctx::new();

        // Infer the type of each field
        for (field_name, field_exp) in fields.iter() {
            let field_typ = field_exp
                .infer_with_calls(kctx, fctx, vctx, on_call)
                .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
            field_types.insert(field_name, &Spanned::dummy(field_typ));
        }

        Ok(CTyp::Record(field_types))
    }

    #[inline(never)]
    pub(super) fn infer_proj(
        &self,
        record_exp: &Spanned<CExp>,
        field_name: &Spanned<String>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        // Infer the type of the record expression
        let record_typ = record_exp
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;

        match record_typ {
            CTyp::Record(fields) => {
                // Look up the field in the record type
                fields
                    .get(field_name)
                    .map(|f| f.node.clone())
                    .ok_or_else(|| {
                        TypeError::next(
                            TypeError::exp(kctx, vctx, self),
                            TypeError::field_not_found(kctx, vctx, record_exp, &field_name.node),
                        )
                    })
            }
            _ => Err(TypeError::next(
                TypeError::exp(kctx, vctx, self),
                TypeError::not_a_record(kctx, vctx, record_exp, &record_typ),
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[inline(never)]
    pub(super) fn infer_set_record(
        &self,
        record_exp: &Spanned<CExp>,
        field_name: &Spanned<String>,
        value_exp: &Spanned<CExp>,
        kctx: &Ctx<Tid, CKind>,
        fctx: &Set<CSig>,
        vctx: &Ctx<Vid, CTyp>,
        on_call: &dyn Fn(&CSig),
    ) -> Result<CTyp, TypeError> {
        // Infer the type of the record expression (must be a record)
        let record_typ = record_exp
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
        let CTyp::Record(fields) = &record_typ else {
            return Err(TypeError::next(
                TypeError::exp(kctx, vctx, self),
                TypeError::not_a_record(kctx, vctx, record_exp, &record_typ),
            ));
        };
        // Check the field exists and the value fits its type (e.g. an integer fits F)
        let field_typ = fields.get(field_name).ok_or_else(|| {
            TypeError::next(
                TypeError::exp(kctx, vctx, self),
                TypeError::field_not_found(kctx, vctx, record_exp, &field_name.node),
            )
        })?;
        let value_typ = value_exp
            .infer_with_calls(kctx, fctx, vctx, on_call)
            .map_err(|e| TypeError::next(TypeError::exp(kctx, vctx, self), e))?;
        if !value_typ.fits(field_typ, kctx) {
            return Err(TypeError::next(
                TypeError::exp(kctx, vctx, self),
                TypeError::located(
                    &value_exp.span,
                    TypeError::field_update(
                        kctx,
                        vctx,
                        &value_exp.node,
                        &field_name.node,
                        field_typ,
                        &value_typ,
                    ),
                ),
            ));
        }
        // Result type is the same record type
        Ok(record_typ.clone())
    }
}
