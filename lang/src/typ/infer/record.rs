//! Records: construction, projection and field update.

use super::*;

impl CRef<'_> {
    pub(super) fn infer_record(
        self,
        fields: &Ctx<Spanned<String>, ExpId>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let mut field_types = Ctx::new();

        // Infer the type of each field
        for (field_name, field_exp) in fields.iter() {
            let field_typ = env.typ(self.at(*field_exp));
            field_types.insert(field_name, &Spanned::dummy(field_typ));
        }

        Ok(CTyp::Record(field_types))
    }

    pub(super) fn infer_proj(
        self,
        record_exp: CRef<'_>,
        field_name: &Spanned<String>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        // Infer the type of the record expression
        let record_typ = env.typ(record_exp);

        match record_typ {
            CTyp::Record(fields) => {
                // Look up the field in the record type
                fields
                    .get(field_name)
                    .map(|f| f.node.clone())
                    .ok_or_else(|| TypeError::FieldNotFound(field_name.node.clone()))
            }
            _ => Err(TypeError::NotARecord(kctx.clone(), record_typ.clone())),
        }
    }

    /// The type of field `field_name` of record `record_exp`, which a `.set` updates; checked
    /// once the record is typed, before the new value is.
    pub(super) fn record_field(
        self,
        record_exp: CRef<'_>,
        field_name: &Spanned<String>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let record_typ = env.typ(record_exp);
        let CTyp::Record(fields) = &record_typ else {
            return Err(TypeError::NotARecord(kctx.clone(), record_typ.clone()));
        };
        fields
            .get(field_name)
            .map(|f| f.node.clone())
            .ok_or_else(|| TypeError::FieldNotFound(field_name.node.clone()))
    }

    /// `record_exp.set(field_name, value_exp)`: the same record, with a value that fits the
    /// field (an integer fits `F`).
    pub(super) fn infer_set_record(
        self,
        record_exp: CRef<'_>,
        field_name: &Spanned<String>,
        value_exp: CRef<'_>,
        env: &Env<'_>,
    ) -> Result<CTyp, TypeError> {
        let Env { kctx, .. } = *env;
        let field_typ = self.record_field(record_exp, field_name, env)?;
        let value_typ = env.typ(value_exp);
        if !value_typ.fits(&field_typ, kctx) {
            return Err(TypeError::located(
                value_exp.span(),
                TypeError::FieldUpdate(
                    kctx.clone(),
                    field_name.node.clone(),
                    field_typ.clone(),
                    value_typ.clone(),
                ),
            ));
        }
        Ok(env.typ(record_exp))
    }
}
