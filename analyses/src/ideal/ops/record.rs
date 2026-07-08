//! Record and projection op encoders: `record_op`, `proj_op`.

use backend::op::HasOpFactory;
use backend::{ATyp, ArkConfig};
use graph::HOp;
use share::Ctx;

use crate::Var;
use crate::frontend::Polynomial;

use super::EncodeCtx;
use super::PolySource;
use super::link_to_polys;

/// Compute the slot offset of `field_name` within a record type.
fn record_field_offset(fields: &Ctx<String, ATyp>, field_name: &str) -> usize {
    let mut offset = 0;
    for (fname, ftyp) in fields.iter() {
        if fname == field_name {
            return offset;
        }
        offset += ftyp.physical_len();
    }
    panic!(
        "ideal: record_field_offset: field '{}' not found in record fields {:?}",
        field_name,
        fields.iter().map(|(k, _)| k).collect::<Vec<_>>()
    )
}

/// Encode `Op::Record(fields)`: field-slot-aware layout.
/// For each field, get the field-level Var via `with_index`,
/// then expand its sub-slots via `slots()` to get hierarchical
/// indices (e.g. `[0][0]`, `[0][1]` for a Vec field).
pub fn record_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    fields: &Ctx<String, HOp<C>>,
) {
    for (field_idx, (_, field_op)) in fields.iter().enumerate() {
        let field_var = var
            .clone()
            .with_index(field_idx)
            .expect("record field index must be within record logical layout");
        let field_polys = PolySource::ref_vars(field_op.get(), &ctx.ideal.vars);
        link_to_polys(ctx.ideal, &field_var, field_polys);
    }
}

/// Encode `Op::Proj(inner, field, typ)`: extract a field from a Record.
/// The field's physical slots sit at an offset within the Record's
/// slot layout: offset = sum of physical_len() of preceding fields
/// (in Ctx iteration order). Emit basis rows linking proj ideal
/// slots to the corresponding inner Record slots.
///
/// Non-record inner types are not supported — after IR lowering every
/// Proj must operate on a Record; any other variant is a compiler bug.
pub fn proj_op<C: ArkConfig + HasOpFactory>(
    ctx: &mut EncodeCtx<'_, C>,
    var: &Var,
    inner: &HOp<C>,
    field: &str,
) {
    let inner_typ = inner.typ();
    let inner_polys = PolySource::ref_vars(inner, &ctx.ideal.vars);
    match &inner_typ {
        ATyp::Record(fields) => {
            let offset = record_field_offset(fields, field);
            let n_slots = var.slots().len();
            let polys: Vec<Polynomial<C::F>> = (0..n_slots)
                .map(|j| inner_polys[offset + j].clone())
                .collect();
            link_to_polys(ctx.ideal, var, polys);
        }
        _ => {
            panic!(
                "ideal: Proj: non-record inner type {:?} for field '{}'; \
                 all Proj ops must operate on Record types after IR lowering",
                inner_typ, field
            );
        }
    }
}

#[cfg(test)]
mod tests {

    use super::super::{Ideal, IdealBuilder};

    use backend::ArkBls12_381;

    use backend::ATyp;
    use backend::op::mk;
    use graph::{GOp, HOp, Op};

    use share::Ctx;

    #[test]
    fn test_record_scalar_fields_bind_slots() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        // Ctx iterates in key order (alphabetical): "x" < "y"
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"y".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let var_a = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Public);
        ideal.register(&var_a);
        let var_b = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Public);
        ideal.register(&var_b);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"y".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
        );

        let var_r = Var::from_node(NodeIndex::new(2), rec_typ, Qualifier::Public);
        ideal.register(&var_r);

        builder.add_op(var_r.clone(), Op::Record(fields), &mut ideal);

        // Ctx iteration order: "x" (slot 0), "y" (slot 1)
        let slot_x = var_r.clone().with_index(0).unwrap();
        let slot_y = var_r.clone().with_index(1).unwrap();

        assert!(
            ideal.pl.contains(&slot_x),
            "record slot 0 (x) missing from pl"
        );
        assert!(
            ideal.pl.contains(&slot_y),
            "record slot 1 (y) missing from pl"
        );

        let poly_x = ideal.pl.get(&slot_x).unwrap();
        let poly_y = ideal.pl.get(&slot_y).unwrap();
        assert!(
            poly_x.contains(&var_a),
            "slot 0 poly should reference field x"
        );
        assert!(
            poly_y.contains(&var_b),
            "slot 1 poly should reference field y"
        );
    }

    #[test]
    fn test_record_mixed_type_fields_bind_slots() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let uni_typ = ATyp::Uni(2);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"p".to_string(), &uni_typ);
        let rec_typ = ATyp::Record(rec_fields);

        let var_scalar = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Public);
        ideal.register(&var_scalar);

        let var_poly = Var::from_node(NodeIndex::new(1), uni_typ.clone(), Qualifier::Public);
        ideal.register(&var_poly);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"a".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"p".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), uni_typ.clone())),
        );

        let var_r = Var::from_node(NodeIndex::new(2), rec_typ, Qualifier::Public);
        ideal.register(&var_r);

        builder.add_op(var_r.clone(), Op::Record(fields), &mut ideal);

        assert_eq!(
            var_r.typ.physical_len(),
            4,
            "1 scalar + 3 Uni(2) coeffs = 4"
        );

        let slot_a = var_r.clone().with_index(0).unwrap();
        assert_eq!(slot_a.typ, s, "field 0 (a) should be scalar");
        assert!(
            ideal.pl.contains(&slot_a),
            "record field 0 (a) missing from pl"
        );

        let slot_p = var_r.clone().with_index(1).unwrap();
        assert_eq!(slot_p.typ, uni_typ, "field 1 (p) should be Uni(2)");
        let p_slots = slot_p.slots();
        assert_eq!(p_slots.len(), 3, "Uni(2) has 3 scalar slots");
        for (i, slot_pi) in p_slots.iter().enumerate() {
            assert_eq!(slot_pi.typ, s, "p slot {} should be scalar", i);
            assert!(
                ideal.pl.contains(slot_pi),
                "record field 1 (p) sub-slot {} missing from pl",
                i
            );
        }
    }

    #[test]
    fn test_record_basis_count_matches_physical_len() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let v2 = ATyp::Vec(Box::new(s.clone()), 3);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"v".to_string(), &v2);
        let rec_typ = ATyp::Record(rec_fields);
        let phys_len = rec_typ.physical_len();
        assert_eq!(phys_len, 4, "1 scalar + 3 Vec scalars = 4");

        let var_x = Var::from_node(NodeIndex::new(0), s.clone(), Qualifier::Public);
        ideal.register(&var_x);

        let var_v = Var::from_node(NodeIndex::new(1), v2.clone(), Qualifier::Public);
        ideal.register(&var_v);

        let mut fields = Ctx::<String, HOp<ArkBls12_381>>::new();
        fields.insert(
            &"x".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(0)), s.clone())),
        );
        fields.insert(
            &"v".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), v2.clone())),
        );

        let var_r = Var::from_node(NodeIndex::new(2), rec_typ, Qualifier::Public);
        ideal.register(&var_r);

        builder.add_op(var_r.clone(), Op::Record(fields), &mut ideal);

        assert_eq!(
            ideal.generating_set.len(),
            phys_len,
            "basis should have one row per physical slot"
        );
    }

    #[test]
    fn test_proj_scalar_field_from_record() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        // Alphabetical: "x" < "y", so "x" is slot 0, "y" is slot 1
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"x".to_string(), &s);
        rec_fields.insert(&"y".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let var_rec = Var::from_node(NodeIndex::new(0), rec_typ.clone(), Qualifier::Public);
        ideal.register(&var_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let var_proj = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Public);
        ideal.register(&var_proj);

        builder.add_op(
            var_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "x".to_string(), s.clone()),
            &mut ideal,
        );

        assert!(ideal.pl.contains(&var_proj), "proj ideal missing from pl");

        let proj_poly = ideal.pl.get(&var_proj).unwrap();
        let slot_0 = var_rec.clone().with_index(0).unwrap();
        assert!(
            proj_poly.contains(&slot_0),
            "proj poly should reference record slot 0 (field x)"
        );
    }

    #[test]
    fn test_proj_second_field_offset_correct() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        // Use "a" and "b" so alphabetical order is "a" then "b"
        // "a" : Scalar (1 slot at offset 0)
        // "b" : Vec<Scalar,3> (3 slots at offset 1)
        let v3 = ATyp::Vec(Box::new(s.clone()), 3);
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"b".to_string(), &v3);
        let rec_typ = ATyp::Record(rec_fields);

        let var_rec = Var::from_node(NodeIndex::new(0), rec_typ.clone(), Qualifier::Public);
        ideal.register(&var_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let var_proj = Var::from_node(NodeIndex::new(1), v3.clone(), Qualifier::Public);
        ideal.register(&var_proj);

        builder.add_op(
            var_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "b".to_string(), v3.clone()),
            &mut ideal,
        );

        assert_eq!(var_proj.typ.physical_len(), 3, "Vec<F, 3> has 3 slots");
        let proj_slots = var_proj.slots();
        let rec_slots = var_rec.slots();
        for i in 0..3 {
            let proj_slot = &proj_slots[i];
            assert!(
                ideal.pl.contains(proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = ideal.pl.get(proj_slot).unwrap();
            let rec_slot = &rec_slots[1 + i];
            assert!(
                proj_poly.contains(rec_slot),
                "proj slot {} poly should reference record slot {} (field b at offset 1)",
                i,
                1 + i
            );
        }
    }

    #[test]
    fn test_proj_first_field_of_multi_field_record() {
        use crate::Var;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();
        let uni2 = ATyp::Uni(2);
        // "a" < "b" alphabetically
        // "a": Uni(2) → 3 slots at offset 0
        // "b": Scalar → 1 slot at offset 3
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &uni2);
        rec_fields.insert(&"b".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        let var_rec = Var::from_node(NodeIndex::new(0), rec_typ.clone(), Qualifier::Public);
        ideal.register(&var_rec);

        let inner_op: GOp<ArkBls12_381> = Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ);

        let var_proj = Var::from_node(NodeIndex::new(1), uni2.clone(), Qualifier::Public);
        ideal.register(&var_proj);

        builder.add_op(
            var_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "a".to_string(), uni2.clone()),
            &mut ideal,
        );

        assert_eq!(var_proj.typ.physical_len(), 3, "Uni(2) has 3 coefficients");
        let proj_slots = var_proj.slots();
        let rec_slots = var_rec.slots();
        for i in 0..3 {
            let proj_slot = &proj_slots[i];
            assert!(
                ideal.pl.contains(proj_slot),
                "proj slot {} missing from pl",
                i
            );

            let proj_poly = ideal.pl.get(proj_slot).unwrap();
            let rec_slot = &rec_slots[i];
            assert!(
                proj_poly.contains(rec_slot),
                "proj slot {} poly should reference record slot {} (field a at offset 0)",
                i,
                i
            );
        }
    }

    #[test]
    fn record_projection_resolves_without_np_lookup() {
        // Build a record {a: Scalar, b: Scalar} from scalar refs, project
        // field "a", assert pl/basis aliases the field directly.
        use crate::Var;
        use backend::op::mk;
        use lang::typ::Qualifier;
        use petgraph::graph::NodeIndex;

        let mut builder = IdealBuilder::<ArkBls12_381>::new();
        let mut ideal = Ideal::<ArkBls12_381>::new();

        let s = ATyp::scalar();

        // Build record {a: Scalar, b: Scalar}.
        // Alphabetical order: "a" at offset 0, "b" at offset 1.
        let mut rec_fields = Ctx::<String, ATyp>::new();
        rec_fields.insert(&"a".to_string(), &s);
        rec_fields.insert(&"b".to_string(), &s);
        let rec_typ = ATyp::Record(rec_fields);

        // Register the record Var.
        let var_rec = Var::from_node(NodeIndex::new(0), rec_typ.clone(), Qualifier::Public);
        ideal.register(&var_rec);

        // Register scalar refs for a and b.
        let var_a = Var::from_node(NodeIndex::new(1), s.clone(), Qualifier::Public);
        let var_b = Var::from_node(NodeIndex::new(2), s.clone(), Qualifier::Public);
        ideal.register(&var_a);
        ideal.register(&var_b);

        // Build record {a: var_a, b: var_b}.
        let mut field_ops: Ctx<String, backend::op::HOp<ArkBls12_381>> = Ctx::new();
        field_ops.insert(
            &"a".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(1)), s.clone())),
        );
        field_ops.insert(
            &"b".to_string(),
            &mk::<ArkBls12_381>(Op::Ref(graph::Ref::new(NodeIndex::new(2)), s.clone())),
        );

        builder.add_op(var_rec.clone(), Op::Record(field_ops), &mut ideal);

        // Project field "a" from the record.
        let var_proj = Var::from_node(NodeIndex::new(3), s.clone(), Qualifier::Public);
        ideal.register(&var_proj);

        let inner_op: GOp<ArkBls12_381> =
            Op::Ref(graph::Ref::new(NodeIndex::new(0)), rec_typ.clone());

        builder.add_op(
            var_proj.clone(),
            Op::Proj(mk::<ArkBls12_381>(inner_op), "a".to_string(), s.clone()),
            &mut ideal,
        );

        // Projection ideal should be in pl.
        assert!(ideal.pl.contains(&var_proj), "proj ideal should be in pl");

        // The proj poly should reference record slot 0 (field "a").
        let proj_poly = ideal.pl.get(&var_proj).unwrap();
        let rec_slot_0 = var_rec.clone().with_index(0).unwrap();
        assert!(
            proj_poly.contains(&rec_slot_0),
            "proj ideal should alias record slot 0 (field 'a')"
        );
    }
}
