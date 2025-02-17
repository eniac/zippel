#![allow(refining_impl_trait)]

/// Define traversals as a relation between a structure and a
/// subfield of that structure. Maybe this is more akin to lenses.
pub trait Traversal<A, B=A> {
    type Domain;
    type Codomain;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E>;
}

/// How to traverse vectors
pub struct VecTraversal<A>(std::marker::PhantomData<A>);
impl<A, B> Traversal<A, B> for VecTraversal<A> {
    type Domain = Vec<A>;
    type Codomain = Vec<B>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        let mut v = Vec::with_capacity(on.len());
        for x in on.into_iter() {
            v.push(f(x)?);
        }
        Ok(v)
    }
}

/// How to traverse vector of pairs
pub struct Vec2Traversal1<A>(std::marker::PhantomData<A>);
impl<A, B, C> Traversal<A, B> for Vec2Traversal1<(A, C)> {
    type Domain = Vec<(A, C)>;
    type Codomain = Vec<(B, C)>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        let mut v = Vec::with_capacity(on.len());
        for (x, y) in on.into_iter() {
            v.push((f(x)?, y));
        }
        Ok(v)
    }
}

pub struct Vec2Traversal2<A>(std::marker::PhantomData<A>);
impl<A, B, C> Traversal<B, C> for Vec2Traversal2<(A, B)> {
    type Domain = Vec<(A, B)>;
    type Codomain = Vec<(A, C)>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(B) -> Result<C, E>,
    ) -> Result<Self::Codomain, E> {
        let mut v = Vec::with_capacity(on.len());
        for (x, y) in on.into_iter() {
            v.push((x, f(y)?));
        }
        Ok(v)
    }
}
/// How to traverse options
pub struct OptionTraversal<A>(std::marker::PhantomData<A>);
impl<A, B> Traversal<A, B> for OptionTraversal<A> {
    type Domain = Option<A>;
    type Codomain = Option<B>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        match on {
            Some(x) => Ok(Some(f(x)?)),
            None => Ok(None),
        }
    }
}

/// How to traverse Boxes
pub struct BoxTraversal<A>(std::marker::PhantomData<A>);
impl<A, B> Traversal<A, B> for BoxTraversal<A> {
    type Domain = Box<A>;
    type Codomain = Box<B>;
    fn traverse<E>(
        on: Self::Domain,
        f: &mut dyn FnMut(A) -> Result<B, E>,
    ) -> Result<Self::Codomain, E> {
        Ok(Box::new(f(*on)?))
    }
}

/// Testing traversal instances
mod test {
    use super::*;

    #[test]
    fn test_traversal_good() {
        let v = vec![(0, 'a'), (2, 'b')];
        let v2 = Vec2Traversal1::traverse(v.clone(), &mut |a| {
            if a % 2 == 0 {
                Ok(a)
            } else {
                Err("Only expected even numbers")
            }
        });
        assert_eq!(v2, Ok(v));
    }

    #[test]
    fn test_traversal_bad() {
        let v = vec![(1, 'a'), (2, 'b')];
        let v2 = Vec2Traversal1::traverse(v.clone(), &mut |a| {
            if a % 2 == 0 {
                Ok(a)
            } else {
                Err("Only expected even numbers")
            }
        });
        assert!(v2.is_err())
    }

    #[test]
    fn test_traversal_option() {
        let v : Option<usize> = None;
        assert_eq!(OptionTraversal::traverse::<()>(v, &mut |a| Ok(a)), Ok(None));
    }
}
