#![allow(refining_impl_trait)]
use crate::context::Ctx;

/// Traverse a structure on the 1st type argument and apply a function
pub trait Traversable1<A>: Sized {
    type Output<Z>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E>
    where
        Self::Output<Z>: Traversable1<Z>;

    /// Derived function [map1]; traverse1 with no errors
    fn map1<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z>
    where
        Self::Output<Z>: Traversable1<Z> {
        Self::traverse1::<Z, ()>(self, &mut |a| Ok(f(a))).unwrap()
    }
}

/// Traverse a structure on the 2nd type argument and apply a function
pub trait Traversable2<B>: Sized {
    type Output<Z>;

    fn traverse2<Z, E>(self, f: &mut dyn FnMut(B) -> Result<Z, E>) -> Result<Self::Output<Z>, E>
    where
        Self::Output<Z>: Traversable2<Z>;

    /// Derived function [map2]; traverse2 with no errors
    fn map2<Z>(self, f: &mut dyn FnMut(B) -> Z) -> Self::Output<Z>
    where
        Self::Output<Z>: Traversable2<Z> {
        Self::traverse2::<Z, ()>(self, &mut |a| Ok(f(a))).unwrap()
    }
}

/// [Box] is a [Traversable1]
impl<A> Traversable1<A> for Box<A> {
    type Output<Z> = Box<Z>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Box<Z>, E> {
        Ok(Box::new(f(*self)?))
    }
}

/// [Vec] is a [Traversable1]
impl<A> Traversable1<A> for Vec<A> {
    type Output<Z> = Vec<Z>;

    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Vec<Z>, E> {
        let mut v = Vec::with_capacity(self.len());
        for x in self.into_iter() {
            v.push(f(x)?);
        }
        Ok(v)
    }
}

/// [Ctx] is a [Traversable2]
impl<A: Ord, B> Traversable2<B> for Ctx<A, B> {
    type Output<Z> = Ctx<A, Z>;
    fn traverse2<Z, E>(
        self,
        f: &mut dyn FnMut(B) -> Result<Z, E>,
    ) -> Result<Ctx<A, Z>, E> {
        let mut m = Ctx::new();
        for (k, v) in self.into_iter() {
            m.insert(k, f(v)?);
        }
        Ok(m)
    }
}

/// Testing traversable instances
mod test {
    use super::*;

    #[derive(Debug, PartialEq, Clone)]
    struct Vec3<A, B, C>(Vec<(A, B, C)>);

    /// [Vec3] is a [Traversable1]
    impl<A, B, C> Traversable1<A> for Vec3<A, B, C> {
        type Output<Z> = Vec3<Z, B, C>;

        fn traverse1<Z, E>(
            self,
            f: &mut dyn FnMut(A) -> Result<Z, E>,
        ) -> Result<Vec3<Z, B, C>, E> {
            let mut v = Vec::with_capacity(self.0.len());
            for (a, b, c) in self.0.into_iter() {
                v.push((f(a)?, b, c));
            }
            Ok(Vec3(v))
        }
    }

    /// [Vec3] is a [Traversable2]
    impl<A, B, C> Traversable2<B> for Vec3<A, B, C> {
        type Output<Z> = Vec3<A, Z, C>;

        fn traverse2<Z, E>(
            self,
            f: &mut dyn FnMut(B) -> Result<Z, E>,
        ) -> Result<Vec3<A, Z, C>, E> {
            let mut v = Vec::with_capacity(self.0.len());
            for (a, b, c) in self.0.into_iter() {
                v.push((a, f(b)?, c));
            }
            Ok(Vec3(v))
        }
    }

    #[test]
    fn test_traverse1_good() {
        let v = Vec3(vec![(0, 'a', true), (2, 'b', false)]);
        let v2 = v.clone().traverse1(&mut |a| {
            if a % 2 == 0 {
                Ok(a)
            } else {
                Err("Only expected even numbers")
            }
        });
        assert_eq!(v2, Ok(v));
    }

    #[test]
    fn test_traverse1_bad() {
        let v = Vec3(vec![(1, 'a', true), (2, 'b', false)]);
        let v2 = v.traverse1(&mut |a| {
            if a % 2 == 0 {
                Ok(a)
            } else {
                Err("Only expected even numbers")
            }
        });
        assert!(v2.is_err())
    }

    #[test]
    fn test_traverse2() {
        let v = Vec3(vec![(1, true, true), (2, true, false)]);
        let mut cnt = 0;
        let v2 = v.traverse2(&mut |b: bool| {
            if b {
                cnt += 1;
                Ok(b)
            } else {
                Err("Only expected [true]")
            }
        });
        assert_eq!(v2, Ok(Vec3(vec![(1, true, true), (2, true, false)])));
        assert_eq!(cnt, 2);
    }
}
