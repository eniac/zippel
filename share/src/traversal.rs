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

/// Acess the traversal for free type parameters (1, 2, 3)
pub trait ToTraversal1<A>: Sized {
    type Output<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E>;
    fn map1<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z> {
        self.traverse1::<Z, ()>(&mut |x| Ok(f(x))).unwrap()
    }
}
pub trait ToTraversal2<A>: Sized {
    type Output<Z>;
    fn traverse2<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E>;
    fn map2<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z> {
        self.traverse2::<Z, ()>(&mut |x| Ok(f(x))).unwrap()
    }
}
pub trait ToTraversal3<A> {
    type Output<Z>;
    fn traverse3<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E>;
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

impl<A> ToTraversal1<A> for Vec<A> {
    type Output<Z> = Vec<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        VecTraversal::traverse(self, f)
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

impl<A> ToTraversal1<A> for Option<A> {
    type Output<Z> = Option<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        OptionTraversal::traverse(self, f)
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

impl<A> ToTraversal1<A> for Box<A> {
    type Output<Z> = Box<Z>;
    fn traverse1<Z, E>(self, f: &mut dyn FnMut(A) -> Result<Z, E>) -> Result<Self::Output<Z>, E> {
        BoxTraversal::traverse(self, f)
    }
}

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

#[cfg(test)]
mod additional_tests {
    use super::*;

    #[test]
    fn test_vec2_traversal2_success() {
        let v = vec![('a', 1), ('b', 2), ('c', 3)];
        let result: Result<Vec<(char, i32)>, ()> = Vec2Traversal2::traverse(v, &mut |x| Ok(x * 2));
        assert_eq!(result, Ok(vec![('a', 2), ('b', 4), ('c', 6)]));
    }

    #[test]
    fn test_vec2_traversal2_error() {
        let v = vec![('a', 1), ('b', 2), ('c', 3)];
        let result = Vec2Traversal2::traverse(v, &mut |x| {
            if x > 1 {
                Err("Too large")
            } else {
                Ok(x)
            }
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_vec2_traversal2_empty() {
        let v: Vec<(char, i32)> = vec![];
        let result: Result<Vec<(char, i32)>, ()> = Vec2Traversal2::traverse(v, &mut |x| Ok(x + 1));
        assert_eq!(result, Ok(vec![]));
    }

    #[test]
    fn test_box_traversal_success() {
        let b = Box::new(42);
        let result: Result<Box<i32>, ()> = BoxTraversal::traverse(b, &mut |x| Ok(x * 2));
        assert_eq!(result, Ok(Box::new(84)));
    }

    #[test]
    fn test_box_traversal_error() {
        let b = Box::new(42);
        let result: Result<Box<i32>, &str> = BoxTraversal::traverse(b, &mut |_| Err("Error"));
        assert!(result.is_err());
    }

    #[test]
    fn test_box_traversal1() {
        let b = Box::new(10);
        let result: Result<Box<i32>, ()> = b.traverse1(&mut |x| Ok(x + 5));
        assert_eq!(result, Ok(Box::new(15)));
    }

    #[test]
    fn test_vec_map1() {
        let v = vec![1, 2, 3];
        let result = v.map1(&mut |x| x * 2);
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_vec_map1_empty() {
        let v: Vec<i32> = vec![];
        let result = v.map1(&mut |x| x * 2);
        assert_eq!(result, Vec::<i32>::new());
    }

    #[test]
    fn test_option_map1_some() {
        let o = Some(42);
        let result = o.map1(&mut |x| x * 2);
        assert_eq!(result, Some(84));
    }

    #[test]
    fn test_option_map1_none() {
        let o: Option<i32> = None;
        let result = o.map1(&mut |x| x * 2);
        assert_eq!(result, None);
    }

    #[test]
    fn test_box_map1() {
        let b = Box::new(7);
        let result = b.map1(&mut |x| x + 3);
        assert_eq!(result, Box::new(10));
    }

    #[test]
    fn test_vec_traversal_with_capacity() {
        let v = vec![1, 2, 3, 4, 5];
        let result: Result<Vec<i32>, ()> = VecTraversal::traverse(v, &mut |x| Ok(x * 3));
        assert_eq!(result, Ok(vec![3, 6, 9, 12, 15]));
    }

    #[test]
    fn test_option_traversal_some() {
        let o = Some(100);
        let result: Result<Option<i32>, ()> = OptionTraversal::traverse(o, &mut |x| Ok(x / 10));
        assert_eq!(result, Ok(Some(10)));
    }
}
