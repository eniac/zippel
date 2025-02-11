pub trait Proj1<A> {
    type Output<B>;
    fn get_proj1(&self) -> &A;
    fn map_proj1<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z>;
    fn modify_proj1(&mut self, f: &mut dyn FnMut(&mut A));
}

pub trait Proj2<A> {
    type Output<B>;
    fn get_proj2(&self) -> &A;
    fn map_proj2<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z>;
    fn modify_proj2(&mut self, f: &mut dyn FnMut(&mut A));
}

impl<A, B> Proj1<A> for (A, B) {
    type Output<Z> = (Z, B);
    fn get_proj1(&self) -> &A {
        &self.0
    }
    fn map_proj1<Z>(self, f: &mut dyn FnMut(A) -> Z) -> Self::Output<Z> {
        (f(self.0), self.1)
    }
    fn modify_proj1(&mut self, f: &mut dyn FnMut(&mut A)) {
        f(&mut self.0)
    }
}

impl<A, B> Proj2<B> for (A, B) {
    type Output<Z> = (A, Z);
    fn get_proj2(&self) -> &B {
        &self.1
    }
    fn map_proj2<Z>(self, f: &mut dyn FnMut(B) -> Z) -> Self::Output<Z> {
        (self.0, f(self.1))
    }
    fn modify_proj2(&mut self, f: &mut dyn FnMut(&mut B)) {
        f(&mut self.1);
    }
}

#[test]
fn pair_proj1() {
    let mut pair = (1, 2);
    assert_eq!(pair.get_proj1(), &1);
    assert_eq!(pair.map_proj1(&mut |x| x + 1), (2, 2));

    pair.modify_proj1(&mut |x| x + 2);
    assert_eq!(pair.get_proj1(), &3);
}

#[test]
fn pair_proj2() {
    let mut pair = (1, 2);
    assert_eq!(pair.get_proj2(), &2);
    assert_eq!(pair.map_proj2(&mut |x| x + 1), (1, 3));

    pair.modify_proj2(&mut |x| x + 2);
    assert_eq!(pair.get_proj2(), &4);
}



