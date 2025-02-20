pub trait Proj1<A, B> {
    fn proj1(self) -> A;
}

pub trait Proj2<A, B> {
    fn proj2(self) -> B;
}

impl<A, B> Proj1<A, B> for (A, B) {
    fn proj1(self) -> A {
        self.0
    }
}

impl<A, B> Proj2<A, B> for (A, B) {
    fn proj2(self) -> B {
        self.1
    }
}

#[test]
fn test_proj() {
    let x = (1, 2);
    assert_eq!(x.proj1(), 1);
    assert_eq!(x.proj2(), 2);
}


