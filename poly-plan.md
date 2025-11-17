Let us implement a new feature for the Zippel language. We want a syntax for defining multivariate (many variables) polynomials. Right now you can use the "poly" command to create a polynomial from vectors
   of coefficients, like this "poly([1,2,3])". Now I want a syntax "fun x => x^2 + 2*x + 3" to define the same univariate polynomial, or "fun x y z => 3*x + 4*y + 5*x*z" to define a multivariate polynomial of
   three variables. At this point, we should say that the Zippel type system supports two types of polynomials, univariate polynomials of degree N (Uni<N>) or Multilinear polynomials of M variables (Mle<M>).

We need a new type for multivariable polynomials (M variables) of degree at most N (Poly<M, N>). So maybe the plan is the following:

   1. Add a new type Poly<M, N> in typ.rs
   2. Remove the existing types Uni<N> and Mle<M> and make them basically aliases for Poly<1, N> and Mle<M, 1> respectively.
   3. Extend the syntax zippel.pest and the FromPest instance for UExp to add support for the "fun x, y, z => <polynomial over x, y z>" syntax.
   4. Write unit tests for the parser and make sure existing tests pass.

   Let us write down this plan while expanding on the details in a .md file and get ready to implement it step by step.
