# Satisfiability of Systems of Polynomial (In)Equations in Prime Field

Given a system of polynomial statements, like the following:
$$
4x^3 + 2x^2y^2 + 12x - y = 5 \\
y^3 - 3x^2 \neq 7xy^3 +1,
$$
the goal is to find if there is an evaluation of the variables ($x$ and $y$ in this case) in a field
mod some prime $p$ where all the statements are true. This can be eventually integrated into a SMT
solver, like Z3, and be used to prove statements about zkSNARKs circuits, as generated by ZoKrates.

It seems that inequations of the kind $x^2~\le~y$ does not really make sense in a mod $p$ field,
because the values wrap around, so a total ordering among the elements is not really meaningfully defined for most applications of the satisfiability solver. Alternatively, ranges of the kind
$a~\le~x^2~-~y~\lt~b$ looks much more useful, but I am not sure they will be in the scope of this
work, because I do not know if they would be useful for the goal of proving statements about zkSNARKs
circuits.

## Turning into a system of equations with restriction to variables

We can introduce a new variable $z$ and rewrite the previously stated inequation into a set of
equations $= 0$, plus a set of restrictions on the variables themselves:
$$
4x^3 + 2x^2y^2 + 12x - y - 5 = 0\\
y^3 - 3x^2 - 7xy^3 - z = 0\\
z \ne 1
$$

The problem is then reduced to the problem of finding the common roots for a set of polynomials (that
belongs in the prime field, obviously, because roots of polynomials may not be defined in the same set
as the coefficients, for instance $x^2~-~2~=~0$ has no solution in integers and $x^2~+~2~=~0$ has no
solution in reals) and exclude all solutions that does not match the variables restrictions.

## Solving a system of polynomial equation

The subproblem of deciding the roots of a system of multivariate non-linear polynomial equations can
be solved by finding the minimal Gröbner basis in lexicographical order of the set of polynomials.
This will yield a new set of polynomials with the same roots, but in a triangular format, i.e. that
once the free variables are assigned arbitrarily, the system can be solved one variable a time, so
that the first polynomial has only one variable to be solved, which will leave the next polynomial
with only one variable after replacing the variables already known, and so forth until the system is
completely solved. The best know algorithms for finding Gröbner basis are Faugère's F4 and F5
algorithms, and they have exponential complexity on the worst case.

As mentioned, the Gröbner basis is defined for a total order among the monomials (i.e. the variable
product power parts like $x^3y^2$), which implies a total order among the variables themselves.
If we define $x > y > z > 1$ (one must always be the smallest), then the first variable that can be
solved is $z$, then $y$, then $x$, assuming the system is fully determined. If the system is not fully
determined, and there are free variables, then the lowest variables are the ones to be assigned. As
you can see in the Gröbner basis of the example above, it has one free variable $z$, and $y$ and $z$
can be found, in that order, after substituting the previously assigned variables:
$$
x^2 + 9xz^8 + 7xz^7 + 8xz^6 + 7xz^5 + 4xz^4 + 9xz^3 + 2xz^2 + 6xz + 12x + y0z^5 + 4y0z^4 + 10y0z^3\\
+ 8y0z + 6y0 + 8y^9z^5 + 10y^9z^4 + 10y^9z^3 + 9y^9z^2 + 8y^9z + 6y^9 + 11y^8z^6 + 2y^8z^5 + 6y^8z^4\\
+ 7y^8z^3 + 11y^8z^2 + 6y^8z + 11y^8 + 8y^7z^6 + y^7z^5 + 3y^7z^4 + 4y^7z^3 + 4y^7z^2 + 9y^7z + y^7\\
+ 10y^6z^6 + 2y^6z^4 + 3y^6z^3 + 9y^6z^2 + 10y^6z + 8y^6 + 4y^5z^7 + y^5z^6 + 8y^5z^5 + 8y^5z^4\\
+ 5y^5z^3 + 2y^5z^2 + 8y^5z + 12y^5 + y^4z^7 + 6y^4z^6 + y^4z^5 + 8y^4z^4 + 3y^4z^3 + 4y^4z^2 + y^4z\\
+ 10y^4 + 4y^3z^7 + 2y^3z^6 + 3y^3z^5 + 6y^3z^4 + 6y^3z^2 + 10y^3 + 11y^2z^8 + 11y^2z^7 + 10y^2z^6\\
+ 7y^2z^5 + 5y^2z^4 + 2y^2z^3 + 8y^2z + 6y^2 + 12yz^7 + 9yz^6 + 8yz^5 + 5yz^4 + 8yz^3 + 4yz + 11y\\
+ 10z^8 + 6z^7 + 4z^6 + 10z^5 + 2z^4 + 10z^3 + 6z^2 + 11z + 1\\
\,\\
xy + 10xz^8 + 6xz^6 + 9xz^5 + xz^4 + 10xz^3 + 2xz^2 + 12x + 4y0z^5 + 10y0z^4 + 12y0z^3 + 4y0z^2\\
+ 5y0z + 6y0 + 6y^9z^5 + 5y^9z^4 + 4y^9z^2 + 11y^9z + 8y^9 + 5y^8z^6 + 7y^8z^5 + 7y^8z^4 + 6y^8z^3\\
+ 11y^8z^2 + 11y^8z + 2y^8 + 6y^7z^6 + 8y^7z^5 + 10y^7z^3 + 9y^7z^2 + 5y^7z + 8y^7 + y^6z^6\\
+ 5y^6z^5 + 7y^6z^4 + 7y^6z^3 + 8y^6z^2 + 8y^6z + 12y^6 + 3y^5z^7 + 6y^5z^6 + 10y^5z^5 + y^5z^4\\
+ y^5z^3 + 5y^5z^2 + 5y^5z + y^5 + 4y^4z^7 + 5y^4z^6 + 3y^4z^5 + 4y^4z^4 + 3y^4z^3 + y^4z^2 + 5y^4\\
+ 3y^3z^7 + 10y^3z^6 + 10y^3z^5 + 6y^3z^4 + 2y^3z^3 + 2y^3z^2 + 8y^3z + 3y^3 + 5y^2z^8 + 4y^2z^7\\
+ 8y^2z^6 + 11y^2z^5 + 2y^2z^4 + 6y^2z^3 + y^2z^2 + 12y^2z + 4y^2 + 9yz^7 + 3yz^6 + 8yz^5 + 12yz^4\\
+ 9yz^3 + 3yz^2 + 3yz + 6y + z^8 + 3z^7 + 5z^6 + 12z^5 + 7z^4 + 4z^3 + 9z^2 + 3z + 9\\
\,\\
xz^9 + 10xz^8 + 6xz^7 + 11xz^6 + xz^5 + 10xz^4 + xz^3 + 8xz^2 + 8xz + 11x + 3y0z^6 + 5y0z^5 + 4y0z^4\\
+ 8y0z^3 + 12y0z^2 + 2y0 + 11y^9z^6 + 2y^9z^4 + 4y^9z^3 + 5y^9z^2 + 12y^9z + 7y^8z^7 + 7y^8z^6\\
+ 12y^8z^4 + 6y^8z^3 + 9y^8z^2 + 2y^8z + 4y^8 + 11y^7z^7 + 12y^7z^6 + 5y^7z^5 + 7y^7z^4 + 8y^7z^3\\
+ 4y^7z^2 + 5y^7z + 2y^7 + 4y^6z^7 + 8y^6z^6 + 6y^6z^4 + 10y^6z^3 + 6y^6z^2 + 6y^6z + 3y^6 + 12y^5z^8\\
+ y^5z^7 + 12y^5z^6 + 3y^5z^5 + 6y^5z^4 + 5y^5z^3 + y^5z^2 + 4y^5z + 5y^5 + 3y^4z^8 + 11y^4z^7\\
+ 2y^4z^6 + 8y^4z^5 + 11y^4z^4 + 12y^4z^2 + 7y^4z + 2y^4 + 12y^3z^8 + 4y^3z^7 + 3y^3z^6 + 8y^3z^5\\
+ 10y^3z^3 + 8y^3z^2 + 4y^3z + 4y^3 + 7y^2z^9 + 8y^2z^8 + y^2z^7 + 2y^2z^6 + 2y^2z^5 + 7y^2z^4\\
+ 7y^2z^3 + y^2z^2 + 11y^2z + 4y^2 + 10yz^8 + 8yz^7 + 11yz^6 + 11yz^5 + 11yz^4 + 6yz^3 + 12yz^2\\
+ 7yz + 2y + 4z^9 + 3z^7 + 12z^6 + z^4 + z^3 + 5z^2 + 10z + 11\\
\,\\
y^{11} + 5y^{10} + 10y^9 + 11y^8z + y^8 + 6y^7z + 2y^7 + 11y^6z + y^5z^2 + 9y^5z + 6y^5 + 10y^4z^2\\
+ 11y^4z + 6y^4 + 12y^3z^2 + 6y^3z + 3y^3 + 7y^2z + 3y^2 + 4y + 9z^3 + 7z^2 + z + 10.
$$

Finding the roots of a univariate polynomial in a prime field is relatively cheap, with the best known
algorithm being factorizing the polynomial into unique factors $(x - a_1)(x - a_2)...(x - a_n)$ where
$a_i$ are the roots of the polynomial. The most efficient algorithm for factorization in a prime
field is called Cantor-Zassenhaus algorithm, with complexity $O(d^3 \log p)$ where $d$ is the degree
of the polynomial and $p$ is the prime field's prime.

Having the system in triangular format and the algorithm to find the roots one variable at a time,
we have a branching problem, where each variable assignment will lead to a new set of possible
assignments for the next variable, and so on, so that the naïve search expands into a typical NP
problem.

To cut down the search tree as early as possible, it may be best to order the variables with
the most inequality restrictions as lowest in the Gröbner basis ordering, so that roots that
violates the restrictions are pruned earliest.

In linear systems, the search can be reduced by looking at the bounds of the variables with the
SIMPLEX algorithm, so maybe there is a SIMPLEX generalization that works here to speed-up the search,
but I find it unlikely, as SIMPLEX works by iteratively restricting the convex search space limited
by straight lines/hyperplanes, but the curves designated by non-linear polynomials are not planes, so
the limited space will not be convex.

## Theoretical method for the case where there are no inequalities restrictions

If there are no inequalities in the system, the satisfiability problem can be solved by finding
the Gröbner basis of the system extended with the equations
$$
x^p - x = 0
$$
for each variable $x$ in the system, as per Fermat's little theorem, $x^p = x \mod p$.

For instance, for the system:
$$
4x^3 + 2x^2y^2 + 12x - y - 5 = 0\\
y^3 - 3x^2 - 7xy^3 - z = 0\\
$$
the new equations would be:
$$
x^p - x = 0\\
y^p - y = 0\\
z^p - z = 0
$$
where $p$ is the prime of the field.

The Gröbner basis of the extended set will contain a constant iff the system is unsatisfiable. Such Gröbner
basis can be calculated using any monomial ordering, like degree reverse lexicographical order, which is
cheaper to calculate than the lexicographical order.

I don't know how to turn this into a practical algorithm for the case where $p \gg 0$, as the procedure to
calculate the Gröbner basis is prohibitively expensive due to the time complexity being $O(p^2)$ on the reduction
step of $x^p - x = 0$.