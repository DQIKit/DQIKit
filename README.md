# DQI-Kit
DQI-Kit is a software framework for encoding combinatorial optimisation into the Max-LINSAT and Max-XORSAT formats for the [Decoded Quantum Interferometry](https://arxiv.org/pdf/2408.08292) algorithm.

## Features
- user-defined Max-XORSAT and Max-LINSAT instances for fields of arbitrary size
- DQI performance estimation in both the perfect and imperfect decoding regimes
- automatic transformation of domain objectives/constraints into the Max-LINSAT format:
    - integer equalities: $2 a - 3 b = 4 - 5 c$
    - integer inequalities: $\neq, \leq, <, \geq, >$
    - Boolean constraints: $\neg a \wedge (b \vee c)$
    - linear objectives: $\text{maximize} \,\,a + b + c$
    - binary polynomial objectives: $a (b + c) - 2 a$
    - binary polynomial constraints: $a (b + c) - 2 a \geq 0$
    - modular constraints: $a + b = 4 \pmod{5}$
    - range constraints: $a \in [0, 4]$
    - $\ldots$
- automatic selection optimal DQI hyperparameters
- 6 implemented classical decoders + the ability to implement custom decoders
- 4 classical solvers + the ability add custom solvers


## Requirements and Installation 
DQI-Kit has several dependencies, including SageMath, GAP and OR-Tools.
We thus recommend using our `Dockerfile`:
```bash
docker build -t dqi-kit . && docker run -it dqi-kit
```

## Example
DQI for _Minimum Vertex Cover_:
```python
# Create graph
n = 10
G = nx.cycle_graph(n)

# Create problem
vertex_cover = MaxConstraintSat()

# Each vertex has one of two colors (0 = white, 1 = black)
x = [
    vertex_cover.new_binary_var(f"x_{i}")
    for i in range(n)
]

# Objective: minimize the number of black vertices
vertex_cover.add_objective(
    sum(x_i for x_i in x),
    minimize=True,
)

# Contraints: for each edge (u, v) either u or v must be black
for u, v in G.edges:
    vertex_cover.add_boolean_constraint(
        x[u] | x[v],
        # constraints have priority over objective
        weight=2,
    )

# Transform constrained optimisation problem into Max-LINSAT format
max_lin_sat = vertex_cover.to_max_lin_sat()

# Estimate DQI solution quality for degree ℓ = 3
dqi = Dqi(prob)
print("DQI:", dqi.estimate_solution_quality(l = 3))

# Compare DQI solution with simulated annealing solver
sim_anneal = SimAnnealSolver(prob)
print("simulated annealing:", sim_anneal.get_solution_quality())
```

## Usage

### MaxLinSat
Given a set of $m$ (weighted) linear constraints over $n$ variables, Max-LINSAT is the problem finding the variables assignment which maximizes the (weighted) number of satisfied constraints.

The `MaxLinSat` class represents a (weighted) Max-LINSAT instance.
The finite field used is passed as a constructor argument:
```python
from max_lin_sat import MaxLinSat
from sage.all import GF

instance = MaxLinSat(GF(2 ** 8))
```
The `MaxXorSat` from `./max_lin_sat.py` is a shorthand for `MaxLinSat(GF(2))`.
Variables are created for each instance by calling the `new_var(name: str)` method and are automatically restricted to be field elements.

Variables and scalars can be combined by using the `+`, `-`, `*`, `==` and `!=` operators to create constraints (e.g. `2 * a - 4 != b`).
Scalars are field elements from the SageMath `GF` field or `int`s, which are automatically converted to field elements.

To define set constraints, you can use the `==` and `!=` operators along with a `set` (e.g. `a + b == {0, 1}`).
Constraints are added to the `MaxLinSat` instance via the `add_constraint(constraint, weight=1)` method.
Only integer weights are supported.

### MaxConstraintSat
The `MaxConstraintSat` class (in `/max_constraint_sat.py`) represents an instance of a constrained optimization problem.
Each `MaxConstraintSat` includes objectives and weighted constraints where the weight of each constraint represents the penalty if broken.
The goal is to find a variable assignment which maximizes the sum of all objectives minus the weighted sum of all satisfied constraints.

A new variable is created with the `new_var(name: str, lower: int, upper: int)` method on `MaxConstraintSat`.
Only integer variables are supported and each variable has to come with a lower and upper bound restricting its range.
Variables and scalars can be combined with `+`, `-`, `*` and `/` expressions (`/` is only supported if the right-hand side is a scalar).
As scalars, `int`s and `Fraction`s (from Python's `fraction`) package are supported.
Floats are also possible but are always converted into `Fraction`s.

An expression can be added as an objective using the `MaxConstraintSat.add_objective` method.
Objectives are maximizing by default, but `add_objective` takes an optional `minimize` Boolean argument.
The method takes an optional `weight` argument, which is a `Fraction` or `int`.

Two expressions can be combined with `==, !=, <=, <, >=, >` to form a constraint.
Constraints can be added using the `MaxConstraintSat.add_constraint` method, which again takes an optional `weight` argument.
Modular constraints can be defined using `%` operator. Be careful with the operator precedence: `instance.add_constraint((a + b == 0) % 2)`.

`MaxConstraintSat` supports polynomial expressions and constraints like `(a + b) * (c + d) + e` or `a * b = 0`.

Binary variables can be created using the `new_binary_var` method.
Binary variables can be combined with the operators `~, &, |, ^` to create binary constraints.
A binary constraint (again with an optional `weight`) can be added using the `add_binary_constraint` method.

A `MaxConstraintSat` instance can be converted into a `MaxLinSat` instance using the `to_max_lin_sat` method, which takes multiple arguments:
- `max_degree` (default: 3): The maximum degrees of polynomial objectives/constraints and Boolean constraints is capped at this value. Any terms of larger degree are decomposed into smaller-degree terms.
A larger `max_degree` generally leads to more Max-LINSAT constraints, but fewer linearly dependent constraints.
- `var_range_constraint_factor`: Each variable is defined with a range (`[upper, lower]`). Additional constraints are added during the transformation to restrict each variable to this range, which should generally get a larger weight. This weight is determined by this factor.
- `equality_constraint_factor`: This argument similarly determines the weight of any additional equality constraints added when decomposing higher-order constraints/objectives.

Note that `to_max_lin_sat` as of not does not support the conversion of polynomial constraints over non-binary variables.

### Dqi
DQI-Kit provides a DQI solver: `Dqi` in `./dqi.py`.
The `Dqi` constructor takes two arguments, the Max-LINSAT instance and optional decoder constructor argument (cf. decoders section).
The main method provided by `Dqi` is `estimate_solution_quality` which takes the following arguments:
- `l`: Determines the degree of the DQI polynomial: larger = potentially better performance, too large = performance degrades due to decoding errors
- `rhs_approximation` (default: `True`): If true, right-hand sides of constraints (e.g. $1$ for $a + b = 1$) are assumed to be uniformly random. This leads to exponentially faster performance estimation while leading to potentially slightly inaccurate results. In the perfect decoding regime, this flag is ignored as here, DQI performance is independent from the right-hand sides anyway.
- `n_decoding_samples` (default: `500`): Determines how many errors are sampled for each error weight (this is only relevant in the imperfect decoding regime). Higher sample numbers lead to more accurate results, but take longer to compute. If set to `None`, all possible errors are used. This leads to an exact result at the expense of an exponential runtime.
- `n_interference_samples` (default: `10000`): This parameter is only used in the imperfect decoding regime and if `rhs_approximation` is `False`. It determines, how many pairs of codewords are sampled to compute the inference for estimating DQI performance. Larger values lead to a more accurate estimation, but require more time to compute.
- `w`: Determines the coefficients of the DQI bias polynomial as a real-valued NumPy array of length `l + 1`. If left empty, the coefficients are computed automatically. These automatically determined coefficients are optimal in the perfect decoding regime and approximately optimal in the imperfect decoding regime.
Depending on the selected parameters `estimate_solution_quality` can take exponential time. 
As alternative method `semicircle_law_solution_quality()` computed the guaranteed solution quality of DQI in the perfect decoding regime.
However, this is possible for Max-LINSAT instances with minimum distance at least 4.

### Decoders
Decoding algorithm for DQI are provided by the `./decoders.py` file. We provide 6 decoders:
- `NearestNeighborDecoder`: Finds the nearest codeword using brute force search. Works for arbitrary codes but is only fast enough for applications for codes for small values of `l`
- `SyndromeDecoder`: Achieves the same results as `NearestNeighborDecoder` by creating a error lookup table. Requires exponential time once at creation but then achieves constant time decoding.
- `InformationSetDecoder`: A wrapper around the [`LinearCodeInformationSetDecoder`](https://doc.sagemath.org/html/en/reference/coding/sage/coding/information_set_decoder.html) from SageMath.
- `BeliefPropagationDecoder`: A wrapper around the [`BpDecoder`](https://software.roffe.eu/ldpc/ldpc/bp_decoder.html) from the `ldpc` package.
- `BeliefPropagationOsdDecoder`: A wrapper around the [`BpOsdDecoder`](https://software.roffe.eu/ldpc/ldpc/bposd_decoder.html) from the `ldpc` package.
- `GeneralizedReedSolomonDecoder`: Specialized decoder for generalized Reed-Solomon codes and the Optimal Polynomial Intersection problem (cf. [Jordan et al.](https://arxiv.org/pdf/2408.08292))

Each decoder has a static `constructor` method that returns a constructor which can be passed to the optional `decoder_constructor` argument of the `Dqi` constructor. `InformationSetDecoder.constructor`, `BeliefPropagationDecoder.constructor` and `BeliefPropagationOsdDecoder.constructor` take optional parameters that are passed on to the underlying decoder implementations (such as `ldpc`'s `BpDecoder` for `BeliefPropagationDecoder`):
```python
import MaxLinSat from max_lin_sat
import BeliefPropagationDecoder from decoders

# instance = MaxLinSat(...)
# instance.add_constraint(...)
# ...

# initialize
syndrome_dqi = Dqi(
    instance,
    decoder_constructor=SyndromeDecoder.constructor(),
)

# initialize DQI solver with Product Sum Belief Progation decoder
bp_dqi = Dqi(
    instance,
    decoder_constructor=BeliefPropagationDecoder.constructor(
        bp_method="product_sum"
    ),
)
```
If the user does not pass a `decoder_constructor`, one is determined automatically based on the code.

You can implement your own custom decoder by extending the `AbstractDecoder` class.
Here, you need to implement two methods:
- `decode(vector, int) -> vector`: Gets a corrupted codeword as a Sage vector of the finite field as well as the number of errors `l` and should return the decoded codword.
- `decoding_radius() -> int | None`: Returns how many errors are guaranteed to be corrected or `None` if no guarantees can be made.

### Solvers
In addition to DQI, we provide  classical solvers located in `./classical_solvers.py`.
All solvers get passed a `MaxLinSat` instance as the first constructor argument as well as potential additional arguments depending on the solver.
Each solver supports the following methods:
- `get_solution()`: Computes the solution or returns the previously computed solution as a Sage vector over the finite field
- `get_solution()`: Returns the number of Max-LINSAT constriants satisfied by the solution.

The following solvers are provided by DQI-KIT:
- `BruteForceSolver`: Finds the optimal solution using brute force. 
- `OrToolsSolver`: Uses The CP-SAT solver from Google's OR-Tools to find a solution. A time limit is passed a the second constructor parameter. If no limit is povided, the solver finds the optimal solution (with exponential runtime). The method `is_optimal()` returns `True` if the found solution is known to be optimal.
- `SimAnnealSolver`: Finds a solution using simulated annealing. Along with the Max-LINSAT instance, it accepts the following optional arguments:
    - `initial_state` (default random): The initial solution
    - `Tmax`, `Tmin` (default `25000`, `2.5`): the initial and final tempetature
    - `steps`: the number of simulated annealing iterations
- `PrangeSolver`: Uses Prange's algorithm, which finds a linearly dependent subset of $n$ constraints, satisfies them and "hopes for the best" for the remaining $m - n$ constraints.

To implement your own custom solver, simply extend the the `AbstractSolver` class and implement the `compute_solution(instance)` method.






## Documentation
Coming soon...
