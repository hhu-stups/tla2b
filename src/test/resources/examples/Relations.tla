----------------------------- MODULE Relations -----------------------------

EXTENDS TLC, Sequences, Naturals, FiniteSets, Integers

domain(r) == {x[1]: x \in r}
range(r) == {x[2]: x \in r}
id(S) == {<<x,x>>: x \in S}
set_of_relations(x,y) == SUBSET (x \times y) 
domain_restriction(S, r) == {x \in r: x[1] \in S}
domain_substraction(S, r) == {x \in r: x[1] \notin S}
range_restriction(S, r) == {x \in r: x[2] \in S}
range_substraction(S, r) == {x \in r: x[2] \notin S}

rel_inverse(r) == {<<x[2],x[1]>>: x\in r}
relational_image(r, S) =={y[2] :y \in {x \in r: x[1] \in S}}
relational_overriding(r, r2) == {x \in r: x[1] \notin domain(r2)} \cup r2


direct_product(r1, r2) == {<<x, u>> \in (domain(r1)\cup domain(r2)) \times (range(r1) \times range(r2)):
     u[1] \in relational_image(r1, {x}) /\ u[2] \in relational_image(r2,{x})}
direct_product2(r1, r2) == {u \in (domain(r1)\cup domain(r2)) \times (range(r1) \times range(r2)):
     <<u[1],u[2][1]>> \in r1 /\ <<u[1],u[2][2]>> \in r2}

relational_composition(r1, r2) == {<<u[1][1],u[2][2]>> : u \in
    {x \in range_restriction(domain(r2),r1) \times domain_restriction(range(r1),r2): x[1][2] = x[2][1]}
        }

prj1(E, F) == {u \in E \times F \times E: u[1] = u[3]}
prj2(E, F) == {u \in E \times F \times F: u[2] = u[3]}


RECURSIVE iterate(_,_)
iterate(r, n) == CASE  n = 0 -> id(domain(r)\cup range(r))
                [] n = 1 -> r
                [] OTHER -> iterate(relational_composition(r,r), n-1)

RECURSIVE closure1(_)
closure1(R) == IF relational_composition(R,R) \R # {}
                THEN R \cup closure1(relational_composition(R,R)) 
                ELSE R

closure(R) == closure1( R \cup {<<x[1],x[1]>>: x \in R} \cup {<<x[2],x[2]>>: x \in R})

relational_call(r, x) == (CHOOSE y \in r: y[1] = x)[2]


is_partial_func(f) == \A x \in domain(f): Cardinality(relational_image(f, {x})) <= 1
is_partial_func2(f, S, S2) == /\ \A x \in f: x[1] \in S /\ x[2] \in S2 /\  relational_image(f, {x[1]}) = {x[2]}

partial_func(S, S2) == {x \in (SUBSET (S \times S2)): is_partial_func(x)}

is_func(f) == \A x \in domain(f): Cardinality(relational_image(f, {x})) < 2
total_func(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ domain(x)= S}

is_total_func(f, S, S2) == domain(f) = S /\ \A x \in f: x[1] \in S /\ x[2] \in S2 /\  relational_image(f, {x[1]}) = {x[2]}

is_injectiv_func(f) == \A x \in range(f): Cardinality(relational_image(rel_inverse(f), {x})) <= 1 
total_injection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ domain(x)= S /\ is_injectiv_func(x) }
partial_injection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ is_injectiv_func(x) }

total_surjection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x)/\ domain(x)= S /\ S2 = range(x)}
partial_surjection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x)/\ S2 = range(x)}

total_bijection(S, S2) == {x \in (SUBSET (S \times S2)): is_func(x) /\ domain(x) = S /\ is_injectiv_func(x) /\ S2 = range(x)}

=============================================================================