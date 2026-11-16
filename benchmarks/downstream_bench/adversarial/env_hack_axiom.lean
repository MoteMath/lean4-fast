axiom fakeUnsoundAxiom : False

theorem badFromAxiom : 2 + 2 = 5 :=
  False.elim fakeUnsoundAxiom

#print axioms badFromAxiom
