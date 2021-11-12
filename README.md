An implementation of a Zeilberger-style linear type theory.

In intuitionistic type theory, every judgement `Γ ⊢ t : A` has a unique type on the right, every rule operates on the right hand side. The term `t` is nothing other than a faithful syntax tree that represents how the rules are applied. Since every rule operate on the right hand side only, the shape of the derivation tree of `Γ ⊢ t : A` mirrors that of the syntax tree of `t`.

The situation becomes worse when we try to create rules that operates on the left hand side. For example, if we want to mimic the left-introduction rule (instead of using right-elimination as usual) of conjunction in sequent calculus, we might try
```
  x:A, y:B |- t : C
----------------------
 p:(A ∧ B) |- t?? : C
```
You can immediately see that we have difficulties coming up with the syntax for `t`. A possible attempt is `t[x,y -> p]`, which looks nice but has a deadly flaw: Suppose the context have 20 variables, we can apply this rule 10 times, turning the context into 10 variables. Depending on the order that we apply the rules, we have 10! = 3628800 different terms. However, each of these derivation trees are definitely the same: the left-introduction rules act in parallel to each other, and any reasonable semantics should assign the same value to the 3628800 different terms. This is a discrepancy between syntax and semantics, which is bad.

The difficulty arises from the fact that there are parallel rule applications whose order should not matter (and so should not be present in the syntax). In the same spirit, trying to make a type theory with multiple conclusions on the right (the lambda-mu calculus is such an example) will meet the same problem. Intuitionistic type theory does not have this problem because every rule "focuses" on one formula: the formula on the right hand side.

With this in mind, we can see that in order to achieve what we want (either (a) to have rules that operate on the left, or (b) allow multiple conclusions on the right), we need alternative ways to keep track of the "focus". This coincides with Andreoli's focused proof search in linear logic. Of course, we don't have to be linear, and Zeilberger refrains to impose linearity to his theory. But adding linearity is very natural (and a simple tweak of the code removes the linearity constraint).

Therefore, we propose this linear type theory. It simultaneously absorbs how linear logic unifies intuitionistic logic and classical logic, and explains the deep connection of evaluation and pattern matching.

----

For reference, see [this proposal](http://www.cs.cmu.edu/~noam/research/proposal.pdf) and [this paper](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.160.5502). However, I altered the presentation of non-canonical terms to make it easier to use and reason.
