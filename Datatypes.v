Parameter imm : Type.
Parameter branch : Type.

Inductive math_expr :=
    | PlusExpr : math_expr -> math_expr -> math_expr
    | MinusExpr : math_expr -> math_expr -> math_expr
    | ImmExpr : imm -> math_expr.
