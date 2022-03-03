package com.github.javaparser.ast.expr;

import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

public class EnumExpression extends LiteralExpr {
	private Enum value;

	public EnumExpression(Enum enumeration) {
		this.value = enumeration;
	}

	@Override
	public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(VoidVisitor<A> v, A arg) {
		v.visit(this, arg);

	}

	public void setValue(Enum value) {
		this.value = value;
	}

	public Enum getValue() {

		return value;
	}

}
