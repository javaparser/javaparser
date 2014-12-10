package com.github.javaparser.ast.expr;


import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;

import java.util.List;

/**
 * Lambda expressions. 
 * @author Raquel Pau
 *
 */
public class LambdaExpr extends Expression {

	private List<Parameter> parameters;

	private boolean parametersEnclosed;

	private Statement body;

	public LambdaExpr() {
	}

	public LambdaExpr(int beginLine, int beginColumn, int endLine,
                      int endColumn, List<Parameter> parameters, Statement body,
                      boolean parametersEnclosed) {

		super(beginLine, beginColumn, endLine, endColumn);
		this.parameters = parameters;
		this.body = body;

		if (this.parameters != null && this.parameters.size() == 1
				&& this.parameters.get(0).getType() == null) {
			this.parametersEnclosed = parametersEnclosed;
		} else {
			this.parametersEnclosed = true;
		}
	}

	public List<Parameter> getParameters() {
		return parameters;
	}

	public void setParameters(List<Parameter> parameters) {
		this.parameters = parameters;
	}

	public Statement getBody() {
		return body;
	}

	public void setBody(Statement body) {
		this.body = body;
	}

	@Override
	public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(VoidVisitor<A> v, A arg) {
		v.visit(this, arg);
	}

	public boolean isParametersEnclosed() {
		return parametersEnclosed;
	}

	public void setParametersEnclosed(boolean parametersEnclosed) {
		this.parametersEnclosed = parametersEnclosed;
	}

}
