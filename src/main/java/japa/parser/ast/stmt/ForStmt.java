/*
 * Copyright (C) 2007 Júlio Vilmar Gesser.
 * 
 * This file is part of Java 1.5 parser and Abstract Syntax Tree.
 *
 * Java 1.5 parser and Abstract Syntax Tree is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Java 1.5 parser and Abstract Syntax Tree is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Java 1.5 parser and Abstract Syntax Tree.  If not, see <http://www.gnu.org/licenses/>.
 */
/*
 * Created on 07/11/2006
 */
package japa.parser.ast.stmt;

import japa.parser.ast.expr.Expression;
import japa.parser.ast.visitor.GenericVisitor;
import japa.parser.ast.visitor.VoidVisitor;

import java.util.Iterator;
import java.util.List;

/**
 * @author Julio Vilmar Gesser
 */
public final class ForStmt extends Statement {

	private List<Expression> init;

	private Expression compare;

	private List<Expression> update;

	private Statement body;

	public ForStmt() {
	}

	public ForStmt(final List<Expression> init, final Expression compare,
			final List<Expression> update, final Statement body) {
		setCompare(compare);
		setInit(init);
		setUpdate(update);
		setBody(body);
	}

	public ForStmt(final int beginLine, final int beginColumn,
			final int endLine, final int endColumn,
			final List<Expression> init, final Expression compare,
			final List<Expression> update, final Statement body) {
		super(beginLine, beginColumn, endLine, endColumn);
		setCompare(compare);
		setInit(init);
		setUpdate(update);
		setBody(body);
	}

	@Override
	public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
		return v.visit(this, arg);
	}

	@Override
	public <A> void accept(final VoidVisitor<A> v, final A arg) {
		v.visit(this, arg);
	}

	public Statement getBody() {
		return body;
	}

	public Expression getCompare() {
		return compare;
	}

	public List<Expression> getInit() {
		return init;
	}

	public List<Expression> getUpdate() {
		return update;
	}

	public void setBody(final Statement body) {
		this.body = body;
		if (this.body != null) {
			this.body.setParentNode(this);
		}
	}

	public void setCompare(final Expression compare) {
		this.compare = compare;
		if (this.compare != null) {
			this.compare.setParentNode(this);
		}
	}

	public void setInit(final List<Expression> init) {
		this.init = init;
		if (this.init != null) {
			Iterator<Expression> it = init.iterator();
			while (it.hasNext()) {
				Expression current = it.next();
				current.setParentNode(this);
			}
		}
	}

	public void setUpdate(final List<Expression> update) {
		this.update = update;
		if (this.update != null) {
			Iterator<Expression> it = this.update.iterator();
			while (it.hasNext()) {
				Expression current = it.next();
				current.setParentNode(this);
			}
		}
	}
}
