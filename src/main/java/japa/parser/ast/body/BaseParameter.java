package japa.parser.ast.body;

import japa.parser.ast.Node;
import japa.parser.ast.expr.AnnotationExpr;

import java.util.List;

public abstract class BaseParameter extends Node {
    private int modifiers;

    private List<AnnotationExpr> annotations;
    
    private VariableDeclaratorId id;
    
    public BaseParameter() {
    }
    
    public BaseParameter(VariableDeclaratorId id) {
        setId(id);
	}

	public BaseParameter(int modifiers, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setId(id);
	}
	
	public BaseParameter(int modifiers, List<AnnotationExpr> annotations, VariableDeclaratorId id) {
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

	public BaseParameter(int beginLine, int beginColumn, int endLine, int endColumn, int modifiers, List<AnnotationExpr> annotations, VariableDeclaratorId id) {
	    super(beginLine, beginColumn, endLine, endColumn);
        setModifiers(modifiers);
        setAnnotations(annotations);
        setId(id);
	}

    public List<AnnotationExpr> getAnnotations() {
        return annotations;
    }

    public VariableDeclaratorId getId() {
        return id;
    }

    /**
     * Return the modifiers of this parameter declaration.
     * 
     * @see ModifierSet
     * @return modifiers
     */
    public int getModifiers() {
        return modifiers;
    }

    public void setAnnotations(List<AnnotationExpr> annotations) {
        this.annotations = annotations;
        setAsParentNodeOf(this.annotations);
    }

    public void setId(VariableDeclaratorId id) {
        this.id = id;
        setAsParentNodeOf(this.id);
    }

    public void setModifiers(int modifiers) {
        this.modifiers = modifiers;
    }
}
