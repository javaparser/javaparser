package me.tomassetti.symbolsolver.model.typesystem;

import com.github.javaparser.ast.type.WildcardType;

import java.util.List;

public class WildcardUsage implements TypeUsage {

    //private WildcardType type;
    private BoundType type;
    private ReferenceTypeUsage boundedType;

    public enum BoundType {
        SUPER,
        EXTENDS
    }

    public static WildcardUsage UNBOUNDED = new WildcardUsage(null, null);

    public static WildcardUsage superBound(ReferenceTypeUsage typeUsage) {
        return new WildcardUsage(BoundType.SUPER, typeUsage);
    }

    public static WildcardUsage extendsBound(ReferenceTypeUsage typeUsage) {
        return new WildcardUsage(BoundType.EXTENDS, typeUsage);
    }

    private WildcardUsage(BoundType type, ReferenceTypeUsage boundedType) {
        this.type = type;
        this.boundedType = boundedType;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof WildcardUsage)) return false;

        WildcardUsage that = (WildcardUsage) o;

        if (boundedType != null ? !boundedType.equals(that.boundedType) : that.boundedType != null) return false;
        if (type != that.type) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = type != null ? type.hashCode() : 0;
        result = 31 * result + (boundedType != null ? boundedType.hashCode() : 0);
        return result;
    }

    @Override
    public String describe() {
        if (type == null) {
            return "?";
        } else if (type == BoundType.SUPER) {
            return "? super " + boundedType.describe();
        } else if (type == BoundType.EXTENDS) {
            return "? extends " + boundedType.describe();
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        throw new UnsupportedOperationException();
    }

}
