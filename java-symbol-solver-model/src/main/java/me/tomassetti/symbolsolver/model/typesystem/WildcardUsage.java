package me.tomassetti.symbolsolver.model.typesystem;

/**
 * A wildcard can be:
 * - unbounded (?)
 * - have a lower bound (? super Number)
 * - have an upper bound (? extends Number)
 * It is not possible to have both a lower and an upper bound at the same time.
 */
public class WildcardUsage implements TypeUsage {

    public static WildcardUsage UNBOUNDED = new WildcardUsage(null, null);
    private BoundType type;
    private TypeUsage boundedType;

    private WildcardUsage(BoundType type, TypeUsage boundedType) {
        if (type == null && boundedType != null) {
            throw new IllegalArgumentException();
        }
        if (type != null && boundedType == null) {
            throw new IllegalArgumentException();
        }
        this.type = type;
        this.boundedType = boundedType;
    }

    @Override
    public String toString() {
        return "WildcardUsage{" +
                "type=" + type +
                ", boundedType=" + boundedType +
                '}';
    }

    public static WildcardUsage superBound(TypeUsage typeUsage) {
        return new WildcardUsage(BoundType.SUPER, typeUsage);
    }

    public static WildcardUsage extendsBound(TypeUsage typeUsage) {
        return new WildcardUsage(BoundType.EXTENDS, typeUsage);
    }

    public boolean isWildcard() {
        return true;
    }

    public WildcardUsage asWildcard() {
        return this;
    }

    @Override
    public boolean isReference() {
        return true;
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

    public boolean isSuper() {
        return type == BoundType.SUPER;
    }

    public boolean isExtends() {
        return type == BoundType.EXTENDS;
    }

    public TypeUsage getBoundedType() {
        if (boundedType == null) {
            throw new IllegalStateException();
        }
        return boundedType;
    }

    @Override
    public boolean isAssignableBy(TypeUsage other) {
        if (boundedType == null) {
            //return other.isReferenceType() && other.asReferenceTypeUsage().getQualifiedName().equals(Object.class.getCanonicalName());
            return false;
        } else if (type == BoundType.SUPER) {
            return boundedType.isAssignableBy(other);
        } else if (type == BoundType.EXTENDS) {
            return false;
        } else {
            throw new RuntimeException();
        }
    }

    @Override
    public TypeUsage replaceParam(String name, TypeUsage replaced) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        if (boundedType == null) {
            return this;
        }
        TypeUsage boundedTypeReplaced = boundedType.replaceParam(name, replaced);
        if (boundedTypeReplaced == null) {
            throw new RuntimeException();
        }
        if (boundedTypeReplaced != boundedType) {
            return new WildcardUsage(type, boundedTypeReplaced);
        } else {
            return this;
        }
    }

    public enum BoundType {
        SUPER,
        EXTENDS
    }
}
