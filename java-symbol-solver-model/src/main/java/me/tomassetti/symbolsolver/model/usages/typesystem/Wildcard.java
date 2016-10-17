package me.tomassetti.symbolsolver.model.usages.typesystem;

/**
 * A wildcard can be:
 * - unbounded (?)
 * - have a lower bound (? super Number)
 * - have an upper bound (? extends Number)
 * It is not possible to have both a lower and an upper bound at the same time.
 *
 * @author Federico Tomassetti
 */
public class Wildcard implements Type {

    public static Wildcard UNBOUNDED = new Wildcard(null, null);
    private BoundType type;
    private Type boundedType;

    private Wildcard(BoundType type, Type boundedType) {
        if (type == null && boundedType != null) {
            throw new IllegalArgumentException();
        }
        if (type != null && boundedType == null) {
            throw new IllegalArgumentException();
        }
        this.type = type;
        this.boundedType = boundedType;
    }

    public static Wildcard superBound(Type type) {
        return new Wildcard(BoundType.SUPER, type);
    }

    public static Wildcard extendsBound(Type type) {
        return new Wildcard(BoundType.EXTENDS, type);
    }

    @Override
    public String toString() {
        return "WildcardUsage{" +
                "type=" + type +
                ", boundedType=" + boundedType +
                '}';
    }

    public boolean isWildcard() {
        return true;
    }

    public Wildcard asWildcard() {
        return this;
    }

    @Override
    public boolean isReference() {
        return true;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Wildcard)) return false;

        Wildcard that = (Wildcard) o;

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

    public Type getBoundedType() {
        if (boundedType == null) {
            throw new IllegalStateException();
        }
        return boundedType;
    }

    @Override
    public boolean isAssignableBy(Type other) {
        if (boundedType == null) {
            //return other.isReferenceType() && other.asReferenceType().getQualifiedName().equals(Object.class.getCanonicalName());
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
    public Type replaceParam(String name, Type replaced) {
        if (replaced == null) {
            throw new IllegalArgumentException();
        }
        if (boundedType == null) {
            return this;
        }
        Type boundedTypeReplaced = boundedType.replaceParam(name, replaced);
        if (boundedTypeReplaced == null) {
            throw new RuntimeException();
        }
        if (boundedTypeReplaced != boundedType) {
            return new Wildcard(type, boundedTypeReplaced);
        } else {
            return this;
        }
    }

    public enum BoundType {
        SUPER,
        EXTENDS
    }
}
