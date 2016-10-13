package me.tomassetti.symbolsolver.model.resolution;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Federico Tomassetti
 */
public interface TypeParameter {

    static TypeParameter onClass(final String name, String classQName, List<Bound> bounds) {
        return new TypeParameter() {
            @Override
            public String getName() {
                return name;
            }

            @Override
            public boolean declaredOnClass() {
                return true;
            }

            @Override
            public boolean declaredOnMethod() {
                return false;
            }

            @Override
            public String getQNameOfDeclaringClass() {
                return classQName;
            }

            @Override
            public List<Bound> getBounds(TypeSolver typeSolver) {
                return bounds;
            }

            @Override
            public String toString() {
                return "TypeParameter onClass " + name;
            }
        };
    }

    String getName();

    boolean declaredOnClass();

    boolean declaredOnMethod();

    String getQNameOfDeclaringClass();

    List<Bound> getBounds(TypeSolver typeSolver);

    default List<Bound> getExtendsBounds(TypeSolver typeSolver) {
        return getBounds(typeSolver).stream().filter(b -> b.isExtends()).collect(Collectors.toList());
    }

    default List<Bound> getSuperBounds(TypeSolver typeSolver) {
        return getBounds(typeSolver).stream().filter(b -> b.isSuper()).collect(Collectors.toList());
    }

    default String describe(TypeSolver typeSolver) {
        StringBuffer sb = new StringBuffer();
        sb.append(getName());
        List<Bound> extendsBounds = getExtendsBounds(typeSolver);
        if (!extendsBounds.isEmpty()) {
            sb.append(" extends ");
            sb.append(String.join(", ", extendsBounds.stream().map(b -> b.getType().describe()).collect(Collectors.toList())));
        }
        List<Bound> superBounds = getSuperBounds(typeSolver);
        if (!superBounds.isEmpty()) {
            sb.append(" super ");
            sb.append(String.join(", ", superBounds.stream().map(b -> b.getType().describe()).collect(Collectors.toList())));
        }
        return sb.toString();
    }

    class Bound {
        private boolean extendsBound;
        private TypeUsage type;

        private Bound(boolean extendsBound, TypeUsage type) {
            this.extendsBound = extendsBound;
            this.type = type;
        }

        public static Bound extendsBound(TypeUsage typeUsage) {
            return new Bound(true, typeUsage);
        }

        public static Bound superBound(TypeUsage typeUsage) {
            return new Bound(false, typeUsage);
        }

        public TypeUsage getType() {
            return type;
        }

        public boolean isExtends() {
            return extendsBound;
        }

        public boolean isSuper() {
            return !isExtends();
        }
    }

}
