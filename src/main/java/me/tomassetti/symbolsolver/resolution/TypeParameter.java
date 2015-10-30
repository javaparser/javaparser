package me.tomassetti.symbolsolver.resolution;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;

public interface TypeParameter {

    public static TypeParameter onClass(final String name, String classQName, List<Bound> bounds) {
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

    public class Bound {
        private boolean extendsBound;
        private TypeUsage type;

        public TypeUsage getType() {
            return type;
        }

        private Bound(boolean extendsBound, TypeUsage type) {
            this.extendsBound = extendsBound;
            this.type = type;
        }

        public boolean isExtends() {
            return extendsBound;
        }

        public boolean isSuper() {
            return !isExtends();
        }

        public static Bound extendsBound(TypeUsage typeUsage) {
            return new Bound(true, typeUsage);
        }

        public static Bound superBound(TypeUsage typeUsage) {
            return new Bound(false, typeUsage);
        }
    }

    public String getName();
    public boolean declaredOnClass();
    public boolean declaredOnMethod();
    public String getQNameOfDeclaringClass();
    public List<Bound> getBounds(TypeSolver typeSolver);

}
