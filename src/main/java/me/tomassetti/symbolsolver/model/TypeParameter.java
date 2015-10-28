package me.tomassetti.symbolsolver.model;

import me.tomassetti.symbolsolver.model.typesystem.TypeUsage;

import java.util.List;

public interface TypeParameter {

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
