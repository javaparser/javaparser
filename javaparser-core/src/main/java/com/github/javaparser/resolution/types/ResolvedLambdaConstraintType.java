package com.github.javaparser.resolution.types;

public class ResolvedLambdaConstraintType implements ResolvedType {
    private ResolvedType bound;

    private ResolvedLambdaConstraintType(ResolvedType bound) {
        this.bound = bound;
    }

    @Override
    public String describe() {
        return "? super " + bound.describe();
    }

    public ResolvedType getBound() {
        return bound;
    }

    @Override
    public boolean isConstraint() {
        return true;
    }

    @Override
    public ResolvedLambdaConstraintType asConstraintType() {
        return this;
    }

    public static ResolvedLambdaConstraintType bound(ResolvedType bound){
        return new ResolvedLambdaConstraintType(bound);
    }

    @Override
    public boolean isAssignableBy(ResolvedType other) {
        return bound.isAssignableBy(other);
    }

    @Override
    public String toString() {
        return "LambdaConstraintType{" +
                "bound=" + bound +
                '}';
    }
}