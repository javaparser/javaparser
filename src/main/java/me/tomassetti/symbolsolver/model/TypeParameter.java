package me.tomassetti.symbolsolver.model;

public interface TypeParameter {

    public String getName();
    public boolean declaredOnClass();
    public boolean declaredOnMethod();
    public String getQNameOfDeclaringClass();

}
