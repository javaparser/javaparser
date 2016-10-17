package me.tomassetti.symbolsolver.javaparsermodel.contexts;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.ImportDeclaration;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.QualifiedNameExpr;
import me.tomassetti.symbolsolver.model.declarations.MethodDeclaration;
import me.tomassetti.symbolsolver.model.declarations.ValueDeclaration;
import me.tomassetti.symbolsolver.model.resolution.SymbolReference;
import me.tomassetti.symbolsolver.model.resolution.TypeSolver;
import me.tomassetti.symbolsolver.model.usages.typesystem.Type;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserClassDeclaration;
import me.tomassetti.symbolsolver.javaparsermodel.declarations.JavaParserInterfaceDeclaration;
import me.tomassetti.symbolsolver.resolution.MethodResolutionLogic;
import me.tomassetti.symbolsolver.resolution.SymbolSolver;

import java.util.List;


public class CompilationUnitContext extends AbstractJavaParserContext<CompilationUnit> {

    public CompilationUnitContext(CompilationUnit wrappedNode, TypeSolver typeSolver) {
        super(wrappedNode, typeSolver);
    }

    private static boolean isQualifiedName(String name) {
        return name.contains(".");
    }

    @Override
    public SymbolReference<? extends ValueDeclaration> solveSymbol(String name, TypeSolver typeSolver) {

        // solve absolute references
        String itName = name;
        while (itName.contains(".")) {
            String typeName = getType(itName);
            String memberName = getMember(itName);
            SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> type = this.solveType(typeName, typeSolver);
            if (type.isSolved()) {
                return new SymbolSolver(typeSolver).solveSymbolInType(type.getCorrespondingDeclaration(), memberName);
            } else {
                itName = typeName;
            }
        }

        // Look among statically imported values
        if (wrappedNode.getImports() != null) {
            for (ImportDeclaration importDecl : wrappedNode.getImports()) {
                if (importDecl.isStatic()) {
                    if (importDecl.isAsterisk()) {
                        if (importDecl.getName() instanceof QualifiedNameExpr) {
                            String qName = importDecl.getName().toString();
                            me.tomassetti.symbolsolver.model.declarations.TypeDeclaration importedType = typeSolver.solveType(qName);
                            SymbolReference<? extends ValueDeclaration> ref = new SymbolSolver(typeSolver).solveSymbolInType(importedType, name);
                            if (ref.isSolved()) {
                                return ref;
                            }
                        } else {
                            throw new UnsupportedOperationException("B");
                        }
                    } else {
                        if (importDecl.getName() instanceof QualifiedNameExpr) {
                            String qName = importDecl.getName().toString();
                            // split in field/method name and type name
                            String typeName = getType(qName);
                            String memberName = getMember(qName);

                            if (memberName.equals(name)) {
                                me.tomassetti.symbolsolver.model.declarations.TypeDeclaration importedType = typeSolver.solveType(typeName);
                                return new SymbolSolver(typeSolver).solveSymbolInType(importedType, memberName);
                            }
                        } else {
                            throw new UnsupportedOperationException("C");
                        }
                    }
                }
            }
        }

        return SymbolReference.unsolved(ValueDeclaration.class);
    }

    private String getType(String qName) {
        int index = qName.lastIndexOf('.');
        if (index == -1) {
            throw new UnsupportedOperationException();
        }
        String typeName = qName.substring(0, index);
        return typeName;
    }

    private String getMember(String qName) {
        int index = qName.lastIndexOf('.');
        if (index == -1) {
            throw new UnsupportedOperationException();
        }
        String memberName = qName.substring(index + 1);
        return memberName;
    }

    @Override
    public SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> solveType(String name, TypeSolver typeSolver) {
        if (wrappedNode.getTypes() != null) {
            for (TypeDeclaration type : wrappedNode.getTypes()) {
                if (type.getName().equals(name)) {
                    if (type instanceof ClassOrInterfaceDeclaration) {
                        if (((ClassOrInterfaceDeclaration) type).isInterface()) {
                            return SymbolReference.solved(new JavaParserInterfaceDeclaration((ClassOrInterfaceDeclaration) type, typeSolver));
                        } else {
                            return SymbolReference.solved(new JavaParserClassDeclaration((ClassOrInterfaceDeclaration) type, typeSolver));
                        }
                    } else {
                        throw new UnsupportedOperationException();
                    }
                }
            }
        }

        if (wrappedNode.getImports() != null) {
            for (ImportDeclaration importDecl : wrappedNode.getImports()) {
                if (!importDecl.isStatic()) {
                    if (!importDecl.isAsterisk()) {
                        if (importDecl.getName() instanceof QualifiedNameExpr) {
                            String qName = importDecl.getName().toString();
                            if (qName.equals(name) || qName.endsWith("." + name)) {
                                SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                                if (ref.isSolved()) {
                                    return ref;
                                }
                            }
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    } else {
                        String qName = importDecl.getName().toString() + "." + name;
                        SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
                        if (ref.isSolved()) {
                            return ref;
                        }
                    }
                }
            }
        }

        // Look in current package
        if (this.wrappedNode.getPackage() != null) {
            String qName = this.wrappedNode.getPackage().getName().toString() + "." + name;
            SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType(qName);
            if (ref.isSolved()) {
                return ref;
            }
        }

        // Look in the java.lang package
        SymbolReference<me.tomassetti.symbolsolver.model.declarations.TypeDeclaration> ref = typeSolver.tryToSolveType("java.lang." + name);
        if (ref.isSolved()) {
            return ref;
        }

        // DO NOT look for absolute name if this name is not qualified: you cannot import classes from the default package
        if (isQualifiedName(name)) {
            return typeSolver.tryToSolveType(name);
        } else {
            return SymbolReference.unsolved(me.tomassetti.symbolsolver.model.declarations.TypeDeclaration.class);
        }
    }

    @Override
    public SymbolReference<MethodDeclaration> solveMethod(String name, List<Type> parameterTypes, TypeSolver typeSolver) {
        if (wrappedNode.getImports() != null) {
            for (ImportDeclaration importDecl : wrappedNode.getImports()) {
                if (importDecl.isStatic()) {
                    if (importDecl.isAsterisk()) {
                        if (importDecl.getName() instanceof QualifiedNameExpr) {
                            String qName = importDecl.getName().toString();
                            me.tomassetti.symbolsolver.model.declarations.TypeDeclaration ref = typeSolver.solveType(qName);
                            SymbolReference<MethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, parameterTypes, typeSolver);
                            if (method.isSolved()) {
                                return method;
                            }
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    } else {
                        if (importDecl.getName() instanceof QualifiedNameExpr) {
                            String qName = importDecl.getName().toString();
                            if (qName.equals(name) || qName.endsWith("." + name)) {
                                String typeName = getType(qName);
                                me.tomassetti.symbolsolver.model.declarations.TypeDeclaration ref = typeSolver.solveType(typeName);
                                SymbolReference<MethodDeclaration> method = MethodResolutionLogic.solveMethodInType(ref, name, parameterTypes, typeSolver);
                                if (method.isSolved()) {
                                    return method;
                                }
                            }
                        } else {
                            throw new UnsupportedOperationException();
                        }
                    }
                }
            }
        }
        return SymbolReference.unsolved(MethodDeclaration.class);
    }
}
