/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
package com.github.javaparser.ast.stmt;

import com.github.javaparser.ast.AllFieldsConstructor;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.observer.ObservableProperty;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import static com.github.javaparser.utils.Utils.assertNotNull;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.metamodel.TryStmtMetaModel;
import com.github.javaparser.metamodel.JavaParserMetaModel;
import javax.annotation.Generated;
import com.github.javaparser.TokenRange;

/**
 * The try statement.
 * <br/><pre>
 * try (InputStream i = new FileInputStream("file")) {
 *   // do things
 * } catch (IOException e) {
 *   e.printStackTrace();
 * } finally {
 *   System.out.println("Finally!!!");
 * }
 * </pre>
 * In this code, "i" is a resource, "// do things" is the content of the tryBlock,
 * there is one catch clause that catches IOException e, and there is a finally block.
 * <p>All of these are optional, but they should not all be empty or none at the same time.
 *
 * @author Julio Vilmar Gesser
 * @see CatchClause
 */
public final class TryStmt extends Statement {

    private NodeList<VariableDeclarationExpr> resources;

    private BlockStmt tryBlock;

    private NodeList<CatchClause> catchClauses;

    private BlockStmt finallyBlock;

    public TryStmt() {
        this(null, new NodeList<>(), new BlockStmt(), new NodeList<>(), null);
    }

    public TryStmt(final BlockStmt tryBlock, final NodeList<CatchClause> catchClauses, final BlockStmt finallyBlock) {
        this(null, new NodeList<>(), tryBlock, catchClauses, finallyBlock);
    }

    @AllFieldsConstructor
    public TryStmt(NodeList<VariableDeclarationExpr> resources, final BlockStmt tryBlock, final NodeList<CatchClause> catchClauses, final BlockStmt finallyBlock) {
        this(null, resources, tryBlock, catchClauses, finallyBlock);
    }

    /**This constructor is used by the parser and is considered private.*/
    @Generated("com.github.javaparser.generator.core.node.MainConstructorGenerator")
    public TryStmt(TokenRange tokenRange, NodeList<VariableDeclarationExpr> resources, BlockStmt tryBlock, NodeList<CatchClause> catchClauses, BlockStmt finallyBlock) {
        super(tokenRange);
        setResources(resources);
        setTryBlock(tryBlock);
        setCatchClauses(catchClauses);
        setFinallyBlock(finallyBlock);
        customInitialization();
    }

    @Override
    public <R, A> R accept(final GenericVisitor<R, A> v, final A arg) {
        return v.visit(this, arg);
    }

    @Override
    public <A> void accept(final VoidVisitor<A> v, final A arg) {
        v.visit(this, arg);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<CatchClause> getCatchClauses() {
        return catchClauses;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public Optional<BlockStmt> getFinallyBlock() {
        return Optional.ofNullable(finallyBlock);
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public BlockStmt getTryBlock() {
        return tryBlock;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public NodeList<VariableDeclarationExpr> getResources() {
        return resources;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TryStmt setCatchClauses(final NodeList<CatchClause> catchClauses) {
        assertNotNull(catchClauses);
        if (catchClauses == this.catchClauses) {
            return (TryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.CATCH_CLAUSES, this.catchClauses, catchClauses);
        if (this.catchClauses != null)
            this.catchClauses.setParentNode(null);
        this.catchClauses = catchClauses;
        setAsParentNodeOf(catchClauses);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TryStmt setFinallyBlock(final BlockStmt finallyBlock) {
        if (finallyBlock == this.finallyBlock) {
            return (TryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.FINALLY_BLOCK, this.finallyBlock, finallyBlock);
        if (this.finallyBlock != null)
            this.finallyBlock.setParentNode(null);
        this.finallyBlock = finallyBlock;
        setAsParentNodeOf(finallyBlock);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TryStmt setTryBlock(final BlockStmt tryBlock) {
        assertNotNull(tryBlock);
        if (tryBlock == this.tryBlock) {
            return (TryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.TRY_BLOCK, this.tryBlock, tryBlock);
        if (this.tryBlock != null)
            this.tryBlock.setParentNode(null);
        this.tryBlock = tryBlock;
        setAsParentNodeOf(tryBlock);
        return this;
    }

    @Generated("com.github.javaparser.generator.core.node.PropertyGenerator")
    public TryStmt setResources(final NodeList<VariableDeclarationExpr> resources) {
        assertNotNull(resources);
        if (resources == this.resources) {
            return (TryStmt) this;
        }
        notifyPropertyChange(ObservableProperty.RESOURCES, this.resources, resources);
        if (this.resources != null)
            this.resources.setParentNode(null);
        this.resources = resources;
        setAsParentNodeOf(resources);
        return this;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetNodeListsGenerator")
    public List<NodeList<?>> getNodeLists() {
        return Arrays.asList(getCatchClauses(), getResources());
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public boolean remove(Node node) {
        if (node == null)
            return false;
        for (int i = 0; i < catchClauses.size(); i++) {
            if (catchClauses.get(i) == node) {
                catchClauses.remove(i);
                return true;
            }
        }
        if (finallyBlock != null) {
            if (node == finallyBlock) {
                removeFinallyBlock();
                return true;
            }
        }
        for (int i = 0; i < resources.size(); i++) {
            if (resources.get(i) == node) {
                resources.remove(i);
                return true;
            }
        }
        return super.remove(node);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public TryStmt removeFinallyBlock() {
        return setFinallyBlock((BlockStmt) null);
    }

    @Generated("com.github.javaparser.generator.core.node.RemoveMethodGenerator")
    public TryStmt removeTryBlock() {
        return setTryBlock((BlockStmt) null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.CloneGenerator")
    public TryStmt clone() {
        return (TryStmt) accept(new CloneVisitor(), null);
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.GetMetaModelGenerator")
    public TryStmtMetaModel getMetaModel() {
        return JavaParserMetaModel.tryStmtMetaModel;
    }

    @Override
    @Generated("com.github.javaparser.generator.core.node.ReplaceMethodGenerator")
    public boolean replace(Node node, Node replacementNode) {
        if (node == null)
            return false;
        for (int i = 0; i < catchClauses.size(); i++) {
            if (catchClauses.get(i) == node) {
                catchClauses.set(i, (CatchClause) replacementNode);
                return true;
            }
        }
        if (finallyBlock != null) {
            if (node == finallyBlock) {
                setFinallyBlock((BlockStmt) replacementNode);
                return true;
            }
        }
        for (int i = 0; i < resources.size(); i++) {
            if (resources.get(i) == node) {
                resources.set(i, (VariableDeclarationExpr) replacementNode);
                return true;
            }
        }
        if (node == tryBlock) {
            setTryBlock((BlockStmt) replacementNode);
            return true;
        }
        return super.replace(node, replacementNode);
    }
}
