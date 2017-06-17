package com.github.javaparser.ast;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParseStart;
import com.github.javaparser.TokenRange;
import com.github.javaparser.ast.visitor.GenericVisitor;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.metamodel.InternalProperty;
import com.github.javaparser.printer.PrettyPrinter;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static com.github.javaparser.Providers.UTF8;
import static com.github.javaparser.Providers.provider;

public class IndexUnit extends Node {

    private NodeList<CompilationUnit> compilationUnits;

    @InternalProperty
    private IndexUnit.Storage storage;

    protected IndexUnit(TokenRange tokenRange) {
        super(tokenRange);
    }

    public IndexUnit(NodeList<CompilationUnit> compilationUnits) {
        super(null);
        this.compilationUnits = compilationUnits;
    }

    public List<CompilationUnit> getCompilationUnits() {
        return compilationUnits;
    }

    public void setCompilationUnits(NodeList<CompilationUnit> compilationUnits) {
        this.compilationUnits = compilationUnits;
    }

    /**
     * @return information about where this compilation unit was loaded from, or empty if it wasn't loaded from a file.
     */
    public Optional<IndexUnit.Storage> getStorage() {
        return Optional.ofNullable(storage);
    }

    public IndexUnit setStorage(Path path) {
        this.storage = new Storage(this, path);
        return this;
    }

    //TODO add a visit method
    @Override
    public <R, A> R accept(GenericVisitor<R, A> v, A arg) {
        return null; //v.visit(this, arg);
    }

    //TODO add a visit method
    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        // v.visit(this, arg);
    }

    /**
     * Information about where this compilation unit was loaded from.
     * This class only stores the absolute location.
     * For more flexibility use SourceRoot.
     */
    public static class Storage {

        private final IndexUnit indexUnit;

        private final Path path;

        private Storage(IndexUnit compilationUnit, Path path) {
            this.indexUnit = compilationUnit;
            this.path = path.toAbsolutePath();
        }

        /**
         * @return the path to the source for this CompilationUnit
         */
        public Path getPath() {
            return path;
        }

        /**
         * @return the CompilationUnit this Storage is about.
         */
        public IndexUnit getIndexUnit() {
            return indexUnit;
        }

        public String getFileName() {
            return path.getFileName().toString();
        }

        public Path getDirectory() {
            return path.getParent();
        }

        /**
         * Saves the compilation unit to its original location
         */
        public void save() {
            save(cu -> new PrettyPrinter().print(getIndexUnit()));
        }

        public void save(Function<IndexUnit, String> makeOutput) {
            try {
                Files.createDirectories(path.getParent());
                final String code = makeOutput.apply(getIndexUnit());
                Files.write(path, code.getBytes(UTF8));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        public ParseResult<IndexUnit> reparse(JavaParser javaParser) {
            try {
                return javaParser.parse(ParseStart.INDEX_UNIT, provider(getPath()));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
