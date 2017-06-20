package com.github.javaparser.ast;

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

/**
 * <p>
 * This class represents an index unit with a list of compilation units. Each stub file represented with an
 * index unit.
 * </p>
 * A index unit contains the list of compilation units.
 * This class copied the {@link CompilationUnit} and then adjusted to the needs of the Checker Framework.
 *
 * @see CompilationUnit
 */
public class IndexUnit extends Node {

    /**
     * The field represents a list of compilations units.
     */
    private NodeList<CompilationUnit> compilationUnits;

    /** Contains the information about where this index unit was loaded from, or empty if it wasn't loaded from a file.*/
    @InternalProperty
    private IndexUnit.Storage storage;

    /**
     * The constructor that takes the tokenRange and just pass it to the super method {@link Node}.
     *
     * @param tokenRange is the range of tokens covered by this index unit.
     */
    protected IndexUnit(TokenRange tokenRange) {
        super(tokenRange);
    }

    /**
     * The constructor that takes the list of compilation units.
     *
     * @param compilationUnits - the list of compilation units in the stub file.
     */
    public IndexUnit(NodeList<CompilationUnit> compilationUnits) {
        super(null);
        this.compilationUnits = compilationUnits;
    }

    /** The getter method for the list of the compilation units of the stub file. */
    public List<CompilationUnit> getCompilationUnits() {
        return compilationUnits;
    }

    /** The setter method for the list of the compilation units of the stub file. */
    public void setCompilationUnits(NodeList<CompilationUnit> compilationUnits) {
        this.compilationUnits = compilationUnits;
    }

    /** @return information about where this index unit was loaded from, or empty if it wasn't loaded from a file.*/
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
        throw new RuntimeException("The method is not implemented!");
         //v.visit(this, arg);
    }

    //TODO add a visit method
    @Override
    public <A> void accept(VoidVisitor<A> v, A arg) {
        throw new RuntimeException("The method is not implemented!");
        // v.visit(this, arg);
    }

    /**
     * Information about where this index unit was loaded from.
     * This class only stores the absolute location.
     * For more flexibility use SourceRoot.
     */
    public static class Storage {

        /** An index unit that it represents. */
        private final IndexUnit indexUnit;

        /** The path to the source for this index unit. */
        private final Path path;

        /**
         * The constructor with all fields.
         *
         * @param indexUnit is the index unit that it describes.
         * @param path to the source for this index unit.
         */
        private Storage(IndexUnit indexUnit, Path path) {
            this.indexUnit = indexUnit;
            this.path = path.toAbsolutePath();
        }

        /** @return the path to the source for this IndexUnit. */
        public Path getPath() {
            return path;
        }

        /** @return the IndexUnit this Storage is about. */
        public IndexUnit getIndexUnit() {
            return indexUnit;
        }

        /** @return the file name of the stub file that represented by the IndexUnit. */
        public String getFileName() {
            return path.getFileName().toString();
        }

        /** @return the directory with the stub file that represented by the IndexUnit. */
        public Path getDirectory() {
            return path.getParent();
        }

        /** Saves the index unit to its original location.*/
        public void save() {
            save(cu -> new PrettyPrinter().print(getIndexUnit()));
        }

        /** Saves the index unit to its original location and give the output.*/
        public void save(Function<IndexUnit, String> makeOutput) {
            try {
                Files.createDirectories(path.getParent());
                final String code = makeOutput.apply(getIndexUnit());
                Files.write(path, code.getBytes(UTF8));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
