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
 * This class represents a stub file. The stub file is a Java file, but with the optionally omitted
 * information that is not relevant to pluggable type-checking; this makes the stub file smaller
 * and easier for people to read and write.
 * </p>
 * A stub unit contains the list of compilation units.
 * This class copied the {@link CompilationUnit} and then adjusted to the needs of the Checker Framework.
 *
 * @see CompilationUnit
 */
public class StubUnit extends Node {

    /**
     * The field represents a list of compilations units.
     */
    private NodeList<CompilationUnit> compilationUnits;

    /** Contains the information about where this stub unit was loaded from, or empty if it wasn't loaded from a file.*/
    @InternalProperty
    private StubUnit.Storage storage;

    /**
     * The constructor that takes the tokenRange and just pass it to the super method {@link Node}.
     *
     * @param tokenRange is the range of tokens covered by this stub unit.
     */
    protected StubUnit(TokenRange tokenRange) {
        super(tokenRange);
    }

    /**
     * The constructor that takes the list of compilation units.
     *
     * @param compilationUnits - the list of compilation units in the stub file.
     */
    public StubUnit(NodeList<CompilationUnit> compilationUnits) {
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

    /** @return information about where this stub unit was loaded from, or empty if it wasn't loaded from a file.*/
    public Optional<StubUnit.Storage> getStorage() {
        return Optional.ofNullable(storage);
    }

    public StubUnit setStorage(Path path) {
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
     * Information about where this stub unit was loaded from.
     * This class only stores the absolute location.
     * For more flexibility use SourceRoot.
     */
    public static class Storage {

        /** An stub unit that it represents. */
        private final StubUnit stubUnit;

        /** The path to the source for this stub unit. */
        private final Path path;

        /**
         * The constructor with all fields.
         *
         * @param stubUnit is the stub unit that it describes.
         * @param path to the source for this stub unit.
         */
        private Storage(StubUnit stubUnit, Path path) {
            this.stubUnit = stubUnit;
            this.path = path.toAbsolutePath();
        }

        /** @return the path to the source for this StubUnit. */
        public Path getPath() {
            return path;
        }

        /** @return the StubUnit this Storage is about. */
        public StubUnit getStubUnit() {
            return stubUnit;
        }

        /** @return the file name of the stub file that represented by the StubUnit. */
        public String getFileName() {
            return path.getFileName().toString();
        }

        /** @return the directory with the stub file that represented by the StubUnit. */
        public Path getDirectory() {
            return path.getParent();
        }

        /** Saves the stub unit to its original location.*/
        public void save() {
            save(cu -> new PrettyPrinter().print(getStubUnit()));
        }

        /** Saves the stub unit to its original location and give the output.*/
        public void save(Function<StubUnit, String> makeOutput) {
            try {
                Files.createDirectories(path.getParent());
                final String code = makeOutput.apply(getStubUnit());
                Files.write(path, code.getBytes(UTF8));
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }
}
