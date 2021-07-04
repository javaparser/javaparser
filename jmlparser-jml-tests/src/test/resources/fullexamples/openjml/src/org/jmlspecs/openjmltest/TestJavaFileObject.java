package org.jmlspecs.openjmltest;
import java.net.URI;

import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;

import org.jmlspecs.openjml.Utils;

/** This class makes a mock JavaFileObject.  It holds a String as its content
 * and is given a pseudo-filename to use, but does not represent an actual file in 
 * the file system. 
 * <P>
 * Note that we use Kind.OTHER to designate specification (non-.java) files.
 * 
 * @author David Cok
 */
public class TestJavaFileObject extends SimpleJavaFileObject {
    
    /** The content of the mock file */
    //@ non_null
    protected String content;
    
    /** A fake file name, used when the user does not want to be bothered
     * supplying one.  We make and cache this because it is a pain to
     * deal with exceptions in constructors.
     */
    //@ non_null
    static final protected URI uritest = makeURI();
    
    /** A utility method to make the URI, so it can handle the exceptions. 
     * We don't try to recover gracefully if the exception occurs - this is
     * just used in testing anyway. */
    private static URI makeURI() {
        try {
            return new URI("file:///TEST.java");
        } catch (Exception e) {
            System.err.println("CATASTROPHIC EXIT - FAILED TO CONSTRUCT A MOCK URI");
            System.exit(3);
            return null;
        }
    }


    // TODO - will it be a problem if someone makes two of these objects in 
    // the same test (since they will have the same name)?
    /** A constructor of a JavaFileObject of kind SOURCE,
     * with the given content and a made-up file name.
     * @param s The content of the file
     */
    public TestJavaFileObject(/*@ non_null */ String s) {
        super(uritest,Kind.SOURCE);
        content = s;
    }

    /** Constructs a new JavaFileObject of kind SOURCE or OTHER depending on the
     * filename extension
     * @param filename the filename to use (no leading slash) (null indicates to
     *          use the internal fabricated filename)
     * @param content the content of the pseudo file
     * @throws Exception if a URI cannot be created
     */
    public TestJavaFileObject(/*@ nullable */String filename, /*@ non_null */String content) throws Exception {
        // This takes three slashes because the filename is supposed to be absolute.
        // In our case this is not a real file anyway, so we pretend it is absolute.
        super(filename == null ? uritest : new URI("file:///" + filename),
                filename == null || filename.endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
        this.content = content;
    }

    /** Constructs a new JavaFileObject
     * @param uri the URI to use
     * @param content the content of the pseudo file
     */
    public TestJavaFileObject(/*@ non_null */URI uri, /*@ non_null */String content) {
        super(uri,uri.getPath().endsWith(".java") ? Kind.SOURCE : Kind.OTHER);
        this.content = content;
    }

    /** Overrides the parent to provide the content directly from the String
     * supplied at construction, rather than reading the file.  This is called
     * by the system.
     */
    @Override
    public CharSequence getCharContent(boolean ignoreEncodingErrors) {
        return content;
    }
    
    /** Overrides the parent method to allow name compatibility between 
     * pseudo files of different kinds.  TODO _ better description of what the system uses this for
     */
    // Don't worry about whether the kinds match, just the file prefix
    @Override
    public boolean isNameCompatible(String simpleName, Kind kind) {
        String s = uri.getPath();
        if (kind == Kind.OTHER) {
            int i = s.lastIndexOf('/');
            s = s.substring(i+1);
            return s.startsWith(simpleName);
        } else {
            String baseName = simpleName + kind.extension;
            return s.endsWith("/" + baseName);
        }
    }
    
    /** Returns true if the receiver and argument represent the same file */
    public boolean equals(Object o) {
        if (!(o instanceof JavaFileObject)) return false;
        return Utils.ifSourcesEqual(this, (JavaFileObject)o);
    }
    
    /** A definition of hashCode, since we have a definition of equals */
    public int hashCode() {
        // Two things are equal if they have the same string, so we'll
        // use that for the hashCode
        return uri.normalize().getPath().hashCode();
        // FIXME -0 this is not right, since if one is a suffix of the other they are equal and should have the same hashCode
    }
    
    public String toString() {
        //String s = super.toString(); // Something like file:///tt/TestJava.java from TestJavaFileObject
        String s = getName();  // Something like tt/TestJava.java
        // Note: in stack traces it appears that everything gets dropped up to and including
        // the last /
        return s;
    }

}

