package icecaptools;

import java.io.DataInputStream;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;
import java.util.HashMap;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.AnnotationEntry;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ElementValue;
import org.apache.bcel.classfile.ElementValuePair;
import org.apache.bcel.classfile.RuntimeInvisibleAnnotations;
import org.apache.bcel.classfile.Visitor;

public class AnnotationsAttribute extends Attribute {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private HashMap<String, HashMap<String, String>> annotations;

	public AnnotationsAttribute(int nameIndex, int length, ConstantPool cp) {
		super(Constants.ATTR_UNKNOWN, nameIndex, length, cp);
		annotations = new HashMap<String, HashMap<String, String>>();
	}

	public void read(DataInputStream in, ConstantPool cp) throws IOException {
		short numAnnotations = in.readShort();
		for (int i = 0; i < numAnnotations; i++) {
			short typeIndex = in.readShort();
			String type = cp.constantToString(cp.getConstant(typeIndex));
			HashMap<String, String> nvPairs = new HashMap<String, String>();
			annotations.put(type.replace("/", "."), nvPairs);

			short numElementValuePairs = in.readShort();
			for (int j = 0; j < numElementValuePairs; j++) {
				short nameIndex = in.readShort();
				String name = cp.constantToString(cp.getConstant(nameIndex));
				byte tag = in.readByte();
				if (tag == 's') {
					short constValueIndex = in.readShort();
					String value = cp.constantToString(cp.getConstant(constValueIndex));
					nvPairs.put(name, value);
				} else if (tag == 'e') {
					in.readShort();
					in.readShort();
				} else {
					throw new UnsupportedOperationException("Unknown attribute type attributes");
				}
			}
		}
	}

	public static AnnotationsAttribute getAttribute(
			RuntimeInvisibleAnnotations attribute) {
		AnnotationsAttribute aattr = new AnnotationsAttribute(attribute.getNameIndex(), attribute.getLength(), attribute.getConstantPool());
		int numAnnotations = attribute.getNumAnnotations();
		for (int i = 0; i < numAnnotations; i++) {
			AnnotationEntry ae = attribute.getAnnotationEntries()[i];
			String type = ae.getAnnotationType();
			
			HashMap<String, String> nvPairs = new HashMap<String, String>();
			aattr.annotations.put(type.replace("/", "."), nvPairs);

			int numElementValuePairs  = ae.getNumElementValuePairs();
			
			for (int j = 0; j < numElementValuePairs; j++) {
				ElementValuePair nextPair = ae.getElementValuePairs()[j];
				String name = nextPair.getNameString();
				ElementValue evalue = nextPair.getValue();
				String value = evalue.stringifyValue();
				nvPairs.put(name, value);
			}
		}
		return aattr;
	}
	
	@Override
	public void accept(Visitor v) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Attribute copy(ConstantPool _constant_pool) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return annotations.toString();
	}

	@SuppressWarnings("unchecked")
	public <A extends Annotation> A getAnnotation(Class<A> annotationClass) {
		String key = "L" + annotationClass.getName().replace("/", ".") + ";";
		final HashMap<String, String> nvPairs = annotations.get(key);

		if (nvPairs == null)
			return null;

		InvocationHandler handler = new InvocationHandler() {
			public Object invoke(Object proxy, java.lang.reflect.Method m, Object[] args) throws Throwable {
				return nvPairs.get(m.getName());
			}
		};

		return (A) Proxy.newProxyInstance(getClass().getClassLoader(), new Class[] { annotationClass }, handler);
	}
}
