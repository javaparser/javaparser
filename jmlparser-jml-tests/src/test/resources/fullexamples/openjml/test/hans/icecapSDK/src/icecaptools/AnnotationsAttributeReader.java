package icecaptools;

import java.io.DataInputStream;
import java.io.IOException;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;

public class AnnotationsAttributeReader implements org.apache.bcel.classfile.AttributeReader {
	public Attribute createAttribute(int nameIndex, int length, DataInputStream in, ConstantPool constantPool) {
		AnnotationsAttribute attribute = new AnnotationsAttribute(nameIndex, length, constantPool);
		try {
			attribute.read(in, constantPool);
			return attribute;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}
}
