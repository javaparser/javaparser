package reflect;

import vm.Address;
import vm.Address32Bit;
import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;

public class ClassInfoX86_32 extends ClassInfo {
	@IcecapCVar(expression = "classes", requiredIncludes = "#include \"types.h\"\n#include \"classes.h\"\nextern const ClassInfo *classes;\n")
	protected static int classes;
	
	public int interfaces;
	public int name;
	public int references;
	
	@IcecapCompileMe
	protected ClassInfoX86_32(short index) {
		super(null);
		address = new Address32Bit(memory_size() * index + classes);
	}

	@Override
	@IcecapCompileMe
	protected short getIndex() {
		return (short) ((((Address32Bit)address).address - classes) / memory_size());
	}
	
	protected byte memory_size() {
		if (gCSupported()) {
			return 20;
		} else {
			return 16;
		}
	}

	@Override
	protected Address getNameRef() {
		return new Address32Bit(name);
	}

	@Override
	protected Address getReferencesRef() {
		return new Address32Bit(references);
	}

	@Override
	public Address getInterfacesRef() {
		return new Address32Bit(interfaces);
	}
}
