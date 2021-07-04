package reflect;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import vm.Address;
import vm.Address64Bit;

public class ClassInfoX86_64 extends ClassInfo {
	@IcecapCVar(expression = "classes", requiredIncludes = "#include \"types.h\"\n#include \"classes.h\"\nextern const ClassInfo *classes;\n")
	protected static long classes;

	public long interfaces;
	public long name;
	public long references;

	@IcecapCompileMe
	public ClassInfoX86_64(short index) {
		super(null);
		address = new Address64Bit(memory_size() * index + classes);
	}

	@Override
	@IcecapCompileMe
	protected short getIndex() {
		return (short) ((((Address64Bit)address).address - classes) / memory_size());
	}

	public byte memory_size() {
		if (gCSupported()) {
			return 32;
		} else {
			return 24;
		}
	}

	@Override
	protected Address getNameRef() {
		return new Address64Bit(name);
	}

	@Override
	protected Address getReferencesRef() {
		return new Address64Bit(references);
	}

	@Override
	public Address getInterfacesRef() {
		return new Address64Bit(interfaces);
	}
}
