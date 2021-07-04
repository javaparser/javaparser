package reflect;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import vm.Address;
import vm.Address32Bit;

public class MethodInfoX86_32 extends MethodInfo {
	@IcecapCVar(expression = "methods", requiredIncludes = "#include \"types.h\"\nextern const MethodInfo *methods;\n")
	protected static int methods;

	public int handlers;
	public int code;
	public int nativeFunc;
	public int name;

	@IcecapCompileMe
	protected MethodInfoX86_32(short index) {
		super(null);
		address = new Address32Bit(memory_size() * index + methods);
	}

	protected byte memory_size() {
		return 27;
	}

	@Override
	protected Address getNameRef() {
		return new Address32Bit(name);
	}

	public MethodInfoX86_32(Address address) {
		super(address);
	}
}
