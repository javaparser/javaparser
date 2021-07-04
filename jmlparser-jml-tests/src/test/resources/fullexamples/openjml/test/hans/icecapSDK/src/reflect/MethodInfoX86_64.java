package reflect;

import icecaptools.IcecapCVar;
import icecaptools.IcecapCompileMe;
import vm.Address;
import vm.Address64Bit;

public class MethodInfoX86_64 extends MethodInfo {
	@IcecapCVar(expression = "methods", requiredIncludes = "#include \"types.h\"\nextern const MethodInfo *methods;\n")
	protected static long methods;

	public long handlers;
	public long code;
	public long nativeFunc;
	public long name;

	@IcecapCompileMe
	public MethodInfoX86_64(short index) {
		super(null);
		address = new Address64Bit(memory_size() * index + methods);
	}

	protected byte memory_size() {
		return 43;
	}
	
	@Override
	protected Address getNameRef() {
		return new Address64Bit(name);
	}

	public MethodInfoX86_64(Address address) {
		super(address);
	}
}
