package test.CR16C;

import vm.Address32Bit;
import vm.HardwareObject;

public class DeviceRegByte extends HardwareObject {

    public byte reg;

    public DeviceRegByte(int address) {
        super(new Address32Bit(address));
    }
}
