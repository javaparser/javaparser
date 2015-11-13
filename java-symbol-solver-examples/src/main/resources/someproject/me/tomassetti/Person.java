package someproject.me.tomassetti;

public class Person {

    private String name;
    private Address address;

    public void setName(String name) {
        this.name = name;
    }

    public void setAddress(Address address) {
        this.address = address;
    }

    public String getName() {
        return name;

    }

    public Address getAddress() {
        return address;
    }
}