package vm;

public abstract class Address {

	public abstract void inc();

	public abstract void add(int i);

	public abstract boolean isNull();

	public abstract void sub(int offset);
}
