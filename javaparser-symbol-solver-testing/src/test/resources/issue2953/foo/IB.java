package foo;
public interface IB {
    Integer getCode();

    default boolean equalByCode(Integer code) {
        return getCode().equals(code);
    }
}