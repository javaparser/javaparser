import java.util.function.*;

//@ non_null_by_default
public class SpecificationInterfaceDemo {

  public interface PositivePureFunction extends Function<Integer,Integer> {

    //@ also
	//@   requires x > 0;
    //@   assignable \nothing;
    //@   ensures \result != null && \result > 0;
    Integer apply(Integer x);
  }


  //@   requires z > 0; // FAILS because there are no specs to say that apply is pure
  //@   assignable \nothing;
  //@ nullable
  public Integer mbad1(Function<Integer,Integer> f, Integer z) {
    return f.apply(z);
  }

  //@   requires z > 0;
  //@   ensures \result != null && \result > 0; // FAILS becuse no specs give info about postcondition
  //@ nullable
  public Integer mbad2(Function<Integer,Integer> f, Integer z) {
    return f.apply(z);
  }

  //@   requires z > 0;
  //@   assignable f.applyFrame;
  //@   ensures \result != null && \result > 0;
  public Integer mok(/*@{ PositivePureFunction }@*/ Function<Integer,Integer> f, Integer z) {
    return f.apply(z);
  }

  int zz;

  public void mbad3(Function<Integer,Integer> f, Integer z) {
    zz = 0;
    Integer k = f.apply(z);
    //@ assert zz == 0;
  }

  //@   requires z > 0;
  public void mok2(/*@{ PositivePureFunction }@*/ Function<Integer,Integer> f, Integer z) {
    zz = 0;
    Integer k = f.apply(z);
    //@ assert zz == 0; // OK because apply is known to be pure
  }
}
