
public class Person {

    public static final int MASC = 0;
    public static final int FEMI = 1;

    public static final int AGE_MAX = 130;

    protected /*@ spec_public */ String name;
    protected /*@ spec_public */ String firstname;
    protected /*@ spec_public */ int age;
    protected /*@ spec_public */ int weight;
    protected /*@ spec_public */ int gender;

    // Added public to the invariants for visibility reasons
    /*@
      @ public invariant !name.equals("");
      @ public invariant !firstname.equals("");
      @ public invariant age >= 0 
      @        && age <= AGE_MAX;
      @ public constraint age >= \old(age);
      @ public invariant weight > 0;
      @ public invariant (gender == MASC) | (gender == FEMI);
      @ public constraint gender == \old(gender);
      @*/
    
    /*@ 
      @ requires !name.equals("");
      @ requires !firstname.equals("");
      @ requires age >= 0 && age <= AGE_MAX;
      @ requires weight > 0;
      @ requires (gender == MASC) | (gender == FEMI);
      @*/
    Person(String name, String firstname, int age, int weight, int gender) {
        this.name = name;
        this.firstname = firstname;
        this.age = age;
        this.weight = weight;
        this.gender = gender;
    }

    /*@ 
      @ ensures name.equals(\result);
      @*/
    public /*@ pure */ String getName() {
        return name;
    }

    /*@ 
      @ ensures firstname.equals(\result);
      @*/
    public /*@ pure */ String getFirstName() {
        return firstname;
    }

    /*@ 
      @ ensures age == \result;
      @*/
    public /*@ pure */ int getAge() {
        return age;
    }

    /*@ 
      @ ensures weight == \result;
      @*/
    public /*@ pure */ int getWeight() {
        return weight;
    }
    
    /*@ 
      @ requires \typeof(this) == \type(Person) ;
      @ requires age < AGE_MAX;
      @ ensures age == \old(age) + 1;
      @*/
    public void oneMoreYear() {
        age++;
    }

    // Commented this out because we do not have WeightNegatifException
//    /*@ 
//      @ normal_behavior
//      @   requires kgs >= 0;
//      @   assignable weight;
//      @   ensures weight == \old(weight) + kgs;
//      @   ensures weight >= \old(weight);
//      @ also
//      @ normal_behavior
//      @   requires kgs < 0;
//      @   requires weight + kgs > 0;
//      @   assignable weight;
//      @   ensures weight == \old(weight) + kgs;
//      @   ensures weight < \old(weight);
//      @ also
//      @ exceptional_behavior
//      @   requires weight + kgs <= 0;
//      @   assignable \nothing;
//      @   signals (WeightNegatifException) weight == \old(weight);
//      @*/
//    public void modifWeight(int kgs) throws WeightNegatifException {
//        if (weight + kgs <= 0) {
//            throw new WeightNegatifException();
//        }
//        weight = weight + kgs;
//    }

    /*@ also
      @ ensures \result != null;
      @*/
    public String toString() {
        return firstname + " " + name + " is" + (gender == MASC ? " man ": " women ") + " aged " + age + " years and weighing " + weight + " kg";
    }
}