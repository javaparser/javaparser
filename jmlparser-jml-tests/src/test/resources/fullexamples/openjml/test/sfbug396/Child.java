
public class Child extends Person {
    protected /*@ spec_public */ Person father;
    protected /*@ spec_public */ Person mother;
    
    // Added public to the invariants for visibility reasons
    /*@
      @ public invariant age + 15 <= father.getAge();
      @ public invariant age + 15 <= mother.getAge();
      @ public invariant name.equals(father.getName()) | name.equals(mother.getName());
      @*/

    /*@ 
      @ requires !fath.equals(moth);
      @ ensures !this.equals(fath);
      @ ensures !this.equals(moth);
      @*/
    Child(String name, String prename, int age, int weight, int gender, Person fath, Person moth) {
        super(name, prename, age, weight, gender);
        this.father = fath;
        this.mother = moth;
    }
    
    /*@ also
      @ requires \typeof(this) == \type(Child);
      @ requires age < AGE_MAX;
      @ requires father.age < AGE_MAX;
      @ requires mother.age < AGE_MAX;
      @ ensures age == \old(age) + 1;
      @ ensures father.age == \old(father.age) + 1;
      @ ensures mother.age == \old(mother.age) + 1;
      @*/
    public void oneMoreYear() {
        age++;
        father.oneMoreYear();
        mother.oneMoreYear();
    }
    
    /*@ also
      @ ensures \result != null;
      @*/
    public String toString() {
        return super.toString() + 
            "\n father = " + father +
            "\n mother = " + mother;
    }
}