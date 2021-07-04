    public class GenericBug {
    
    
        //@ requires me != null;
        public void nomutate(ReadableValue<Integer> me){
    
    	int foo = me.getValue();
        }
    
        public static void main(String args[]){
    
    	ReadableValue<Integer> r = new ReadableValue<Integer>(new Integer(0));
    
    	GenericBug b = new GenericBug();
    
    
    	b.nomutate(r);
    
        }
    
    }


     class ReadableValue<T> {
        protected /*@ spec_public @*/ T value;
    
        //@ ensures this.value == value;
        //@ ensures this.value != null;
        //@ requires value != null;
        //@ assignable \nothing;
        public ReadableValue(T value){
    	this.value = value;
        }
    
        //@ ensures \result == this.value;
        public /*@ pure @*/ T getValue(){
    	return value;
        }
    }

