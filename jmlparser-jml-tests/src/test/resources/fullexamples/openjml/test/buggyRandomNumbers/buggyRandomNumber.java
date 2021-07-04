// This was partly a problem with inadequate specs, but then also a problem with the
// library specs for Collection, ArrayList, List
import java.util.Random;
import java.util.ArrayList;

public class buggyRandomNumber{

    //@ public normal_behavior
   //@ requires range > 0;
   //@ requires repeat >= 0;
   //@ ensures (\forall int k; 0 <= k && k < \result.size() ; \result.get(k) >= 0 && \result.get(k) < range);
   //@ ensures repeat == \result.size();
   public ArrayList<Integer> Generate(int range, int repeat){
      ArrayList<Integer> randomNumbers = new ArrayList<Integer>();
      int counter, selected = 0;
      Random rnum = new Random();
      System.out.println("Random Numbers:");

      //@ decreases repeat - counter;
      //@ maintaining (\lbl RS randomNumbers.size()) == (\lbl CN counter)-1;
      //@ maintaining randomNumbers.size() <= repeat;   
      //@ maintaining 0 <= selected && selected < range; 
      //@ maintaining (\forall int i; 0 <= i && i < randomNumbers.size(); 0 <= randomNumbers.get(i) && randomNumbers.get(i) <range);
      for (counter = 1; counter <= repeat; counter++) {
     selected = rnum.nextInt(range);
     randomNumbers.add(selected);
     //@ assert randomNumbers.get(randomNumbers.size()-1) == selected;
     //@ assert 0 <= randomNumbers.get(randomNumbers.size()-1);
     //@ assert randomNumbers.get(randomNumbers.size()-1) < range;
      }
      //@ assert randomNumbers.size() == repeat && counter-1 == repeat;
      return randomNumbers;
    }
   
   //@ public normal_behavior
   //@ requires range > 0;
   //@ requires repeat >= 0;
   //@ ensures (\forall int k; 0 <= k && k < \result.size() ; \result.get(k) >= 0 && \result.get(k) < range);
   //@ ensures repeat == \result.size();
   public ArrayList<Integer> GenerateBad(int range, int repeat){
      ArrayList<Integer> randomNumbers = new ArrayList<Integer>();
      int counter, selected = 0;
      Random rnum = new Random();
      System.out.println("Random Numbers:");

      //@ decreases repeat - counter;
      //@ maintaining randomNumbers.size() == counter-1;
      //@ maintaining randomNumbers.size() <= repeat;   
      //@ maintaining 0 <= selected && selected < range; 
      //@ maintaining (\forall int i; 0 <= i && i < randomNumbers.size(); 0 <= randomNumbers.get(i) && randomNumbers.get(i) <range);
      for (counter = 1; counter <= repeat; counter++) {
     selected = rnum.nextInt(range);
     randomNumbers.add(selected);
     //@ assert randomNumbers.get(randomNumbers.size()-1) == selected;
     //@ assert 0 <= randomNumbers.get(randomNumbers.size()-1);
     //@ assert randomNumbers.get(randomNumbers.size()-1) < range;
      }
      //@ assert randomNumbers.size() == repeat && counter-1 == repeat;
      return randomNumbers;
    }
}
