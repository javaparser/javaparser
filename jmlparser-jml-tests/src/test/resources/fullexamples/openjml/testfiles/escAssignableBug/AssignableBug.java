public class AssignableBug {

    public int xSize;
    
  public Piece piece;
  
  //@ requires pp.position.x >= 0 && pp.position.x < xSize;
  //@ ensures piece == pp;
  //@ pure
  public AssignableBug(Piece pp, int xSize) {
      piece = pp;
      this.xSize = xSize;
  }

  //@ public invariant piece.position.x >= 0 && piece.position.x < xSize;
  
  //@ normal_behavior
  //@ requires inRange(p);
  //@ assignable piece.position;
  public void test(Position p) {
    piece.setPosition(p);
    //@ assert inRange(piece.position);
  }
  
  //@ ensures \result == ( p.x >= 0 && p.x < xSize );
  //@ pure helper
  public boolean inRange(Position p) {
      return p.x >= 0 && p.x < xSize;
  }
}

class Piece {
   public Position position;

   //@ ensures position == p;
   //@ pure
   public Piece(Position p) {
      position = p;
   }

   //@ normal_behavior
   //@ assignable position;
   //@ ensures position == p;
   public void setPosition(Position p) {
      position = p;
   }
}

class Position {
   public int x;
}
