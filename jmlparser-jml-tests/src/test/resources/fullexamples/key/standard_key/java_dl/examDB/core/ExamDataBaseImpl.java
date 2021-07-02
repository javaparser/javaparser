package core;

public class ExamDataBaseImpl extends ExamDataBase {

    public ExamDataBaseImpl(){
	this.threshold = 2000;
	this.step = 350;
	this.maxPoints = 6000;
	this.students = new Student[100];
    }

    /*@ private normal_behavior
      @  assignable students, \object_creation(Student[]);
      @  ensures (\forall int i; 0<=i && i<students.length; 
      @               students[i] == (i<\old(students.length) 
      @                               ? \old(students)[i] 
      @                               : null));
      @  ensures students!=null && students.length > \old(students.length) && \fresh(students);
      @*/
    private void increaseStudents(){
	Student[] oldStudents = students;
	students = new Student[students.length+50];
	/*@ loop_invariant 
          @   (\forall int l; 
          @        0<=l && l<k;
          @            students[l]==oldStudents[l]) && k>=0;
	  @ assignable k, students[0..oldStudents.length-1];
	  @ decreasing oldStudents.length-k;
	  @*/	
	for(int k=0; k<oldStudents.length; k++){
	    students[k]=oldStudents[k];
	}
    }


    /*@ private behavior
      @  ensures (\exists int i; 
      @               0<=i && i<students.length && students[i]!=null
      @               && students[i].matrNr==matrNr && \result==i);
      @  assignable \object_creation(ExamDataBaseException);
      @  signals (ExamDataBaseException) 
      @      !(\exists int i; 
      @            0<=i && i<students.length && students[i]!=null
      @            && students[i].matrNr==matrNr);
      @  signals_only ExamDataBaseException;
      @*/
    private int getIndex(int matrNr) throws ExamDataBaseException{
	/*@ loop_invariant 
          @     (\forall int j; 
          @          0<=j && j<i && students[j]!=null;
          @              students[j].matrNr!=matrNr) && i>=0;
	  @ assignable i;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null && matrNr==students[i].matrNr){
		return i;
	    }
	}
	throw new ExamDataBaseException("Matriculation number not found");
    }


    /*@ public normal_behavior
      @  ensures \result==(\num_of int i; 
      @                        0<=i && i<students.length; students[i]!=null);
      @*/
    private /*@pure@*/ int countStudents(){
	int result=0;
	/*@ loop_invariant 
          @     i>=0 && result>=0 
          @     && result==(\num_of int k; 0<=k && k<i; students[k]!=null);
	  @ assignable i, result;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null){
		result++;
	    }
	}
	return result;
    }


    public void setExamParameters(int newThreshold, 
                                  int newStep, 
                                  int newMaxPoints) 
						throws ExamDataBaseException{
        if(!(0<newThreshold && newThreshold<=newMaxPoints 
           && 0<newStep && newStep<=(newMaxPoints-newThreshold)/10)) {
	    throw new ExamDataBaseException("Exam parameters inconsistent");
        }

        this.threshold = newThreshold;
        this.step = newStep;
        this.maxPoints = newMaxPoints;
    }


    public void addStudent(int matrNr, 
                           String firstname, 
                           String surname) throws ExamDataBaseException{
   	if(matrNr<=0 || firstname==null || surname==null){
	    throw new ExamDataBaseException("Tried to add invalid student");
	}
   	
	int freeIndex=-1;
	/*@ loop_invariant 
          @  (\forall int j; 
          @       0<=j && j<i && students[j]!=null;
          @           students[j].matrNr!=matrNr) 
          @   && i>=0 && freeIndex>=-1 && freeIndex<students.length
          @   && (freeIndex!=-1 ==> students[freeIndex]==null);
	  @ assignable i,freeIndex;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null){
		if(students[i].matrNr==matrNr){
		    throw new ExamDataBaseException("Tried to add already existing student");
		}
	    }else{
		freeIndex=i;
	    }
	}
	
	if(freeIndex==-1){
	    freeIndex=students.length;
	    increaseStudents();
	}
	students[freeIndex] = new Student(matrNr, firstname, surname);
    }


    public void deleteStudent(int matrNr) throws ExamDataBaseException{
	students[getIndex(matrNr)] = null;
    }


    public void setPoints(int matrNr, int points) throws ExamDataBaseException{
	if(!(-1<=points && points<=maxPoints)) {
	    throw new ExamDataBaseException("Tried to set invalid points");
	}
        students[getIndex(matrNr)].points = points;
    }


    public void setBonusPoints(int matrNr, int bonusPoints) 
						throws ExamDataBaseException{
	if(!(0<=bonusPoints && bonusPoints<=maxPoints)) {
	    throw new ExamDataBaseException("Tried to set invalid bonus points");
	}
        students[getIndex(matrNr)].bonusPoints = bonusPoints;
    }

    
    public void setBackedOut(int matrNr, boolean backedOut) 
						throws ExamDataBaseException {
	students[getIndex(matrNr)].backedOut = backedOut;
    }


    public int threshold(){
	return threshold;
    }

    
    public int step(){
 	return step;
    }
    
    
    public int maxPoints(){
	return maxPoints;
    }


    public int[] getMatrNrs(){
	int[] result = new int[countStudents()];
	int j=0;
	/*@ loop_invariant 
          @    (\forall int mnr; 
          @         (\exists int x; 
          @              0<=x && x<i && students[x]!=null 
          @              && students[x].matrNr==mnr) 
          @          <==> ((\exists int y; 
          @                    0<=y && y<j && result[y]==mnr))) 
          @    && (\forall int k,l; 
          @            0<=k && k<j && 0<=l && l<j && k!=l;
          @                result[k]!=result[l]) 
          @    && i>=0 && j>=0
          @    && j==(\num_of int k; 0<=k && k<i; students[k]!=null);
	  @ assignable i, j, result[*];
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null){
		result[j++]=students[i].matrNr;
	    }
	}
	return result;
    }


    public String getFirstname(int matrNr) throws ExamDataBaseException{
	return students[getIndex(matrNr)].firstname;
    }


    public String getSurname(int matrNr) throws ExamDataBaseException{
	return students[getIndex(matrNr)].surname;
    }


    public int getPoints(int matrNr) throws ExamDataBaseException{
	return students[getIndex(matrNr)].points;
    }

    
    public int getBonusPoints(int matrNr) throws ExamDataBaseException{
        return students[getIndex(matrNr)].bonusPoints;
    }
   

    public boolean getBackedOut(int matrNr) throws ExamDataBaseException{
	return students[getIndex(matrNr)].backedOut;
    }


    public int getGrade(int matrNr) throws ExamDataBaseException{
	int i=getIndex(matrNr);
	if(!students[i].backedOut){
	    return pointsToGrade(students[i].points, students[i].bonusPoints);
	}
	throw new ExamDataBaseException("Matriculation number not found");
    }


    public boolean consistent(){
	/*@ loop_invariant 
          @     (\forall int j; 
          @          0<=j && j<i && students[j]!=null && !students[j].backedOut; 
          @              students[j].points >= 0) && i>=0;
	  @ assignable i;
	  @ decreasing students.length-i;
	  @*/
        for(int i=0; i<students.length; i++) {
	    if(students[i] != null 
               && !students[i].backedOut 
               && students[i].points < 0) {
		return false;
	    }
	}
	return true;
    }
    
    
    public /*@pure@*/ int getNumParticipants() {
	int num=0;
        /*@ loop_invariant 
          @     i>=0 && num>=0 
          @     && num==(\num_of int j; 
          @                  0<=j && j<i; students[j]!=null 
          @                  && !students[j].backedOut);
          @ assignable i, num;
          @ decreasing students.length-i;
          @*/
        for(int i=0; i<students.length; i++){
            if(students[i]!=null && !students[i].backedOut){
        	num++;
            }
        }
        return num;
    }
    

    public int getNumWithGrade(int grade) throws ExamDataBaseException{
	if(!consistent()){ 
	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
        }
        int num=0;
	/*@ loop_invariant 
          @     i>=0 && num>=0
          @     && num==(\num_of int j;
	  @                  0<=j && j<i; students[j]!=null
          @                  && !students[j].backedOut 
          @                  && grade==pointsToGrade(students[j].points, 
	  @		                             students[j].bonusPoints));
	  @ assignable i, num;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null 
               && !students[i].backedOut){
		int g = pointsToGrade(students[i].points, 
			              students[i].bonusPoints);
		if(grade==g){
		    num++;
                }
	    }
	}
	return num;
    }


    public int getAverage() throws ExamDataBaseException{
	if(!consistent()){
	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
	}
	int sum=0;
        int num=0;
	/*@ loop_invariant 
          @     i>=0
          @     && sum==(\sum int j; 
          @                  0<=j && j<i; students[j]!=null 
          @                  && !students[j].backedOut?
          @                      pointsToGrade(students[j].points, 
          @                                    students[j].bonusPoints) : 0) 
	  @     && num==(\num_of int j;
          @                  0<=j && j<i; students[j]!=null
          @                  && !students[j].backedOut);
	  @ assignable i, sum, num;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null && !students[i].backedOut){
		sum += pointsToGrade(students[i].points, 
			             students[i].bonusPoints);
                num++;
	    }
	}
	return (num==0 ? -1 : sum/num);
    }


    public int getPassedAverage() throws ExamDataBaseException{
	if(!consistent()){ 
	    throw new ExamDataBaseException("Tried to get average in inconsistent state");
        }
	int sum=0;
	/*@ loop_invariant 
          @     i>=0
          @     && sum==(\sum int j; 
          @                  0<=j && j<i; students[j]!=null 
          @                  && !students[j].backedOut
          @                  && pointsToGrade(students[j].points,
          @                                   students[j].bonusPoints)<500?
          @                      pointsToGrade(students[j].points, 
          @                                    students[j].bonusPoints) : 0);
	  @ assignable i, sum;
	  @ decreasing students.length-i;
	  @*/
	for(int i=0; i<students.length; i++){
	    if(students[i]!=null 
               && !students[i].backedOut) {
		int grade = pointsToGrade(students[i].points, 
					  students[i].bonusPoints);
		if(grade<500) {
		    sum+=grade;
		}
	    }
	}
	int numPassed = getNumParticipants()-getNumWithGrade(500);
	return (numPassed==0 ? -1 : sum/numPassed);
    }
}
