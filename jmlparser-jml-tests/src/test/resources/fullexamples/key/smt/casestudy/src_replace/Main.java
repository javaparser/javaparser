package system;


import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.util.LinkedList;
import java.util.List;

public class Main {

	 public static void main(String []  args){
		 String input = args[0];
		 String output = args[1];
		 boolean std = args.length >=3;
		 

		 List<String> lines = read(input);		 
		 int bitInt = std ? 10 : readPositiveInteger("BIT_INT: ");
	     int bitHeap = std ? 3 : readPositiveInteger("BIT_HEAP: ");
	     int bitField = std ? 6 :readPositiveInteger("BIT_FIELD: ");
	     int bitObject = std ? 8 :readPositiveInteger("BIT_OBJECT: ");
	     List<String> newLines = new LinkedList<String>();
	     for(String line : lines){
	    	 line = replace(line,"#BIT_INT",Integer.toString(bitInt));
	    	 line = replace(line,"#BIT_HEAP",Integer.toString(bitHeap));
	    	 line = replace(line,"#BIT_FIELD",Integer.toString(bitField));
	    	 line = replace(line,"#BIT_OBJECT",Integer.toString(bitObject));
	    	 line = replaceOp(line,"<= ", "bvsle ");
	    	 line = replaceOp(line,">= ", "bvsge ");
	    	 line = replaceOp(line,"\\+ ", "bvadd ");
	    	 line = replaceOp(line,"\\* ", "bvmul ");
	    	 line = replaceOp(line,"- ", "bvsub ");
	    	 line = replaceOp(line,"\\(> ", "(bvsgt ");
	    	 line = replaceOp(line,"\\(< ", "(bvslt ");
	    	 line = replaceConstants(line, bitInt);
	    	 newLines.add(line);
	     }
		 write(newLines, output);
		 
	 }
	 
	 private static String replaceOp(String line, String dest, String val) {
		 return  line.replaceAll(dest, val);
	}

	public static String replaceConstants(String line, int bitInt){
		 String []words = line.split(" ");
		 StringBuffer newWords = new StringBuffer();
		 for(String word : words){
			 Integer constant;
			 if((constant = toInteger(word))!=null){
				 String binary = Integer.toBinaryString(constant);
				 if(binary.length() > bitInt){
					 throw new RuntimeException("bit vector too small!");
				 }
				 for(int i= binary.length(); i < bitInt; i++){
					binary = "0"+binary; 
				 }				 
				 word = "#b"+binary;
			 }
			 newWords.append(word+" ");
		 }
		 newWords.replace(newWords.length()-1, newWords.length(), "");
		 return newWords.toString();
	 }
	 
	 public static Integer toInteger(String s){
		 try{
			 return Integer.parseInt(s);
			 
		 }catch(Throwable e){
			 return null;
		 }
	 }

	 
	 
	 
	 public static String replace(String line, String dest, String val){
		 return  line.replaceAll(dest, "(_ BitVec "+ val+")");
	 }
	 
	 public static void write(List<String> lines, String output){
		 try{
			 BufferedWriter writer = new BufferedWriter(new FileWriter(new File(output)));
			 for(String line : lines){
				 writer.write(line);
				 writer.write("\n");
			 }
			 writer.flush();
			 writer.close();
		 }catch(Throwable e){
			 throw new RuntimeException(e);
		 }
	 }
	 
	 public static List<String> read(String input){
		 try{
			 LinkedList<String> lines = new LinkedList<String>();
			 BufferedReader reader = new BufferedReader(new FileReader(new File(input)));
			 for(String line = reader.readLine(); line != null; line = reader.readLine()){
				 lines.add(line);
			 }
			 return lines;
		 }catch(Throwable e){
			 throw new RuntimeException(e);
		 }
	 }
	 
	 public static String readLine(){
	      BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

	      String line = null;
	      try {
	         line = br.readLine();
	      } catch (Throwable e) {
	        throw new RuntimeException(e);
	      }
	      return line;
	 }
	 
	 public static int readPositiveInteger(String title){
		 for(;;){
			 try{
				 System.out.print(title);
				 int val = readInteger();
				 if(val >0){
					 return val;
				 }
			 }catch(Throwable e){
				 // repeat loop.
			 }
		 }		  
	 }
	 
	 public static int readInteger(){
		 return Integer.parseInt(readLine());
	 }
}
