package gui;
import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.DefaultComboBoxModel;
import javax.swing.JButton;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextField;
import javax.swing.table.DefaultTableModel;

import core.ExamDataBase;
import core.ExamDataBaseException;
import core.ExamDataBaseImpl;

/**
* This code was edited or generated using CloudGarden's Jigloo
* SWT/Swing GUI Builder, which is free for non-commercial
* use. If Jigloo is being used commercially (ie, by a corporation,
* company or business for any purpose whatever) then you
* should purchase a license for each developer using Jigloo.
* Please visit www.cloudgarden.com for details.
* Use of Jigloo implies acceptance of these licensing terms.
* A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR
* THIS MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED
* LEGALLY FOR ANY CORPORATE OR COMMERCIAL PURPOSE.
*/
public class ExamDialog extends javax.swing.JDialog {
    private DefaultTableModel examTableModel;
    private DefaultComboBoxModel numWithGradeListModel;
    private JLabel passedAverageTextLabel;
    private JLabel passedAverageLabel;
    private JLabel averageLabel;
    private JTextField maxPointsTextField;
    private JLabel numParticipantsLabel;
    private JLabel numParticipantsTextLabel;
    private JList numWithGradeList;
    private JButton newLineButton;
    private JTextField stepTextField;
    private JTextField thresholdTextField;
    private JLabel maxPointsTextLabel;
    private JLabel stepTextLabel;
    private JLabel thresholdTextLabel;
    private JScrollPane examScrollPane;
    private JButton refreshButton;
    private JLabel averageTextLabel;
    private JTable examTable;
	
    public ExamDialog(JFrame frame) {
    	super(frame);
    	initGUI();
    	thresholdTextField.setText("20.5");
    	stepTextField.setText("3");
    	maxPointsTextField.setText("60");
    	examTableModel.setColumnCount(7);
    	examTableModel.setColumnIdentifiers(new String[]{"Matrikelnr.", "Vorname", "Nachname", "Punkte", "Bonus", "Rücktritt", "Note"});
    	examTableModel.setRowCount(0);
    	examTableModel.addRow(new String[]{"123456", "Erwin", "Mustermann", "26.5", "6", "false", "?"});
    	examTableModel.addRow(new String[]{"0001", "The", "Hoff", "20", "1.5", "false", "?"});
    	examTableModel.addRow(new String[]{"830193", "Dr", "Zoidberg", "43", "14", "false", "?"});
    	examTableModel.addRow(new String[]{"777777", "Tatzel", "Wurm", "-1", "0", "true", "?"});
    	refreshButton.addActionListener(new ActionListener() {
    	    public void actionPerformed(ActionEvent e) {
    		refresh();
    	    }
    	});
    	newLineButton.addActionListener(new ActionListener() {
    	    public void actionPerformed(ActionEvent e) {
    		examTableModel.addRow(new String[]{"?", "?", "?", "-1", "0", "false", "?"});
    	    }
    	});
    	refreshButton.doClick();
    }
    
    
    /*@ private normal_behavior
      @  ensures true;
      @*/
    private /*@pure@*/ String toVisual(int i) {
	return (i==-1 ? "-" : ""+((float)i)/100);
    }
    
    
    /*@ private normal_behavior
      @  ensures true;
      @*/
    private /*@pure@*/ int toInternal(String s) {
	float f = Float.parseFloat(s);
	return (f==-1.0 ? -1 : (int)(f*100));
    }
    
    
    private void refresh() {
	try {
	    examTable.editCellAt(0, 0);
            ExamDataBase edb = new ExamDataBaseImpl();
            
            //parse and set exam parameters
            int threshold = toInternal(thresholdTextField.getText());
            int step      = toInternal(stepTextField.getText());
            int maxPoints = toInternal(maxPointsTextField.getText());
            edb.setExamParameters(threshold, step, maxPoints);
            
            //parse and add students, display grades
            for(int i=0; i<examTableModel.getRowCount(); i++) {
        	int matrNr;
        	String firstname;
        	String surname;
        	int points;
        	int bonusPoints;
        	boolean backedOut;
        	try {
                    matrNr      = Integer.parseInt((String)examTableModel.getValueAt(i, 0));
                    firstname   = (String)examTableModel.getValueAt(i, 1);
                    surname     = (String)examTableModel.getValueAt(i, 2);
                    points      = toInternal((String)examTableModel.getValueAt(i, 3));
                    bonusPoints = toInternal((String)examTableModel.getValueAt(i, 4));
                    backedOut   = examTableModel.getValueAt(i, 5).equals("true");
        	}catch(Exception exc) {
        	    examTableModel.setValueAt("nicht parsebar", i, 6);
        	    continue;
        	}
                edb.addStudent(matrNr, firstname, surname);
                edb.setPoints(matrNr, points);
                edb.setBonusPoints(matrNr, bonusPoints);
                edb.setBackedOut(matrNr, backedOut);

                if(backedOut) {
                    examTableModel.setValueAt("zurückgetreten", i, 6);
                } else if(points==-1){
                    examTableModel.setValueAt("nk", i, 6);
                } else {
                    int grade = edb.getGrade(matrNr);                             
                    examTableModel.setValueAt(""+toVisual(grade), i, 6);
                }
            }
            
            //update accumulative displays
            numWithGradeListModel.removeAllElements();
            if(edb.consistent()) {
        	int numParticipants = edb.getNumParticipants();
        	int average = edb.getAverage();
        	int passedAverage = edb.getPassedAverage();      	
                numParticipantsLabel.setText(""+numParticipants);
                averageLabel.setText(""+toVisual(average));
                passedAverageLabel.setText(""+toVisual(passedAverage));
                for(int i = 100; i <= 500; i+= (i%100==0 || i%100==70 ? 30 : 40)) {
                    int numWithGrade = edb.getNumWithGrade(i);
                    String percentWithGrade = (numParticipants == 0 ? "" : " (" + (numWithGrade*100)/numParticipants + "%)"); 
                    numWithGradeListModel.addElement(toVisual(i) + ": " + numWithGrade + percentWithGrade);
                }
                numWithGradeListModel.removeElementAt(10);
                numWithGradeListModel.removeElementAt(10);
            } else {
        	averageLabel.setText("nk");
        	passedAverageLabel.setText("nk");
        	numWithGradeListModel.addElement("nk");
            }
	} catch(ExamDataBaseException exc) {
	    System.out.println(exc.getMessage());
	}
    }
	
	

    private void initGUI() {
	//@assume false;
    	try {
	getContentPane().setLayout(null);
	this.setSize(952, 670);
    //START >>  averageTextLabel
    averageTextLabel = new JLabel();
    getContentPane().add(averageTextLabel);
BoxLayout averageTextLabelLayout = new BoxLayout(
    averageTextLabel,
    javax.swing.BoxLayout.X_AXIS);
averageTextLabel.setLayout(null);
    averageTextLabel.setText("Durchschnitt:");
    averageTextLabel.setBounds(798, 203, 84, 14);
    //END <<  averageTextLabel
//START >>  passedAverageTextLabel
passedAverageTextLabel = new JLabel();
getContentPane().add(passedAverageTextLabel);
BoxLayout jLabel1Layout = new BoxLayout(passedAverageTextLabel, javax.swing.BoxLayout.X_AXIS);
passedAverageTextLabel.setText("Durchschnitt (best.):");
passedAverageTextLabel.setLayout(null);
passedAverageTextLabel.setBounds(763, 231, 133, 14);
//END <<  passedAverageTextLabel
//START >>  averageLabel
averageLabel = new JLabel();
getContentPane().add(averageLabel);
averageLabel.setText("nk");
averageLabel.setLayout(null);
averageLabel.setBounds(889, 203, 133, 14);
//END <<  averageLabel
//START >>  passedAverageLabel
passedAverageLabel = new JLabel();
getContentPane().add(passedAverageLabel);
passedAverageLabel.setText("nk");
passedAverageLabel.setLayout(null);
passedAverageLabel.setBounds(889, 231, 133, 14);
//END <<  passedAverageLabel
//START >>  refreshButton
refreshButton = new JButton();
getContentPane().add(refreshButton);
refreshButton.setText("Aktualisieren");
refreshButton.setBounds(791, 553, 119, 28);
//END <<  refreshButton
//START >>  examScrollPane
examScrollPane = new JScrollPane();
getContentPane().add(examScrollPane);
examScrollPane.setBounds(0, 0, 756, 651);

//START >>  examTable
examTableModel = new DefaultTableModel(new String[][] { { "One", "Two" },
	{ "Three", "Four" } }, new String[] { "Column 1", "Column 2" });
examTable = new JTable();
examScrollPane.setViewportView(examTable);
examTable.setModel(examTableModel);
examTable.setBounds(0, 0, 763, 595);
examTable.setBorder(BorderFactory.createTitledBorder(""));
//END <<  examTable
//END <<  examScrollPane        	this.setSize(1009, 631);
//START >>  thresholdTextLabel
thresholdTextLabel = new JLabel();
getContentPane().add(thresholdTextLabel);
thresholdTextLabel.setText("Schwellwert:");
thresholdTextLabel.setLayout(null);
thresholdTextLabel.setBounds(777, 28, 84, 14);
//END <<  thresholdTextLabel
//START >>  stepTextLabel
stepTextLabel = new JLabel();
getContentPane().add(stepTextLabel);
stepTextLabel.setText("Schrittweite:");
stepTextLabel.setLayout(null);
stepTextLabel.setBounds(777, 70, 84, 14);
//END <<  stepTextLabel
//START >>  maxPointsTextLabel
maxPointsTextLabel = new JLabel();
getContentPane().add(maxPointsTextLabel);
maxPointsTextLabel.setText("Gesamtpunkte:");
maxPointsTextLabel.setLayout(null);
maxPointsTextLabel.setBounds(763, 112, 98, 14);
//END <<  maxPointsTextLabel
//START >>  thresholdTextField
thresholdTextField = new JTextField();
getContentPane().add(thresholdTextField);
thresholdTextField.setText("20");
thresholdTextField.setBounds(875, 21, 63, 28);
//END <<  thresholdTextField
//START >>  stepTextField
stepTextField = new JTextField();
getContentPane().add(stepTextField);
stepTextField.setText("3");
stepTextField.setBounds(875, 63, 63, 28);
//END <<  stepTextField
//START >>  maxPointsTextField
maxPointsTextField = new JTextField();
getContentPane().add(maxPointsTextField);
maxPointsTextField.setText("60");
maxPointsTextField.setBounds(875, 105, 63, 28);
//END <<  maxPointsTextField
//START >>  newLineButton
newLineButton = new JButton();
getContentPane().add(newLineButton);
newLineButton.setText("Neue Zeile");
newLineButton.setBounds(791, 595, 119, 28);
//END <<  newLineButton
//START >>  numWithGradeList
numWithGradeListModel = new DefaultComboBoxModel(new String[] {});
numWithGradeList = new JList();
getContentPane().add(numWithGradeList);
numWithGradeList.setModel(numWithGradeListModel);
numWithGradeList.setBounds(770, 273, 154, 217);
numWithGradeList.setEnabled(false);
//END <<  numWithGradeList
//START >>  numParticipantsTextLabel
numParticipantsTextLabel = new JLabel();
getContentPane().add(numParticipantsTextLabel);
numParticipantsTextLabel.setText("Teilnehmer:");
numParticipantsTextLabel.setLayout(null);
numParticipantsTextLabel.setBounds(805, 175, 84, 14);
//END <<  numParticipantsTextLabel
//START >>  numParticipantsLabel
numParticipantsLabel = new JLabel();
getContentPane().add(numParticipantsLabel);
numParticipantsLabel.setText("nk");
numParticipantsLabel.setLayout(null);
numParticipantsLabel.setBounds(889, 175, 133, 14);
//END <<  numParticipantsLabel
    	} catch (Exception e) {
    		e.printStackTrace();
    	}
    }
	

    public static void main(String[] args) {
    	JFrame frame = new JFrame();
    	ExamDialog inst = new ExamDialog(frame);
    	inst.setTitle("Klausurbewertungssystem");
    	inst.setVisible(true);
    }
}
