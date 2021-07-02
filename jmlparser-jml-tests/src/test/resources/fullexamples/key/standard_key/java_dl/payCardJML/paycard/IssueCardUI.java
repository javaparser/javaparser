// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package paycard;

import javax.swing.JPanel;
import javax.swing.JRadioButtonMenuItem;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;


public class IssueCardUI {

    public IssueCardUI() {
        frame = new JFrame("Issue Paycard");
        desiredCardType = STANDARD;
    }

    
    public void initGUI() {
	frame.setBounds(100, 100, 550, 230);
	frame.setResizable(true);
	frame.setDefaultCloseOperation(javax.swing.JFrame.EXIT_ON_CLOSE);
	frame.getContentPane().setLayout(new BorderLayout());
	frame.getContentPane().add(new JPanel(), BorderLayout.WEST);
	frame.getContentPane().add(new JPanel(), BorderLayout.EAST);
	frame.getContentPane().add(jPanel1, BorderLayout.CENTER);
	frame.getContentPane().add(jPanel2, BorderLayout.SOUTH);
	GridLayout layout = new GridLayout(3, 1);
	jPanel1.setLayout(layout);
	jPanel2.setLayout(new GridLayout(1, 3));
	jPanel3.setLayout(new GridLayout(1, 3));
	jPanel5.setLayout(new BorderLayout());
	jPanel1.add(jRadioButton1);
	jPanel1.add(jRadioButton2);
	jPanel1.add(jPanel3,BorderLayout.SOUTH);
	jPanel3.add(jRadioButton3);
	jPanel2.add(jButton1);
	jPanel2.add(jButton2);
	jPanel4.setLayout(new BorderLayout());
	jPanel4.add(jLabel1, BorderLayout.EAST);
	jPanel3.add(jPanel4);
	jPanel5.add(new JPanel(), BorderLayout.NORTH);
	jPanel5.add(new JPanel(), BorderLayout.SOUTH);
	jPanel5.add(jTextField1, BorderLayout.CENTER);
	jPanel3.add(jPanel5);
	jRadioButton1.setText("jRadioButton1");
	jRadioButton1.setLabel("Standard Paycard");
	jRadioButton1.setSelected(true);
	jRadioButton2.setText("jRadioButton2");
	jRadioButton2.setLabel("Junior Paycard");
	jRadioButton3.setText("jRadioButton3");
	jRadioButton3.setLabel("User Defined Paycard");
	jButton1.setText("jButton1");
	jButton1.setLabel("Issue Paycard");
	jButton2.setText("jButton2");
	jButton2.setLabel("Quit");
	jTextField1.setText("1000");
	jTextField1.setMaximumSize(new Dimension(200, 10));
	jTextField1.setMinimumSize(new Dimension(200, 10));
	jTextField1.setPreferredSize(new Dimension(200, 10));
	jLabel1.setText("Limit:  ");
	jLabel1.setToolTipText("Limit of the paycard");
	ButtonGroup group = new ButtonGroup();
	group.add(jRadioButton1);
	group.add(jRadioButton2);
	group.add(jRadioButton3);
	RadioListener listener = new RadioListener();
	jRadioButton1.addActionListener(listener);
	jRadioButton2.addActionListener(listener);
	jRadioButton3.addActionListener(listener);
	frame.show();
	jButton2.addActionListener(new ActionListener(){public void actionPerformed(ActionEvent e){jButton2ActionPerformed(e);}});
	jButton1.addActionListener(new ActionListener(){public void actionPerformed(ActionEvent e){jButton1ActionPerformed(e);}});
    }
    

    public void jButton2ActionPerformed(ActionEvent e) {
        frame.dispose();
        System.exit(0);
    }

    
    public void jButton1ActionPerformed(ActionEvent e) {
	// read textfield
	int limit = 0;
	if(desiredCardType == USER_DEFINED) {
	    try {
		limit=Integer.parseInt(jTextField1.getText());
	    }
	    catch (NumberFormatException ex) {
		JOptionPane.showMessageDialog(
			frame, "Limit has to be a number!", "Error",
			JOptionPane.ERROR_MESSAGE);
		return;
	    }
	}
	frame.dispose();
	ChargeUI chargeUI = new ChargeUI(desiredCardType, limit);
        chargeUI.initGUI();
    }
    

    class RadioListener implements ActionListener{
	public void actionPerformed(ActionEvent e){
	    if(e.getActionCommand().equals("Standard Paycard")) {
		desiredCardType = STANDARD;
	    } else if(e.getActionCommand().equals("Junior Paycard")) {
		desiredCardType = JUNIOR;
	    } else if(e.getActionCommand().equals("User Defined Paycard")) {
		desiredCardType = USER_DEFINED;
	    }
	}
    }


    private JFrame frame;
    private JPanel jPanel1 = new JPanel();
    private JPanel jPanel2 = new JPanel();
    private JPanel jPanel3 = new JPanel();
    private JPanel jPanel4 = new JPanel();
    private JPanel jPanel5 = new JPanel();
    private JRadioButton jRadioButton1 = new JRadioButton();
    private JRadioButton jRadioButton2 = new JRadioButton();
    private JRadioButton jRadioButton3 = new JRadioButton();
    private JButton jButton1 = new JButton();
    private JButton jButton2 = new JButton();
    private JTextField jTextField1 = new JTextField();
    private JLabel jLabel1 = new JLabel();
    protected final static int STANDARD = 1;
    protected final static int JUNIOR = 2;
    protected final static int USER_DEFINED = 3;
    private int desiredCardType;
}
