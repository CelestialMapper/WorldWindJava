package gov.nasa.cms.features.moonshading;
import gov.nasa.worldwind.WorldWindow;
import javax.swing.*;
import java.awt.*;
import java.util.*;
/**
 * shows the time
 * @author hniyer
 */
public class ShowTimeJSpinner{

    private static ShowTimeJSpinner time;
    
   
     private JFrame calendar;
     
	public ShowTimeJSpinner(){
		this.calendar = new JFrame("Creating JSpinner Component with time");
		this.calendar.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		Date date = new Date();
		SpinnerDateModel sm = new SpinnerDateModel(date, null, null, Calendar.HOUR_OF_DAY);
		JSpinner spinner = new JSpinner(sm);
		JSpinner.DateEditor de = new JSpinner.DateEditor(spinner, "hh:mm");
                spinner.setEditor(de);
		this.calendar.add(spinner,BorderLayout.NORTH);
		this.calendar.setSize(100,100);
		this.calendar.setVisible(true);
	}
        
        public void setVisible(boolean visible)
        {
            calendar.setVisible(visible);
        }
        public static void main(String[]args){
            time = new ShowTimeJSpinner();
            time.setVisible(true);
        }
     
}