package gov.nasa.cms.features;

import gov.nasa.worldwind.WorldWindow;
import gov.nasa.worldwind.geom.LatLon;
import gov.nasa.worldwind.layers.RenderableLayer;
import gov.nasa.worldwind.layers.TerrainProfileLayer;
import gov.nasa.worldwind.util.measure.MeasureTool;
import gov.nasa.worldwind.util.measure.MeasureToolController;
import static gov.nasa.worldwindx.examples.ApplicationTemplate.insertBeforePlacenames;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.event.ChangeEvent;

/**
 * Creates a MeasureDialog using CMSMeasurePanel.java. CMSMeasurePanel uses
 * MeasureTool and MeasureToolController to interact with shapes. The user
 * can create as many Measure Tools as they like by opening new tabs. Each
 * MeasureTool contains a TerrainProfileLayer which measures the terrain profile
 * along the MeasureTool that is created.
 *
 * @author kjdickin
 */
public class MeasureDialog
{

    private JDialog dialog;
    private final TerrainProfileLayer profile = new TerrainProfileLayer();
    private JTabbedPane tabbedPane = new JTabbedPane();
    private final PropertyChangeListener measureToolListener = new MeasureToolListener();
    private int lastTabIndex = -1;
    WorldWindow wwdObject;
    String FEATURE_OWNER_PROPERTY = "gov.nasa.worldwindx.applications.worldwindow.FeatureOwnerProperty";
    private RenderableLayer shapeLayer;
    private RenderableLayer controlPointsLayer;
    private static final String LAYER_NAME = "Measure Tool";
    
    public MeasureDialog(WorldWindow wwdObject, MeasureTool measureToolObject, Component component)
    {
        
        // Add terrain profile layer
        profile.setEventSource(wwdObject);
        profile.setFollow(TerrainProfileLayer.FOLLOW_PATH);
        profile.setShowProfileLine(false);
        insertBeforePlacenames(wwdObject, profile);

        // Add + tab
        this.tabbedPane = new JTabbedPane();
        tabbedPane.add(new JPanel());
        tabbedPane.setTitleAt(0, "+");
        tabbedPane.addChangeListener((ChangeEvent changeEvent) ->
        {
            if (tabbedPane.getSelectedIndex() == 0)
            {
                // Add new measure tool in a tab when '+' selected
                MeasureTool measureTool = new MeasureTool(wwdObject);
                measureTool.setController(new MeasureToolController());
                tabbedPane.add(new CMSMeasurePanel(wwdObject, measureTool));
                tabbedPane.setTitleAt(tabbedPane.getTabCount() - 1, "" + (tabbedPane.getTabCount() - 1));
                tabbedPane.setSelectedIndex(tabbedPane.getTabCount() - 1);
                switchMeasureTool();
            } else
            {
                switchMeasureTool();
            }
        });
  
//        JButton deleteButton = new JButton ("Remove Current Measurement");
//        deleteButton.setOpaque(false);
//        deleteButton.setBackground(new Color(0, 0, 0, 0));
//        deleteButton.setBorderPainted(false);
//        deleteButton.addActionListener(new ActionListener()
//        {
//            public void actionPerformed(ActionEvent e)
//            {
//                CMSMeasurePanel measurePanel = getCurrentPanel();
//                tabbedPane.remove(tabbedPane.getSelectedComponent());
//            }
//        });
        //deleteButton.setEnabled(true);     // do i need this with add ?? it shows up either way 
        
        // Add measure tool control panel to tabbed pane
        final MeasureTool measureTool = new MeasureTool(wwdObject);
        measureTool.setController(new MeasureToolController());
        
        CMSMeasurePanel measurePanel = new CMSMeasurePanel(wwdObject, measureTool);
      //  measurePanel.add(deleteButton);
        
        tabbedPane.add(measurePanel);
        tabbedPane.setTitleAt(1, "1");
        tabbedPane.setSelectedIndex(1);
        tabbedPane.setToolTipTextAt(0, "Create measurement");
        switchMeasureTool();
        
        // Create the dialog from a Frame and set the bounds
        dialog = new JDialog((Frame) component);     
        Rectangle bounds = component.getBounds();
        dialog.getContentPane().setLayout(new BorderLayout());
        dialog.setTitle("Measure Tool");
        // Set the location and resizable to false
        dialog.setLocation(bounds.x, bounds.y + 90);
        dialog.setResizable(false);
        // Add the tabbedPane to the dialog
        dialog.getContentPane().add(tabbedPane, BorderLayout.CENTER);
        dialog.pack();
    }

    private CMSMeasurePanel getCurrentPanel()
    {
        JComponent p = (JComponent) tabbedPane.getSelectedComponent();
        return (CMSMeasurePanel) p.getClientProperty(FEATURE_OWNER_PROPERTY);
    }
        
    public void setVisible(boolean visible)
    {
        dialog.setVisible(visible);
    }

    private void switchMeasureTool()
    {
        // Disarm last measure tool when changing tab and switching tool
        if (lastTabIndex != -1)
        {
            MeasureTool mt = ((CMSMeasurePanel) tabbedPane.getComponentAt(lastTabIndex)).getMeasureTool();
            mt.setArmed(false);
            mt.removePropertyChangeListener(measureToolListener);
        }
        // Update terrain profile from current measure tool
        lastTabIndex = tabbedPane.getSelectedIndex();
        MeasureTool mt = ((CMSMeasurePanel) tabbedPane.getComponentAt(lastTabIndex)).getMeasureTool();
        mt.addPropertyChangeListener(measureToolListener);
        updateProfile(mt);
    }

    private class MeasureToolListener implements PropertyChangeListener
    {

        @Override
        public void propertyChange(PropertyChangeEvent event)
        {
            // Measure shape position list changed - update terrain profile
            if (event.getPropertyName().equals(MeasureTool.EVENT_POSITION_ADD)
                    || event.getPropertyName().equals(MeasureTool.EVENT_POSITION_REMOVE)
                    || event.getPropertyName().equals(MeasureTool.EVENT_POSITION_REPLACE))
            {
                updateProfile(((MeasureTool) event.getSource()));
            }
        }
    }

    private void updateProfile(MeasureTool mt)
    {
        ArrayList<? extends LatLon> positions = mt.getPositions();
        if (positions != null && positions.size() > 1)
        {
            profile.setPathPositions(positions);
            profile.setEnabled(true);
        } else
        {
            profile.setEnabled(false);
        }

        mt.getWwd().redraw();
    }
}
