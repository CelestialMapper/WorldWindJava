package gov.nasa.worldwindx.examples;

import gov.nasa.worldwind.WorldWindow;
import gov.nasa.worldwind.geom.LatLon;
import gov.nasa.worldwind.layers.TerrainProfileLayer;
import gov.nasa.worldwind.util.measure.MeasureTool;
import gov.nasa.worldwind.util.measure.MeasureToolController;
import static gov.nasa.worldwindx.examples.ApplicationTemplate.insertBeforePlacenames;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.event.ChangeEvent;

public class MeasureDialog
{

    private JDialog dialog;
    private final TerrainProfileLayer profile = new TerrainProfileLayer();
    private final JTabbedPane tabbedPane = new JTabbedPane();
    private final PropertyChangeListener measureToolListener = new MeasureToolListener();
    private int lastTabIndex = -1;
    WorldWindow wwdObject;
    
    public MeasureDialog(WorldWindow wwdObject, MeasureTool measureToolObject, Component component)
    {
        // Add terrain profile layer
        profile.setEventSource(wwdObject);
        profile.setFollow(TerrainProfileLayer.FOLLOW_PATH);
        profile.setShowProfileLine(false);
        insertBeforePlacenames(wwdObject, profile);

        // Add + tab
        tabbedPane.add(new JPanel());
        tabbedPane.setTitleAt(0, "+");
        tabbedPane.addChangeListener((ChangeEvent changeEvent) ->
        {
            if (tabbedPane.getSelectedIndex() == 0)
            {
                // Add new measure tool in a tab when '+' selected
                MeasureTool measureTool = new MeasureTool(wwdObject);
                measureTool.setController(new MeasureToolController());
                tabbedPane.add(new MeasureToolPanel(wwdObject, measureTool));
                tabbedPane.setTitleAt(tabbedPane.getTabCount() - 1, "" + (tabbedPane.getTabCount() - 1));
                tabbedPane.setSelectedIndex(tabbedPane.getTabCount() - 1);
                switchMeasureTool();
            } else
            {
                switchMeasureTool();
            }
        });
  
        // Add measure tool control panel to tabbed pane
        final MeasureTool measureTool = new MeasureTool(wwdObject);
        measureTool.setController(new MeasureToolController());
        tabbedPane.add(new MeasureToolPanel(wwdObject, measureTool));
        tabbedPane.setTitleAt(1, "1");
        tabbedPane.setSelectedIndex(1);
        tabbedPane.setToolTipTextAt(0, "Create measurement");
        switchMeasureTool();
        
        dialog = new JDialog((Frame) component);
        dialog.getContentPane().add(tabbedPane, BorderLayout.CENTER);
        dialog.pack();
        dialog.setLocationRelativeTo(component);
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
            MeasureTool mt = ((MeasureToolPanel) tabbedPane.getComponentAt(lastTabIndex)).getMeasureTool();
            mt.setArmed(false);
            mt.removePropertyChangeListener(measureToolListener);
        }
        // Update terrain profile from current measure tool
        lastTabIndex = tabbedPane.getSelectedIndex();
        MeasureTool mt = ((MeasureToolPanel) tabbedPane.getComponentAt(lastTabIndex)).getMeasureTool();
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
