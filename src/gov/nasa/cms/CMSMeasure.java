/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.cms;

import gov.nasa.cms.CelestialMapper.AppFrame;
import gov.nasa.worldwind.WorldWindow;
import gov.nasa.worldwind.layers.Layer;
import gov.nasa.worldwind.layers.TerrainProfileLayer;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JCheckBoxMenuItem;


/**
 * Creates a new terrain profile layer from <code>{@link JCheckBoxMenuItem}</code>
 * @author kjdickin
 */
public class CMSMeasure extends JCheckBoxMenuItem
{

    private WorldWindow wwd;
    private TerrainProfileLayer tpl;
    private boolean isItemEnabled;

    // Create the terrain profile layer
    public void setupProfile()
    {
        this.tpl = new TerrainProfileLayer(); 
        this.tpl.setEventSource(this.getWwd()); 
        String layerName = "Terrain Profile"; 
        this.tpl.setName(layerName);
        ApplicationTemplate.insertBeforeCompass(this.getWwd(), tpl); // display on screen
    }

    public CMSMeasure(AppFrame cms, WorldWindow Wwd)
    {
        super("Terrain Profiler");

        // Enable and disable terrain profile 
        this.addActionListener(new ActionListener()
        {
            @Override
            public void actionPerformed(ActionEvent event)
            {
                isItemEnabled = ((JCheckBoxMenuItem) event.getSource()).getState();

                if (isItemEnabled)
                {
                    setWwd(Wwd);
                    setupProfile();
                } 
                else
                {
                    String layer = "Terrain Profile";                 
                    Layer selectedLayer = Wwd.getModel().getLayers().getLayerByName(layer);
                    Wwd.getModel().getLayers().remove(selectedLayer); //removes tpl layer from layer list
                }
            }
        });
    }

    public WorldWindow getWwd()
    {
        return this.wwd;
    }

    public void setWwd(WorldWindow wwd)
    {
        this.wwd = wwd;
    }
}
