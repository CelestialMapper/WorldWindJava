/*
 * Copyright (C) 2012 United States Government as represented by the Administrator of the
 * National Aeronautics and Space Administration.
 * All Rights Reserved.
 */
package gov.nasa.cms;

import gov.nasa.cms.features.ApolloMenu;
import gov.nasa.cms.features.Apollo;
import gov.nasa.cms.features.CMSProfile;
import gov.nasa.cms.features.LayerManagerLayer;
import gov.nasa.cms.features.MeasureDialog;
import gov.nasa.cms.features.MoonElevationModel;
import gov.nasa.worldwind.WorldWindow;
import gov.nasa.worldwind.util.measure.MeasureTool;
import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.io.*;

/**
 * CelestialMapper.java
 *
 */
public class CelestialMapper
{

    protected static final String CMS_LAYER_NAME = "Celestial Shapes";
    protected static final String CLEAR_SELECTION = "CelestialMapper.ClearSelection";
    protected static final String ENABLE_EDIT = "CelestialMapper.EnableEdit";
    protected static final String OPEN = "CelestialMapper.Open";
    protected static final String OPEN_URL = "CelestialMapper.OpenUrl";
    protected static final String REMOVE_SELECTED = "CelestialMapper.RemoveSelected";
    protected static final String SAVE = "CelestialMapper.Save";
    protected static final String SELECTION_CHANGED = "CelestialMapper.SelectionChanged";
    protected static final String ELEVATIONS_PATH = "testData/lunar-dem.tif";

    //**************************************************************//
    //********************  Main  **********************************//
    //**************************************************************//
    protected static class AppFrame extends ApplicationTemplate.AppFrame
    {

        ActionListener controller;
        private CMSPlaceNamesMenu cmsPlaceNamesMenu;
        private WorldWindow wwd;
        private MeasureDialog measureDialog;
        private Apollo apollo;
        private ApolloMenu apolloMenu;
        private CMSProfile profile;
        private MeasureTool measureTool;
        private MoonElevationModel elevationModel;
        private CMSStereo stereo;
        
        public AppFrame() 
        { 
            super(true, false, false); // disable layer menu and statisics panel for AppFrame
            getWwd().getModel().getLayers().add(new LayerManagerLayer(getWwd())); // add layer box UI
                        
            // Wait for the elevation to import            
            // Import the lunar elevation data from a Local Elevation Model
            elevationModel = new MoonElevationModel(this.getWwd());

            // Make the menu bar
            makeMenuBar(this, this.controller); 
        }
        
        // Menu bar creation
        public void makeMenuBar(JFrame frame, final ActionListener controller)
        {
            JMenuBar menuBar = new JMenuBar();

            //======== "CMS Place Names" ========          
            cmsPlaceNamesMenu = new CMSPlaceNamesMenu(this, this.getWwd());
            menuBar.add(cmsPlaceNamesMenu);

            //======== "Tools" ========        
            JMenu tools = new JMenu("Tools");
            {
                // Terrain Profiler
                profile = new CMSProfile(this.getWwd());
                tools.add(profile);

                menuBar.add(tools);

                // Measurement Dialog
                JMenuItem openMeasureDialogItem = new JMenuItem(new AbstractAction("Measurement")
                {
                    public void actionPerformed(ActionEvent actionEvent)
                    {
                        final WorldWindow wwd = getWwd();
                        try
                        {
                            // Check if the MeasureDialog has already been opened
                            if (AppFrame.this.measureDialog == null)
                            {
                                // Create the dialog 
                                AppFrame.this.measureDialog = new MeasureDialog(wwd, measureTool, AppFrame.this);
                            }
                            // Display on screen 
                            AppFrame.this.measureDialog.setVisible(true);
                        } catch (Exception e)
                        {
                            e.printStackTrace();
                        }
                    }
                });
                tools.add(openMeasureDialogItem);
            }
            menuBar.add(tools);

            //======== "View" ========           
            JMenu menu = new JMenu("View");
            {                
                // Stereo menu item
                stereo = new CMSStereo(this, this.getWwd());
                menu.add(stereo);

            }
            menuBar.add(menu);
            
            apolloMenu = new ApolloMenu(this.getWwd());
            menuBar.add(apolloMenu);
            frame.setJMenuBar(menuBar);

            this.cmsPlaceNamesMenu.setWwd(this.wwd); //sets window for place names   
            this.profile.setWwd(this.wwd); // sets the window for terrain profiler
            this.elevationModel.setWwd(this.wwd); // sets the window for terrain profiler
            this.stereo.setWwd(this.wwd);
        }
    }
}
