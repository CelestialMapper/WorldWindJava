/*
 * Copyright (C) 2012 United States Government as represented by the Administrator of the
 * National Aeronautics and Space Administration.
 * All Rights Reserved.
 */
package gov.nasa.worldwindx.examples;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.net.URISyntaxException;

/**
 * This example demonstrates the use of multiple WMS layers, as displayed in a WMSLayersPanel.
 *
 * @author tag
 * @version $Id: WMSLayerManager.java 2109 2014-06-30 16:52:38Z tgaskins $
 */
public class WMSLayerManager
{
    protected static final String[] servers = new String[]
        {
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/earth/moon_simp_cyl.map",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/earth/moon_npole.map",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/earth/moon_spole.map",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/earth/moon_simp_cyl_quads.map",
            "https://wms.wr.usgs.gov/cgi-bin/mapserv?map=/maps/earth/moon_nomen_wms.map",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/mars/mars_simp_cyl.map&",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/saturn/titan_simp_cyl.map&",
            "http://webmap.lroc.asu.edu/",
            "https://planetarymaps.usgs.gov/cgi-bin/mapserv?map=/maps/venus/venus_simp_cyl.map&"
        };

    protected static class AppFrame extends ApplicationTemplate.AppFrame
    {
        protected final Dimension wmsPanelSize = new Dimension(400, 600);
        protected JTabbedPane tabbedPane;
        protected int previousTabIndex;

        public AppFrame()
        {
            this.tabbedPane = new JTabbedPane();

            this.tabbedPane.add(new JPanel());
            this.tabbedPane.setTitleAt(0, "+");
            this.tabbedPane.addChangeListener(new ChangeListener()
            {
                public void stateChanged(ChangeEvent changeEvent)
                {
                    if (tabbedPane.getSelectedIndex() != 0)
                    {
                        previousTabIndex = tabbedPane.getSelectedIndex();
                        return;
                    }

                    String server = JOptionPane.showInputDialog("Enter wms server URL");
                    if (server == null || server.length() < 1)
                    {
                        tabbedPane.setSelectedIndex(previousTabIndex);
                        return;
                    }

                    // Respond by adding a new WMSLayerPanel to the tabbed pane.
                    if (addTab(tabbedPane.getTabCount(), server.trim()) != null)
                        tabbedPane.setSelectedIndex(tabbedPane.getTabCount() - 1);
                }
            });

            // Create a tab for each server and add it to the tabbed panel.
            for (int i = 0; i < servers.length; i++)
            {
                this.addTab(i + 1, servers[i]); // i+1 to place all server tabs to the right of the Add Server tab
            }

            // Display the first server pane by default.
            this.tabbedPane.setSelectedIndex(this.tabbedPane.getTabCount() > 0 ? 1 : 0);
            this.previousTabIndex = this.tabbedPane.getSelectedIndex();

            // Add the tabbed pane to a frame separate from the WorldWindow.
            JFrame controlFrame = new JFrame();
            controlFrame.getContentPane().add(tabbedPane);
            controlFrame.pack();
            controlFrame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            controlFrame.setVisible(true);
        }

        protected WMSLayersPanel addTab(int position, String server)
        {
            // Add a server to the tabbed dialog.
            try
            {
                WMSLayersPanel layersPanel = new WMSLayersPanel(AppFrame.this.getWwd(), server, wmsPanelSize);
                this.tabbedPane.add(layersPanel, BorderLayout.CENTER);
                String title = layersPanel.getServerDisplayString();
                this.tabbedPane.setTitleAt(position, title != null && title.length() > 0 ? title : server);

                return layersPanel;
            }
            catch (URISyntaxException e)
            {
                JOptionPane.showMessageDialog(null, "Server URL is invalid", "Invalid Server URL",
                    JOptionPane.ERROR_MESSAGE);
                tabbedPane.setSelectedIndex(previousTabIndex);
                return null;
            }
        }
    }

    public static void main(String[] args)
    {
        ApplicationTemplate.start("CMS WMS Layers", AppFrame.class);
    }
}
