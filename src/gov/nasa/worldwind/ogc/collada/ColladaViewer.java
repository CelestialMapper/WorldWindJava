/*
 * Copyright 2006-2009, 2017, 2020 United States Government, as represented by the
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 * 
 * The NASA World Wind Java (WWJ) platform is licensed under the Apache License,
 * Version 2.0 (the "License"); you may not use this file except in compliance
 * with the License. You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 * 
 * NASA World Wind Java (WWJ) also contains the following 3rd party Open Source
 * software:
 * 
 *     Jackson Parser – Licensed under Apache 2.0
 *     GDAL – Licensed under MIT
 *     JOGL – Licensed under  Berkeley Software Distribution (BSD)
 *     Gluegen – Licensed under Berkeley Software Distribution (BSD)
 * 
 * A complete listing of 3rd Party software notices and licenses included in
 * NASA World Wind Java (WWJ)  can be found in the WorldWindJava-v2.2 3rd-party
 * notices and licenses PDF found in code directory.
 */
/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package gov.nasa.worldwind.ogc.collada;

import gov.nasa.worldwind.*;
import gov.nasa.worldwind.avlist.AVKey;
import gov.nasa.worldwind.geom.Position;
import gov.nasa.worldwind.layers.Layer;
import gov.nasa.worldwind.layers.LayerList;
import gov.nasa.worldwind.layers.RenderableLayer;
import gov.nasa.worldwind.ogc.collada.impl.ColladaController;
import gov.nasa.worldwind.util.WWUtil;
import gov.nasa.worldwindx.examples.ApplicationTemplate;
import static gov.nasa.worldwindx.examples.ApplicationTemplate.start;

import javax.swing.*;
import java.awt.*;
import java.io.File;

/**
 * Shows how to load <a href="https://www.khronos.org/collada/">COLLADA</a> 3D models.
 */
public class ColladaViewer extends ApplicationTemplate {

    public static class AppFrame extends ApplicationTemplate.AppFrame {

        public AppFrame() {
            super(true, true, false); // Don't include the layer panel; we're using the on-screen layer tree.

            // Size the WorldWindow to take up the space typically used by the layer panel.
            Dimension size = new Dimension(1400, 800);
            this.setPreferredSize(size);
            this.pack();
            WWUtil.alignComponent(null, this, AVKey.CENTER);
            LayerList layers = getWwd().getModel().getLayers();
            for (Layer layer : layers) {
                String layerName = layer.getName();
                if (layerName != null && layerName.toLowerCase().startsWith("bing")) {
                    layer.setEnabled(true);
                    break;
                }
            }
        }

        /**
         * Adds the specified <code>colladaRoot</code> to this app frame's <code>WorldWindow</code> as a new
         * <code>Layer</code>.
         *
         * @param colladaRoot the ColladaRoot to add a new layer for.
         */
        protected void addColladaLayer(ColladaRoot colladaRoot) {
            // Create a ColladaController to adapt the ColladaRoot to the WorldWind renderable interface.
            ColladaController colladaController = new ColladaController(colladaRoot);

            // Adds a new layer containing the ColladaRoot to the end of the WorldWindow's layer list.
            RenderableLayer layer = new RenderableLayer();
            layer.addRenderable(colladaController);
            this.getWwd().getModel().getLayers().add(layer);
        }
    }

    // A <code>Thread</code> that loads a COLLADA file and displays it in an <code>AppFrame</code>.
    public static class WorkerThread extends Thread {

        // Indicates the source of the COLLADA file loaded by this thread. Initialized during construction.
        protected Object colladaSource;

        // Geographic position of the COLLADA model.
        protected Position position;

        // Indicates the <code>AppFrame</code> the COLLADA file content is displayed in. Initialized during
        // construction.
        protected AppFrame appFrame;

        /**
         * Creates a new worker thread from a specified <code>colladaSource</code> and <code>appFrame</code>.
         *
         * @param colladaSource the source of the COLLADA file to load. May be a {@link java.io.File}, a {@link
         *                      java.net.URL}, or an {@link java.io.InputStream}, or a {@link String} identifying a file path or URL.
         * @param position the geographic position of the COLLADA model.
         * @param appFrame the <code>AppFrame</code> in which to display the COLLADA source.
         */
        public WorkerThread(Object colladaSource, Position position, AppFrame appFrame) {
            this.colladaSource = colladaSource;
            this.position = position;
            this.appFrame = appFrame;
        }

        /**
         * Loads this worker thread's COLLADA source into a new
         * <code>{@link gov.nasa.worldwind.ogc.collada.ColladaRoot}</code>, then adds the new <code>ColladaRoot</code>
         * to this worker thread's <code>AppFrame</code>.
         */
        @Override
        public void run() {
            try {
                final ColladaRoot colladaRoot = ColladaRoot.createAndParse(this.colladaSource);
                colladaRoot.setPosition(this.position);
                colladaRoot.setAltitudeMode(WorldWind.RELATIVE_TO_GROUND);

                // Schedule a task on the EDT to add the parsed document to a layer
                SwingUtilities.invokeLater(() -> {
                    appFrame.addColladaLayer(colladaRoot);
                });
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }

    public static void main(String[] args) {

        // Set camera position and pitch angle.
        Configuration.setValue(AVKey.INITIAL_LATITUDE, 40.028);
        Configuration.setValue(AVKey.INITIAL_LONGITUDE, -105.27284091410579);
        Configuration.setValue(AVKey.INITIAL_ALTITUDE, 4000);
        Configuration.setValue(AVKey.INITIAL_PITCH, 50);

        // Set the application frame to update, a position for the model, and a path to the COLLADA file.
        final AppFrame af = (AppFrame) start("WorldWind COLLADA Viewer", AppFrame.class);
        final Position MackyAuditoriumPosition = Position.fromDegrees(40.009993372683, -105.272774533734);
        final File ColladaFile = new File("testData/collada/cu_macky/CU Macky.dae");

        // Invoke the <code>Thread</code> to load the COLLADA model asynchronously.
        new WorkerThread(ColladaFile, MackyAuditoriumPosition, af).start();

    }
}
