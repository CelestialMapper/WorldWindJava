/*
Copyright (C) 2001, 2006 United States Government
as represented by the Administrator of the
National Aeronautics and Space Administration.
All Rights Reserved.
 */
package gov.nasa.worldwind.terrain;

import com.jogamp.common.nio.Buffers;
import com.jogamp.opengl.GL;
import com.jogamp.opengl.GL2;
import gov.nasa.worldwind.Configuration;
import gov.nasa.worldwind.View;
import gov.nasa.worldwind.WorldWind;
import gov.nasa.worldwind.avlist.AVKey;
import gov.nasa.worldwind.cache.BasicMemoryCache;
import gov.nasa.worldwind.cache.GpuResourceCache;
import gov.nasa.worldwind.cache.MemoryCache;
import gov.nasa.worldwind.geom.Angle;
import gov.nasa.worldwind.geom.Cylinder;
import gov.nasa.worldwind.geom.Extent;
import gov.nasa.worldwind.geom.Frustum;
import gov.nasa.worldwind.geom.Intersection;
import gov.nasa.worldwind.geom.LatLon;
import gov.nasa.worldwind.geom.Line;
import gov.nasa.worldwind.geom.PolarPoint;
import gov.nasa.worldwind.geom.Sector;
import gov.nasa.worldwind.geom.Vec4;
import gov.nasa.worldwind.globes.Globe;
import gov.nasa.worldwind.pick.PickedObject;
import gov.nasa.worldwind.render.DrawContext;
import gov.nasa.worldwind.util.Logging;
import gov.nasa.worldwind.util.OGLStackHandler;
import java.awt.Point;
import java.nio.DoubleBuffer;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;
import java.util.HashMap;
import java.util.List;

/**
 * @author Tom Gaskins
 * @version $Id: EllipsoidIcosahedralTessellator.java 5377 2008-05-28 20:28:48Z
 * tgaskins $
 */
public class EllipsoidIcosahedralTessellator //extends WWObjectImpl implements Tessellator
{

    // TODO: This class works as of 3/15/07 but it is not complete. There is a problem with texture coordinate
    // generation around +-20 degrees latitude, and picking and meridian/parallel lines are not implemented.
    // Also needs skirt creation.
    private static int DEFAULT_DENSITY = 20;
    private static final int DEFAULT_MAX_LEVEL = 14;
    protected static final HashMap<Integer, Object> textureCoordVboCacheKeys = new HashMap<Integer, Object>();
    protected static final HashMap<Integer, Object> indexListsVboCacheKeys = new HashMap<Integer, Object>();

    private static class GlobeInfo
    {

        private final Globe globe; // TODO: remove the dependency on this
        private final double level0EdgeLength;
        private final double invAsq;
        private final double invCsq;

        static final double EDGE_FACTOR = Math.sqrt(10d + 2d * Math.sqrt(5d)) / 4d;

        private GlobeInfo(Globe globe)
        {
            this.globe = globe;
            double equatorialRadius = globe.getEquatorialRadius();
            double polarRadius = globe.getPolarRadius();

            this.invAsq = 1 / (equatorialRadius * equatorialRadius);
            this.invCsq = 1 / (polarRadius * polarRadius);

            this.level0EdgeLength = equatorialRadius / EDGE_FACTOR;
        }
    }

    private static class IcosaTile implements SectorGeometry
    {

        private static java.util.HashMap<Integer, double[]> parameterizations = new java.util.HashMap<Integer, double[]>();
        private static java.util.HashMap<Integer, java.nio.IntBuffer> indexLists = new java.util.HashMap<Integer, java.nio.IntBuffer>();
        protected final int level;
        private final GlobeInfo globeInfo;
        private final LatLon g0, g1, g2;
        private Sector sector; // lazily evaluated
        protected final Vec4 unitp0, unitp1, unitp2; // points on unit sphere
        private final Vec4 p0;
        private final Vec4 p1;
        private final Vec4 p2;
        private final Vec4 pCentroid;
        //        private final Vector normal; // ellipsoids's normal vector at tile centroid
        private final Extent extent; // extent of triangle in object coordinates
        private final double edgeLength;
        private int density = DEFAULT_DENSITY;
        private long byteSize;
        static final double ROOT3_OVER4 = Math.sqrt(3) / 4d;
        protected RenderInfo ri;

        protected static double[] getParameterization(int density)
        {
            double[] p = parameterizations.get(density);
            if (p != null)
            {
                return p;
            }

            int coordCount = (density * density + 3 * density + 2) / 2;
            p = new double[2 * coordCount];
            double delta = 1d / density;
            int k = 0;
            for (int j = 0; j <= density; j++)
            {
                double v = j * delta;
                for (int i = 0; i <= density - j; i++)
                {
                    p[k++] = i * delta; // u
                    p[k++] = v;
                }
            }

            parameterizations.put(density, p);

            return p;
        }

        protected static java.nio.IntBuffer getIndices(int density)
        {
            java.nio.IntBuffer buffer = indexLists.get(density);
            if (buffer != null)
            {
                return buffer;
            }

            int indexCount = density * density + 4 * density - 2;
            buffer = Buffers.newDirectIntBuffer(indexCount);
            int k = 0;
            for (int i = 0; i < density; i++)
            {
                buffer.put(k);
                if (i > 0)
                {
                    k = buffer.get(buffer.position() - 3);
                    buffer.put(k);
                    buffer.put(k);
                }

                if (i % 2 == 0) // even
                {
                    for (int j = 0; j < density - i; j++)
                    {
                        ++k;
                        buffer.put(k);
                        k += density - j;
                        buffer.put(k);
                    }
                } else // odd
                {
                    for (int j = density - i - 1; j >= 0; j--)
                    {
                        k -= density - j;
                        buffer.put(k);
                        --k;
                        buffer.put(k);
                    }
                }
            }

            indexLists.put(density, buffer);

            return buffer;
        }

        public static Vec4 getUnitPoint(double u, double v, Vec4 p0, Vec4 p1, Vec4 p2)
        {
            double w = 1d - u - v;
            double x = u * p1.x + v * p2.x + w * p0.x;
            double y = u * p1.y + v * p2.y + w * p0.y;
            double z = u * p1.z + v * p2.z + w * p0.z;
            double invLength = 1d / Math.sqrt(x * x + y * y + z * z);

            return new Vec4(x * invLength, y * invLength, z * invLength);
        }

        public static Vec4 getMidPoint(Vec4 p0, Vec4 p1)
        {
            return new Vec4(
                    (p0.x + p1.x) / 2.0,
                    (p0.y + p1.y) / 2.0,
                    (p0.z + p1.z) / 2.0);
        }

        public IcosaTile(GlobeInfo globeInfo, int level, Vec4 unitp0, Vec4 unitp1, Vec4 unitp2, DrawContext dc)
        {
            this.level = level;
            this.globeInfo = globeInfo;

            this.unitp0 = unitp0;
            this.unitp1 = unitp1;
            this.unitp2 = unitp2;

            // Compute lat/lon at tile vertices.
            Angle lat = Angle.fromRadians(Math.asin(this.unitp0.y));
            Angle lon = Angle.fromRadians(Math.atan2(this.unitp0.x, this.unitp0.z));
            this.g0 = new LatLon(lat, lon);
            lat = Angle.fromRadians(Math.asin(this.unitp1.y));
            lon = Angle.fromRadians(Math.atan2(this.unitp1.x, this.unitp1.z));
            this.g1 = new LatLon(lat, lon);
            lat = Angle.fromRadians(Math.asin(this.unitp2.y));
            lon = Angle.fromRadians(Math.atan2(this.unitp2.x, this.unitp2.z));
            this.g2 = new LatLon(lat, lon);

            // Compute the triangle corner points on the ellipsoid at mean, max and min elevations.
            this.p0 = this.scaleUnitPointToEllipse(this.unitp0, this.globeInfo.invAsq, this.globeInfo.invCsq);
            this.p1 = this.scaleUnitPointToEllipse(this.unitp1, this.globeInfo.invAsq, this.globeInfo.invCsq);
            this.p2 = this.scaleUnitPointToEllipse(this.unitp2, this.globeInfo.invAsq, this.globeInfo.invCsq);

            double a = 1d / 3d;
            Vec4 unitCentroid = getUnitPoint(a, a, this.unitp0, this.unitp1, this.unitp2);
            this.pCentroid = this.scaleUnitPointToEllipse(unitCentroid, this.globeInfo.invAsq, this.globeInfo.invCsq);

//            // Compute the tile normal, which is the gradient of the ellipse at the centroid.
//            double nx = 2 * this.pCentroid.x() * this.globeInfo.invAsq;
//            double ny = 2 * this.pCentroid.y() * this.globeInfo.invCsq;
//            double nz = 2 * this.pCentroid.z() * this.globeInfo.invAsq;
//            this.normal = new Vector(nx, ny, nz).normalize();
            this.extent = Sector.computeBoundingBox(dc.getGlobe(), dc.getVerticalExaggeration(), this.getSector());

            this.edgeLength = this.globeInfo.level0EdgeLength / Math.pow(2, this.level);
        }

        public IcosaTile(GlobeInfo globeInfo, int level, LatLon g0, LatLon g1, LatLon g2, DrawContext dc)
        {
            // TODO: Validate args
            this.level = level;
            this.globeInfo = globeInfo;

            this.g0 = g0;
            this.g1 = g1;
            this.g2 = g2;

            this.unitp0 = PolarPoint.toCartesian(this.g0.getLatitude(), this.g0.getLongitude(), 1);
            this.unitp1 = PolarPoint.toCartesian(this.g1.getLatitude(), this.g1.getLongitude(), 1);
            this.unitp2 = PolarPoint.toCartesian(this.g2.getLatitude(), this.g2.getLongitude(), 1);

            // Compute the triangle corner points on the ellipsoid at mean, max and min elevations.
            this.p0 = this.scaleUnitPointToEllipse(this.unitp0, this.globeInfo.invAsq, this.globeInfo.invCsq);
            this.p1 = this.scaleUnitPointToEllipse(this.unitp1, this.globeInfo.invAsq, this.globeInfo.invCsq);
            this.p2 = this.scaleUnitPointToEllipse(this.unitp2, this.globeInfo.invAsq, this.globeInfo.invCsq);

            double a = 1d / 3d;
            Vec4 unitCentroid = getUnitPoint(a, a, this.unitp0, this.unitp1, this.unitp2);
            this.pCentroid = this.scaleUnitPointToEllipse(unitCentroid, this.globeInfo.invAsq, this.globeInfo.invCsq);

//            // Compute the tile normal, which is the gradient of the ellipse at the centroid.
//            double nx = 2 * this.pCentroid.x() * this.globeInfo.invAsq;
//            double ny = 2 * this.pCentroid.y() * this.globeInfo.invCsq;
//            double nz = 2 * this.pCentroid.z() * this.globeInfo.invAsq;
//            this.normal = new Vector(nx, ny, nz).normalize();
            this.extent = Sector.computeBoundingBox(dc.getGlobe(), dc.getVerticalExaggeration(), this.getSector());

            this.edgeLength = this.globeInfo.level0EdgeLength / Math.pow(2, this.level);
        }

        @Override
        public Sector getSector()
        {
            if (this.sector != null)
            {
                return this.sector;
            }

            double m;

            m = this.g0.getLatitude().getRadians();
            if (this.g1.getLatitude().getRadians() < m)
            {
                m = this.g1.getLatitude().getRadians();
            }
            if (this.g2.getLatitude().getRadians() < m)
            {
                m = this.g2.getLatitude().getRadians();
            }
            Angle minLat = Angle.fromRadians(m);

            m = this.g0.getLatitude().getRadians();
            if (this.g1.getLatitude().getRadians() > m)
            {
                m = this.g1.getLatitude().getRadians();
            }
            if (this.g2.getLatitude().getRadians() > m)
            {
                m = this.g2.getLatitude().getRadians();
            }
            Angle maxLat = Angle.fromRadians(m);

            m = this.g0.getLongitude().getRadians();
            if (this.g1.getLongitude().getRadians() < m)
            {
                m = this.g1.getLongitude().getRadians();
            }
            if (this.g2.getLongitude().getRadians() < m)
            {
                m = this.g2.getLongitude().getRadians();
            }
            Angle minLon = Angle.fromRadians(m);

            m = this.g0.getLongitude().getRadians();
            if (this.g1.getLongitude().getRadians() > m)
            {
                m = this.g1.getLongitude().getRadians();
            }
            if (this.g2.getLongitude().getRadians() > m)
            {
                m = this.g2.getLongitude().getRadians();
            }
            Angle maxLon = Angle.fromRadians(m);

            return this.sector = new Sector(minLat, maxLat, minLon, maxLon);
        }

        private Vec4 scaleUnitPointToEllipse(Vec4 up, double invAsq, double invCsq)
        {
            double f = up.x * up.x * invAsq + up.y * up.y * invCsq + up.z * up.z * invAsq;
            f = 1 / Math.sqrt(f);
            return new Vec4(up.x * f, up.y * f, up.z * f);
        }

        private IcosaTile[] split(DrawContext dc, IcosaTile tile)
        {
            // Subdivisions
            Vec4 up01 = getMidPoint(this.p0, this.p1);
            Vec4 up12 = getMidPoint(this.p1, this.p2);
            Vec4 up20 = getMidPoint(this.p2, this.p0);
            up01 = up01.multiply3(1d / up01.getLength3());
            up12 = up12.multiply3(1d / up12.getLength3());
            up20 = up20.multiply3(1d / up20.getLength3());

            IcosaTile[] subTiles = new IcosaTile[4];
            subTiles[0] = new IcosaTile(this.globeInfo, tile.level + 1, this.unitp0, up01, up20, dc);
            subTiles[1] = new IcosaTile(this.globeInfo, tile.level + 1, up01, this.unitp1, up12, dc);
            subTiles[2] = new IcosaTile(this.globeInfo, tile.level + 1, up20, up12, this.unitp2, dc);
            subTiles[3] = new IcosaTile(this.globeInfo, tile.level + 1, up12, up20, up01, dc);

            return subTiles;
        }

        public String toString()
        {
            return this.level + ": (" + unitp0.toString() + ", " + unitp1.toString() + ", " + unitp2.toString() + ")";
        }

        public Extent getExtent()
        {
            return this.extent;
        }

        @Override
        public void beginRendering(DrawContext dc, int numTextureUnits)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public void endRendering(DrawContext dc)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public void renderWireframe(DrawContext dc, boolean interior, boolean exterior)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public void renderTileID(DrawContext dc)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public PickedObject[] pick(DrawContext dc, List<? extends Point> pickPoints)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public Intersection[] intersect(Line line)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public Intersection[] intersect(double elevation)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public DoubleBuffer makeTextureCoordinates(GeographicTextureCoordinateComputer computer)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public void renderMultiTexture(DrawContext dc, int numTextureUnits, boolean beginRenderingCalled)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        @Override
        public void render(DrawContext dc, boolean beginRenderingCalled)
        {
            throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
        }

        private static class RenderInfo
        {

            private final int density;
            //            private int[] bufferIds = new int[2];
            private DoubleBuffer vertices;
            protected final IntBuffer indices;
            private final DoubleBuffer texCoords;
            protected Object vboCacheKey = new Object();
            protected boolean isVboBound = false;

            private RenderInfo(int density, DoubleBuffer vertices, DoubleBuffer texCoords)
            {
                this.density = density;
                this.vertices = vertices;
                this.texCoords = texCoords;

                this.indices = indexLists.get(this.density);
            }

            protected void fillVerticesVBO(DrawContext dc)
            {
                GL gl = dc.getGL();

                int[] vboIds = (int[]) dc.getGpuResourceCache().get(this.vboCacheKey);
                if (vboIds == null)
                {
                    vboIds = new int[1];
                    gl.glGenBuffers(vboIds.length, vboIds, 0);
                    int size = this.vertices.limit() * 4;
                    dc.getGpuResourceCache().put(this.vboCacheKey, vboIds, GpuResourceCache.VBO_BUFFERS, size);
                }

                try
                {
                    DoubleBuffer vb = this.vertices;
                    gl.glBindBuffer(GL.GL_ARRAY_BUFFER, vboIds[0]);
                    gl.glBufferData(GL.GL_ARRAY_BUFFER, vb.limit() * 4, vb.rewind(), GL.GL_STATIC_DRAW);
                } finally
                {
                    gl.glBindBuffer(GL.GL_ARRAY_BUFFER, 0);
                }
            }

            private long getSizeInBytes()
            {
                return 12;// + this.vertices.limit() * 5 * Float.SIZE;
            }
        }

        private RenderInfo makeVerts(DrawContext dc, IcosaTile tile)
        {
            MemoryCache cache = WorldWind.getMemoryCache(IcosaTile.class.getName());
            CacheKey key = new CacheKey(this, dc.getVerticalExaggeration(), density);
            RenderInfo ri = (RenderInfo) cache.getObject(key);
            if (ri != null)
            {
                return ri;
            }

            ri = this.buildVerts(dc, tile);
            cache.add(key, ri, this.byteSize = ri.getSizeInBytes());

            return ri;
        }

        private RenderInfo buildVerts(DrawContext dc, IcosaTile tile)
        {
            // Density is intended to approximate closely the tessellation's number of intervals along a side.
            double[] params = getParameterization(density); // Parameterization is independent of tile location.
            int numVertexCoords = params.length + params.length / 2;
            int numPositionCoords = params.length;
            DoubleBuffer verts = Buffers.newDirectDoubleBuffer(numVertexCoords);
            DoubleBuffer positions = Buffers.newDirectDoubleBuffer(numPositionCoords);

            Vec4 pu = this.unitp1; // unit vectors at triangle vertices at sphere surface
            Vec4 pv = this.unitp2;
            Vec4 pw = this.unitp0;

            int i = 0;
            while (verts.hasRemaining())
            {
                double u = params[i++];
                double v = params[i++];
                double w = 1d - u - v;

                // Compute point on triangle.
                double x = u * pu.x + v * pv.x + w * pw.x;
                double y = u * pu.y + v * pv.y + w * pw.y;
                double z = u * pu.z + v * pv.z + w * pw.z;

                // Compute latitude and longitude of the vector through point on triangle.
                // Do this before applying ellipsoid eccentricity or elevation.
                double lat = Math.atan2(y, Math.sqrt(x * x + z * z));
                double lon = Math.atan2(x, z);

                // Scale point to lie on the globe's mean ellilpsoid surface.
                double f = 1d / Math.sqrt(
                        x * x * this.globeInfo.invAsq + y * y * this.globeInfo.invCsq + z * z * this.globeInfo.invAsq);
                x *= f;
                y *= f;
                z *= f;

                Angle latParam = Angle.fromDegrees(lat);
                Angle lonParam = Angle.fromDegrees(lon);

                // Scale the point so that it lies at the given elevation.
                double elevation = dc.getGlobe().getElevation(latParam, lonParam);
                double nx = 2 * x * this.globeInfo.invAsq;
                double ny = 2 * y * this.globeInfo.invCsq;
                double nz = 2 * z * this.globeInfo.invAsq;
                double scale = elevation * dc.getVerticalExaggeration() / Math.sqrt(nx * nx + ny * ny + nz * nz);
                nx *= scale;
                ny *= scale;
                nz *= scale;
                lat = Math.atan2(y, Math.sqrt(x * x + z * z));
                lon = Math.atan2(x, z);
                x += (nx - this.pCentroid.x);
                y += (ny - this.pCentroid.y);
                z += (nz - this.pCentroid.z);

                // Store point and position
                verts.put(x).put(y).put(z);
                positions.put(lon).put(lat);
                // TODO: store normal as well
            }

            verts.rewind();

            return new RenderInfo(density, verts, positions);
        }

        public void renderMultiTexture(DrawContext dc, int numTextureUnits)
        {
            dc.getView().setReferenceCenter(dc, this.pCentroid);
            if (dc.getGLRuntimeCapabilities().isUseVertexBufferObject())
            {
                if (this.bindVbos(dc, this, numTextureUnits))
                {
                    this.ri.isVboBound = true;
                }
            }
        }

        public void render(DrawContext dc)
        {
            this.beginRendering(dc, 1);
            this.render(dc, this);
            this.endRendering(dc);
        }

        protected void render(DrawContext dc, IcosaTile tile)
        {
            if (dc == null)
            {
                String msg = Logging.getMessage("nullValue.DrawContextIsNull");
                Logging.logger().severe(msg);
                throw new IllegalArgumentException(msg);
            }

            this.render(dc, tile, 1);
        }

        private long render(DrawContext dc, IcosaTile tile, int numTextureUnits)
        {
            if (tile.ri == null)
            {
                String msg = Logging.getMessage("nullValue.RenderInfoIsNull");
                Logging.logger().severe(msg);
                throw new IllegalStateException(msg);
            }

            if (dc.getGLRuntimeCapabilities().isUseVertexBufferObject())
            {
                if (!this.renderVBO(dc, tile, numTextureUnits))
                {
                    // Fall back to VA rendering. This is an error condition at this point because something went wrong with
                    // VBO fill or binding. But we can still probably draw the tile using vertex arrays.
                    dc.getGL().glBindBuffer(GL.GL_ARRAY_BUFFER, 0);
                    dc.getGL().glBindBuffer(GL.GL_ELEMENT_ARRAY_BUFFER, 0);
                    this.renderVA(dc, tile, numTextureUnits);
                }
            } else
            {
                this.renderVA(dc, tile, numTextureUnits);
            }

            return tile.ri.indices.limit() - 2; // return number of triangles rendered
        }

        protected boolean renderVBO(DrawContext dc, IcosaTile tile, int numTextureUnits)
        {
            if (tile.ri.isVboBound || this.bindVbos(dc, tile, numTextureUnits))
            {
                // Render the tile
                dc.getGL().glDrawElements(GL.GL_TRIANGLE_STRIP, tile.ri.indices.limit(), GL.GL_UNSIGNED_INT, 0);
                return true;
            } else
            {
                return false;
            }
        }

        protected void renderVA(DrawContext dc, IcosaTile tile, int numTextureUnits)
        {
            GL2 gl = dc.getGL().getGL2(); // GL initialization checks for GL2 compatibility.

            gl.glVertexPointer(3, GL2.GL_DOUBLE, 0, tile.ri.vertices.rewind());

            for (int i = 0; i < numTextureUnits; i++)
            {
                gl.glClientActiveTexture(GL2.GL_TEXTURE0 + i);
                gl.glEnableClientState(GL2.GL_TEXTURE_COORD_ARRAY);
                Object texCoords = dc.getValue(AVKey.TEXTURE_COORDINATES);
                if (texCoords != null && texCoords instanceof DoubleBuffer)
                {
                    gl.glTexCoordPointer(2, GL2.GL_DOUBLE, 0, ((DoubleBuffer) texCoords).rewind());
                } else
                {
                    gl.glTexCoordPointer(2, GL2.GL_DOUBLE, 0, tile.ri.texCoords.rewind());
                }
            }

            gl.glDrawElements(GL.GL_TRIANGLE_STRIP, tile.ri.indices.limit(), GL.GL_UNSIGNED_INT, tile.ri.indices.rewind());
        }

        protected boolean bindVbos(DrawContext dc, IcosaTile tile, int numTextureUnits)
        {
            int[] verticesVboId = (int[]) dc.getGpuResourceCache().get(tile.ri.vboCacheKey);
            if (verticesVboId == null)
            {
                tile.ri.fillVerticesVBO(dc);
                verticesVboId = (int[]) dc.getGpuResourceCache().get(tile.ri.vboCacheKey);
                if (verticesVboId == null)
                {
                    return false;
                }
            }

            GL2 gl = dc.getGL().getGL2(); // GL initialization checks for GL2 compatibility.

            // Bind vertices
            gl.glBindBuffer(GL.GL_ARRAY_BUFFER, verticesVboId[0]);
            gl.glVertexPointer(3, GL2.GL_DOUBLE, 0, 0);

            // Bind texture coordinates
            if (numTextureUnits > 0)
            {
                Object texCoordsVboCacheKey = textureCoordVboCacheKeys.get(tile.density);
                int[] texCoordsVboId = (int[]) (texCoordsVboCacheKey != null ? dc.getGpuResourceCache().get(texCoordsVboCacheKey) : null);
                if (texCoordsVboId == null)
                {
                    texCoordsVboId = this.fillTextureCoordsVbo(dc, tile.density, tile.ri.texCoords);
                }
                for (int i = 0; i < numTextureUnits; i++)
                {
                    gl.glClientActiveTexture(GL2.GL_TEXTURE0 + i);
                    gl.glEnableClientState(GL2.GL_TEXTURE_COORD_ARRAY);

                    gl.glBindBuffer(GL.GL_ARRAY_BUFFER, texCoordsVboId[0]);
                    gl.glTexCoordPointer(2, GL2.GL_DOUBLE, 0, 0);
                }
            }

            // Bind index list
            Object indexListVboCacheKey = indexListsVboCacheKeys.get(tile.density);
            int[] indexListVboId = (int[]) (indexListVboCacheKey != null ? dc.getGpuResourceCache().get(indexListVboCacheKey) : null);
            if (indexListVboId == null)
            {
                indexListVboId = this.fillIndexListVbo(dc, tile.density, tile.ri.indices);
            }
            if (indexListVboId != null)
            {
                gl.glBindBuffer(GL.GL_ELEMENT_ARRAY_BUFFER, indexListVboId[0]);
            }

            return indexListVboId != null;
        }

        protected int[] fillIndexListVbo(DrawContext dc, int density, IntBuffer indices)
        {
            GL gl = dc.getGL();

            Object indexListVboCacheKey = indexListsVboCacheKeys.get(density);
            int[] indexListVboId = (int[]) (indexListVboCacheKey != null ? dc.getGpuResourceCache().get(indexListVboCacheKey) : null);
            if (indexListVboId == null)
            {
                indexListVboId = new int[1];
                gl.glGenBuffers(indexListVboId.length, indexListVboId, 0);

                if (indexListVboCacheKey == null)
                {
                    indexListVboCacheKey = new Object();
                    indexListsVboCacheKeys.put(density, indexListVboCacheKey);
                }

                int size = indices.limit() * 4;
                dc.getGpuResourceCache().put(indexListVboCacheKey, indexListVboId, GpuResourceCache.VBO_BUFFERS, size);
            }

            try
            {
                gl.glBindBuffer(GL.GL_ELEMENT_ARRAY_BUFFER, indexListVboId[0]);
                gl.glBufferData(GL.GL_ELEMENT_ARRAY_BUFFER, indices.limit() * 4, indices.rewind(), GL.GL_STATIC_DRAW);
            } finally
            {
                gl.glBindBuffer(GL.GL_ELEMENT_ARRAY_BUFFER, 0);
            }

            return indexListVboId;
        }

        protected int[] fillTextureCoordsVbo(DrawContext dc, int density, DoubleBuffer texCoords)
        {
            GL gl = dc.getGL();

            Object texCoordVboCacheKey = textureCoordVboCacheKeys.get(density);
            int[] texCoordVboId = (int[]) (texCoordVboCacheKey != null ? dc.getGpuResourceCache().get(texCoordVboCacheKey) : null);
            if (texCoordVboId == null)
            {
                texCoordVboId = new int[1];
                gl.glGenBuffers(texCoordVboId.length, texCoordVboId, 0);

                if (texCoordVboCacheKey == null)
                {
                    texCoordVboCacheKey = new Object();
                    textureCoordVboCacheKeys.put(density, texCoordVboCacheKey);
                }

                int size = texCoords.limit() * 4;
                dc.getGpuResourceCache().put(texCoordVboCacheKey, texCoordVboId, GpuResourceCache.VBO_BUFFERS, size);
            }

            try
            {
                gl.glBindBuffer(GL.GL_ARRAY_BUFFER, texCoordVboId[0]);
                gl.glBufferData(GL.GL_ARRAY_BUFFER, texCoords.limit() * 4, texCoords.rewind(), GL.GL_STATIC_DRAW);
            } finally
            {
                gl.glBindBuffer(GL.GL_ARRAY_BUFFER, 0);
            }

            return texCoordVboId;
        }

        public void renderWireframe(DrawContext dc, IcosaTile tile, boolean showTriangles, boolean showTileBoundary)
        {
            if (dc == null)
            {
                String msg = Logging.getMessage("nullValue.DrawContextIsNull");
                Logging.logger().severe(msg);
                throw new IllegalArgumentException(msg);
            }

            if (tile.ri == null)
            {
                String msg = Logging.getMessage("nullValue.RenderInfoIsNull");
                Logging.logger().severe(msg);
                throw new IllegalStateException(msg);
            }

            dc.getView().pushReferenceCenter(dc, this.pCentroid);

            GL2 gl = dc.getGL().getGL2(); // GL initialization checks for GL2 compatibility.
            gl.glPushAttrib(
                    GL2.GL_DEPTH_BUFFER_BIT | GL2.GL_POLYGON_BIT | GL2.GL_ENABLE_BIT | GL2.GL_CURRENT_BIT);
            gl.glEnable(GL.GL_BLEND);
            gl.glBlendFunc(GL.GL_SRC_ALPHA, GL.GL_ONE);
            gl.glDisable(GL.GL_DEPTH_TEST);
            gl.glEnable(GL.GL_CULL_FACE);
            gl.glCullFace(GL.GL_BACK);
            gl.glColor4d(1d, 1d, 1d, 0.2);
            gl.glPolygonMode(GL2.GL_FRONT, GL2.GL_LINE);

            if (showTriangles)
            {
                OGLStackHandler ogsh = new OGLStackHandler();

                try
                {
                    ogsh.pushClientAttrib(gl, GL2.GL_CLIENT_VERTEX_ARRAY_BIT);

                    gl.glEnableClientState(GL2.GL_VERTEX_ARRAY);

                    gl.glVertexPointer(3, GL2.GL_DOUBLE, 0, tile.ri.vertices.rewind());
                    gl.glDrawElements(GL.GL_TRIANGLE_STRIP, tile.ri.indices.limit(),
                            GL.GL_UNSIGNED_INT, tile.ri.indices.rewind());
                } finally
                {
                    ogsh.pop(gl);
                }
            }

            dc.getView().popReferenceCenter(dc);

            gl.glPopAttrib();

            if (showTileBoundary)
            {
                this.renderPatchBoundary(gl);
            }
        }

        private void renderPatchBoundary(GL2 gl)
        {
            gl.glColor4d(1d, 0, 0, 1d);
            gl.glBegin(GL.GL_TRIANGLES);
            gl.glVertex3d(this.p0.x, this.p0.y, this.p0.z);
            gl.glVertex3d(this.p1.x, this.p1.y, this.p1.z);
            gl.glVertex3d(this.p2.x, this.p2.y, this.p2.z);
            gl.glEnd();
        }

        public void renderBoundingVolume(DrawContext dc)
        {
        }

        public Vec4 getSurfacePoint(Angle latitude, Angle longitude, double metersOffset)
        {
            // TODO: Replace below with interpolation over containing triangle.
            return this.globeInfo.globe.computePointFromPosition(latitude, longitude, metersOffset);
        }

        public void pick(DrawContext dc, java.awt.Point pickPoint)
        {
        }

        public long getSizeInBytes()
        {
            return this.byteSize;
        }

        public int compareTo(SectorGeometry that)
        {
            if (that == null)
            {
                String msg = Logging.getMessage("nullValue.GeometryIsNull");
                Logging.logger().severe(msg);
                throw new IllegalArgumentException(msg);
            }
            return this.getSector().compareTo(that.getSector());
        }

        public boolean equals(Object o)
        {
            if (this == o)
            {
                return true;
            }
            if (o == null || getClass() != o.getClass())
            {
                return false;
            }

            IcosaTile icosaTile = (IcosaTile) o;

            if (density != icosaTile.density)
            {
                return false;
            }
            if (level != icosaTile.level)
            {
                return false;
            }
            if (g0 != null ? !g0.equals(icosaTile.g0) : icosaTile.g0 != null)
            {
                return false;
            }
            if (g1 != null ? !g1.equals(icosaTile.g1) : icosaTile.g1 != null)
            {
                return false;
            }
            if (g2 != null ? !g2.equals(icosaTile.g2) : icosaTile.g2 != null)
            {
                return false;
            }
            if (globeInfo != null ? !globeInfo.equals(icosaTile.globeInfo) : icosaTile.globeInfo != null)
            {
                return false;
            }
            if (p0 != null ? !p0.equals(icosaTile.p0) : icosaTile.p0 != null)
            {
                return false;
            }
            if (p1 != null ? !p1.equals(icosaTile.p1) : icosaTile.p1 != null)
            {
                return false;
            }
            if (p2 != null ? !p2.equals(icosaTile.p2) : icosaTile.p2 != null)
            {
                return false;
            }
            if (this.getSector() != null ? !this.getSector().equals(icosaTile.getSector())
                    : icosaTile.getSector() != null)
            {
                return false;
            }
            if (unitp0 != null ? !unitp0.equals(icosaTile.unitp0) : icosaTile.unitp0 != null)
            {
                return false;
            }
            if (unitp1 != null ? !unitp1.equals(icosaTile.unitp1) : icosaTile.unitp1 != null)
            {
                return false;
            }
            //noinspection RedundantIfStatement
            if (unitp2 != null ? !unitp2.equals(icosaTile.unitp2) : icosaTile.unitp2 != null)
            {
                return false;
            }

            return true;
        }

        public int hashCode()
        {
            int result;
            result = level;
            result = 31 * result + (globeInfo != null ? globeInfo.hashCode() : 0);
            result = 31 * result + (g0 != null ? g0.hashCode() : 0);
            result = 31 * result + (g1 != null ? g1.hashCode() : 0);
            result = 31 * result + (g2 != null ? g2.hashCode() : 0);
            result = 31 * result + (this.getSector().hashCode());
            result = 31 * result + (unitp0 != null ? unitp0.hashCode() : 0);
            result = 31 * result + (unitp1 != null ? unitp1.hashCode() : 0);
            result = 31 * result + (unitp2 != null ? unitp2.hashCode() : 0);
            result = 31 * result + (p0 != null ? p0.hashCode() : 0);
            result = 31 * result + (p1 != null ? p1.hashCode() : 0);
            result = 31 * result + (p2 != null ? p2.hashCode() : 0);
            result = 31 * result + density;
            return result;
        }
    }

    // Angles used to form icosahedral triangles.
    private static Angle P30 = Angle.fromDegrees(30);
    private static Angle N30 = Angle.fromDegrees(-30);
    private static Angle P36 = Angle.fromDegrees(36);
    private static Angle N36 = Angle.fromDegrees(-36);
    private static Angle P72 = Angle.fromDegrees(72);
    private static Angle N72 = Angle.fromDegrees(-72);
    private static Angle P108 = Angle.fromDegrees(108);
    private static Angle N108 = Angle.fromDegrees(-108);
    private static Angle P144 = Angle.fromDegrees(144);
    private static Angle N144 = Angle.fromDegrees(-144);

    // Lat/lon of vertices of icosahedron aligned with lat/lon domain boundaries.
    private static final LatLon[] L0 =
    {
        new LatLon(Angle.POS90, N144), // 0
        new LatLon(Angle.POS90, N72), // 1
        new LatLon(Angle.POS90, Angle.ZERO), // 2
        new LatLon(Angle.POS90, P72), // 3
        new LatLon(Angle.POS90, P144), // 4
        new LatLon(P30, Angle.NEG180), // 5
        new LatLon(P30, N144), // 6
        new LatLon(P30, N108), // 7
        new LatLon(P30, N72), // 8
        new LatLon(P30, N36), // 9
        new LatLon(P30, Angle.ZERO), // 10
        new LatLon(P30, P36), // 11
        new LatLon(P30, P72), // 12
        new LatLon(P30, P108), // 13
        new LatLon(P30, P144), // 14
        new LatLon(P30, Angle.POS180), // 15
        new LatLon(N30, N144), // 16
        new LatLon(N30, N108), // 17
        new LatLon(N30, N72), // 18
        new LatLon(N30, N36), // 19
        new LatLon(N30, Angle.ZERO), // 20
        new LatLon(N30, P36), // 21
        new LatLon(N30, P72), // 22
        new LatLon(N30, P108), // 23
        new LatLon(N30, P144), // 24
        new LatLon(N30, Angle.POS180), // 25
        new LatLon(N30, N144), // 26
        new LatLon(Angle.NEG90, N108), // 27
        new LatLon(Angle.NEG90, N36), // 28
        new LatLon(Angle.NEG90, P36), // 29
        new LatLon(Angle.NEG90, P108), // 30
        new LatLon(Angle.NEG90, Angle.POS180), // 31
        new LatLon(P30, Angle.NEG180), // 32
        new LatLon(N30, Angle.NEG180), // 33
        new LatLon(Angle.NEG90, Angle.NEG180),
    }; // 34

    public static IcosaTile createTileFromAngles(GlobeInfo globeInfo, int level, LatLon g0, LatLon g1, LatLon g2, DrawContext dc)
    {
        return new IcosaTile(globeInfo, level, g0, g1, g2, dc);
    }

    private static java.util.ArrayList<IcosaTile> makeLevelZeroEquilateralTriangles(GlobeInfo globeInfo, DrawContext dc)
    {
        java.util.ArrayList<IcosaTile> topLevels = new java.util.ArrayList<IcosaTile>(22);

        // These lines form the level 0 icosahedral triangles. Two of the icosahedral triangles,
        // however, are split to form right triangles whose sides align with the longitude domain
        // limits (-180/180) so that no triangle spans the discontinuity between +180 and -180.
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[5], L0[7], L0[0], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[7], L0[9], L0[1], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[9], L0[11], L0[2], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[11], L0[13], L0[3], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[13], L0[15], L0[4], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[16], L0[7], L0[5], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[16], L0[18], L0[7], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[18], L0[9], L0[7], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[18], L0[20], L0[9], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[20], L0[11], L0[9], dc)); // triangle centered on 0 lat, 0 lon
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[20], L0[22], L0[11], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[22], L0[13], L0[11], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[22], L0[24], L0[13], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[24], L0[15], L0[13], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[24], L0[25], L0[15], dc)); // right triangle
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[33], L0[26], L0[32], dc)); // right triangle
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[27], L0[18], L0[16], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[28], L0[20], L0[18], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[29], L0[22], L0[20], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[30], L0[24], L0[22], dc));
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[25], L0[24], L0[31], dc)); // right triangle
        topLevels.add(createTileFromAngles(globeInfo, 0, L0[26], L0[33], L0[34], dc)); // right triangle

        return topLevels;
    }

    @SuppressWarnings(
            {
                "FieldCanBeLocal"
            })
    private Globe globe;
    @SuppressWarnings(
            {
                "FieldCanBeLocal"
            })
    private GlobeInfo globeInfo;
    private java.util.ArrayList<IcosaTile> topLevels;
    private SectorGeometryList currentTiles = new SectorGeometryList();
    private Frustum currentFrustum;
    private int currentLevel;
    private int maxLevel = DEFAULT_MAX_LEVEL;//14; // TODO: Make configurable
    private Sector sector; // union of all tiles selected during call to render()
    private int density = DEFAULT_DENSITY; // TODO: make configurable
    private boolean makeTileSkirts = true;

    public EllipsoidIcosahedralTessellator()
    {
    }

    public void setGlobe(Globe globe, DrawContext dc)
    {
        if (globe == null)
        {
            String msg = Logging.getMessage("nullValue.GlobeIsNull");
            Logging.logger().severe(msg);
            throw new IllegalArgumentException(msg);
        }

        this.globe = globe;
        this.globeInfo = new GlobeInfo(this.globe);
        this.topLevels = makeLevelZeroEquilateralTriangles(this.globeInfo, dc);
    }

    public Sector getSector()
    {
        return this.sector;
    }

    public SectorGeometryList tessellate(DrawContext dc)
    {
        View view = dc.getView();

        if (!WorldWind.getMemoryCacheSet().containsCache(CacheKey.class.getName()))
        {
            long size = Configuration.getLongValue(AVKey.SECTOR_GEOMETRY_CACHE_SIZE, 20000000L);
            MemoryCache cache = new BasicMemoryCache((long) (0.85 * size), size);
            WorldWind.getMemoryCacheSet().addCache(CacheKey.class.getName(), cache);
        }

        this.setGlobe(globe, dc);
        this.currentTiles.clear();
        this.currentLevel = 0;
        this.sector = null;

        this.currentFrustum = view.getFrustumInModelCoordinates();

        for (IcosaTile tile : topLevels)
        {
            this.selectVisibleTiles(tile, view, dc);
        }

        dc.setVisibleSector(this.getSector());

        return this.currentTiles;
    }

    private boolean needToSplit(IcosaTile tile, View view)
    {
        double d1 = view.getEyePoint().distanceTo3(tile.p0);
        double d2 = view.getEyePoint().distanceTo3(tile.p1);
        double d3 = view.getEyePoint().distanceTo3(tile.p2);
        double d4 = view.getEyePoint().distanceTo3(tile.pCentroid);

        double minDistance = d1;
        if (d2 < minDistance)
        {
            minDistance = d2;
        }
        if (d3 < minDistance)
        {
            minDistance = d3;
        }
        if (d4 < minDistance)
        {
            minDistance = d4;
        }

        // Meets criteria when the texel size is less than the size of some number of pixels.
        double pixelSize = view.computePixelSizeAtDistance(minDistance);
        return tile.edgeLength / this.density >= 30d * (2d * pixelSize); // 2x pixel size to compensate for view bug
    }

    public boolean isMakeTileSkirts()
    {
        return makeTileSkirts;
    }

    public void setMakeTileSkirts(boolean makeTileSkirts)
    {
        this.makeTileSkirts = makeTileSkirts;
    }

    private void selectVisibleTiles(IcosaTile tile, View view, DrawContext dc)
    {
        if (!tile.getExtent().intersects(this.currentFrustum))
        {
            return;
        }

        if (this.currentLevel < this.maxLevel && this.needToSplit(tile, view))
        {
            ++this.currentLevel;
            IcosaTile[] subtiles = tile.split(dc, tile);
            for (IcosaTile child : subtiles)
            {
                this.selectVisibleTiles(child, view, dc);
            }
            --this.currentLevel;
            return;
        }
        this.sector = tile.getSector().union(this.sector);
        this.currentTiles.add(tile);
    }

    private static class CacheKey
    {

        private final Vec4 centroid;
        private int resolution;
        private final double verticalExaggeration;
        private int density;

        private CacheKey(IcosaTile tile, double verticalExaggeration, int density)
        {
            // private class, no validation required.
            this.centroid = tile.pCentroid;
            this.verticalExaggeration = verticalExaggeration;
            this.density = density;
        }

        @Override
        public String toString()
        {
            return "density " + this.density + " ve " + this.verticalExaggeration + " resolution " + this.resolution;
//                + " g0 " + this.g0 + " g1 " + this.g1 + " g2 " + this.g2;
        }

        public boolean equals(Object o)
        {
            if (this == o)
            {
                return true;
            }
            if (o == null || getClass() != o.getClass())
            {
                return false;
            }

            CacheKey cacheKey = (CacheKey) o;

            if (density != cacheKey.density)
            {
                return false;
            }
            if (Double.compare(cacheKey.verticalExaggeration, verticalExaggeration) != 0)
            {
                return false;
            }
            //noinspection RedundantIfStatement
            if (centroid != null ? !centroid.equals(cacheKey.centroid) : cacheKey.centroid != null)
            {
                return false;
            }

            return true;
        }

        public int hashCode()
        {
            int result;
            long temp;
            result = (centroid != null ? centroid.hashCode() : 0);
            temp = verticalExaggeration != +0.0d ? Double.doubleToLongBits(verticalExaggeration) : 0L;
            result = 31 * result + (int) (temp ^ (temp >>> 32));
            result = 31 * result + density;
            return result;
        }
    }
}
