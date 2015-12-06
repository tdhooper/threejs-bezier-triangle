/**
 * Most of this is taken from https://github.com/pixelperfect3/BezierView
 * but creates cleaner geometry.
 */

THREE.BezierTriangleGeometry = function(points, degree, subdivisions) {

    THREE.Geometry.call( this );

    /** UTILITY FUNCTIONS **/

    // Mapping functions for triangular bezier surfaces
    // barycentral coordinate mapping to 1d array index
    // according to j & k
    // i.e. when (i,j,k) has the property: (i+j+k<d)
    //             (i,j,k)    will go to 
    //              /
    //          ((d-j-k), j, k)
    // 
    // this provides a certain way of overwriting points in DeCastejel
    // algorithm, so that the intermediate values can be used to
    // calculate derivatives and curvatures.

    /*
    //                  /\ C(i,j,k+1)
    //                 /  \
    //                /    \
    //               /      \      P will overwrite A
    //              /    .   \
    //             / P(i,j,k) \
    //  A(i+1,j,k)/____________\ B(i,j+1,k)
    */

    function b2i_i (i, j, k, d)
    {
        var lk = 0;
        var kk = 0;

        for (kk = 0 ; kk <k; kk++)
        {
            lk += (d+1-kk);
        }
        
        //console.log("Returning: " + (lk+j));
        return lk+j;
    }

    /* mapping function according to i & k
    // i.e. when (i,j,k) has the property: (i+j+k<d)
    //             (i,j,k)    will go to
    //                \ 
    //             (i, (d-i-k), k)
    //  
    // this provides another way of overwriting points in DeCasteljau
    //  algorithm.
    //  
    //  P will overwrite B in same graph in b2i_i
    */
    function b2i_j (i, j, k, d)
    {
        var lk = 0;
        var kk = 0;

        // d = i+j+k;
        for (kk = 0 ; kk <k; kk++)
        {
            lk += (d+1-kk);
        }
        //console.log("Returning: " + (lk+(d-i-k)));
        return lk+ (d-i-k);
    } 

    // mapping function according to j & i
    // i.e. when (i,j,k) has the property: (i+j+k<d)
    //                (i,j,(d-i-j))
    //                 /
    //             (i,j,k)    will go to
    //
    // this provides the third way of overwriting points in DeCasteljau
    //  algorithm.
    //  
    //  P will overwrite C in same graph in b2i_i
    //
    function b2i_k (i, j, k, d)
    {
        var lk = 0;
        var kk = 0;
        k = d-i-j;

        for (kk = 0 ; kk <k; kk++)
        {
            lk += (d+1-kk);
        }
        //console.log("Returning: " + (lk+j));
        return lk+j;
    }

    function evalPN(v00, v01, v10, P, N)
    {
        var rv00 = new THREE.Vector3().fromArray(v00.toArray()).divideScalar(v00.w);
        var rv10 = new THREE.Vector3().fromArray(v10.toArray()).divideScalar(v10.w);
        var rv01 = new THREE.Vector3().fromArray(v01.toArray()).divideScalar(v01.w);
        rv10.sub(rv00);
        rv01.sub(rv00);
        N.copy(rv10.cross(rv01));
        P.copy(rv00);
    }

    // BUILD

    var     i,j,k;
    var     m;
    var     u, v, w; /* parameter of patch */ 
    var     uu, vv;
    var     loc = 0;   /* increase 1 for each point computed */
    var     size;

    var deg = degree;
    var MAXDEG = deg;
    var DIM = 4;

    // initialize the decasteljau array
    var DeCastel = new Array((MAXDEG+1)*(MAXDEG+2)/2);
    for (var i = 0; i < (MAXDEG+1)*(MAXDEG+2)/2; i++) {
        DeCastel[i] = new THREE.Vector4();
    }

    // the mapping function
    var b2i;

    pts  = 1 << subdivisions;

    /* allocate the memory for evaluation */
    size = (pts+1)*(pts+2)/2;
    var eval_P = new Array(size);
    var eval_N = new Array(size);
    
    for(var i = 0; i < size; i++) {
        eval_P[i] = new THREE.Vector3();
        eval_N[i] = new THREE.Vector3();
    }

    for (var uu=0; uu<=pts; uu++)
    {
        for (var vv=0;vv<=pts-uu;vv++)
        {
            var point = new THREE.Vector4();
            var h;
            var V00, V01, V02, V10, V20, V11;

            var onbdy = (uu==0) ;  // on the boundary
            var atvtx = (uu==0 && vv==0); 

            u = uu/pts;
            v = vv/pts;
            w = 1-u-v;

            // use two different mapping functions
            //  for the interior and the boundary
            if (atvtx)
                b2i = b2i_k;
            else if (onbdy)    
                b2i = b2i_j;
            else
                b2i = b2i_i;

            /* initialize the DeCastel Array */
            for (var i = 0; i <= deg; i++) {
                for(var j=0; j <= deg - i; j++) {
                    k = deg -i-j;
                    DeCastel[b2i(i,j,k, deg)].copy( 
                        points[b2i(i,j,k, deg)]
                    ); 
                }
            }

            /* de Casteljau algorithm */
            for (var d = deg - 1; d >= 1; d--) {
                for (var k=0; k <= d; k++) {
                    for (var j = 0; j <= d - k; j++) {
                        var i = d-j-k;

                        var index = b2i(i,j,k,deg);
                        DeCastel[index].x =
                            u * DeCastel[b2i(i+1,j,k,deg)].x +
                            v * DeCastel[b2i(i,j+1,k,deg)].x +
                            w * DeCastel[b2i(i,j,k+1,deg)].x;
                        
                        DeCastel[index].y =
                            u * DeCastel[b2i(i+1,j,k,deg)].y +
                            v * DeCastel[b2i(i,j+1,k,deg)].y +
                            w * DeCastel[b2i(i,j,k+1,deg)].y;
                                            
                        DeCastel[index].z =
                            u * DeCastel[b2i(i+1,j,k,deg)].z +
                            v * DeCastel[b2i(i,j+1,k,deg)].z +
                            w * DeCastel[b2i(i,j,k+1,deg)].z;
                    }
                }
            }

            /* Last step of de Casteljau algorithm */
            point.x  = u* DeCastel[b2i(1,0,0,deg)].x +
                       v* DeCastel[b2i(0,1,0,deg)].x +
                       w* DeCastel[b2i(0,0,1,deg)].x;
            point.y  = u* DeCastel[b2i(1,0,0,deg)].y +
                       v* DeCastel[b2i(0,1,0,deg)].y +
                       w* DeCastel[b2i(0,0,1,deg)].y;
            
            point.z  = u* DeCastel[b2i(1,0,0,deg)].z +
                       v* DeCastel[b2i(0,1,0,deg)].z +
                       w* DeCastel[b2i(0,0,1,deg)].z;

            V00 = point;
            if (atvtx )   {
                V01   = DeCastel[b2i(0,1,0,deg)];
                V10   = DeCastel[b2i(1,0,0,deg)];
            } else if (onbdy) {
                V01   = DeCastel[b2i(1,0,0,deg)];
                V10   = DeCastel[b2i(0,0,1,deg)];
            } else {
                V01   = DeCastel[b2i(0,0,1,deg)];
                V10   = DeCastel[b2i(0,1,0,deg)];
            }

            // compute the point and the normal at the (u,v) parameter
            evalPN(V00, V01, V10, eval_P[loc], eval_N[loc]);

            loc ++;
        }
    }

    for (var i = 0; i < size; i++) {
        this.vertices.push(eval_P[i]);
    }

    var a, b, c;
    var v1, v2, v3, v4;
    var n1, n2, n3, n4;

    for(var i = 0; i < pts; i++) {
        for(var j = 0; j < pts - i + 1; j++) {
            a = i;
            b = j;
            c = pts-i-j;

            v1 = b2i_i(a, b, c, pts);
            v2 = b2i_i(a, b+1, c-1, pts);
            v3 = b2i_i(a+1, b, c-1, pts);
            v4 = b2i_i(a+1, b+1, c-2, pts);

            n1 = eval_N[v1];
            n2 = eval_N[v2];
            n3 = eval_N[v3];
            n4 = eval_N[v4];

            if (j < pts - i) {
                this.faces.push( new THREE.Face3(v1, v2, v3, [n1, n2, n3]) );
            }
            if (j < pts - i - 1) {
                this.faces.push( new THREE.Face3(v4, v2, v3, [n4, n2, n3]) );
            }
        }
    }
};

THREE.BezierTriangleGeometry.prototype = Object.create( THREE.Geometry.prototype );
THREE.BezierTriangleGeometry.prototype.constructor = THREE.BezierTriangleGeometry;
