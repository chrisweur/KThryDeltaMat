-*-------------------------------------------------------------------------------------
Examples in "K-classes of delta-matroids and equivariant localization"

Needs the file "KThryDeltaMat_upload.m2"
-------------------------------------------------------------------------------------*-

--Example 5.1
restart
load "KThryDeltaMat_upload.m2"
n = 3
D = subsets(n,1) | subsets(n,3)
fastPushPull(D,n)
S = QQ[q]; interlacePolynomial(D,n,S)


--Example 5.2
restart
load "KThryDeltaMat_upload.m2"
n = 4
D = subsets(n,0) | subsets(n,1) | subsets(n,3)
fastPushPull(D,n)
S = QQ[q]; interlacePolynomial(D,n,S)


--Examples not featured in the paper
restart
load "KThryDeltaMat_upload.m2"
n = 5
D = {{0, 2, 3, 4}, {2, 3, 4}, {0, 1, 3, 4}, {1, 3, 4}, {3, 4}, {0, 1, 2, 4}, {1, 2, 4}, {2, 4},
       {0, 1, 4}, {1, 4}, {0, 4}, {0, 1, 2, 3}, {1, 2, 3}, {2, 3}, {0, 1, 3}, {1, 3}, {0, 3}, {0,
       1, 2}, {1, 2}, {0, 2}, {0, 1}, {1}, {}}
testVeryAmple basisIndicatorMatrix(D,n)
fastPushPull(D,n,Timed=>true)
S = QQ[q]; interlacePolynomial(D,n,S)

D = {{1, 3, 4}, {0, 3, 4}, {1, 2, 4}, {0, 2, 4}, {4}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {3}, {0, 1, 2}, {0, 2}, {2}, {1}, {0}}
fastPushPull(D,n,Timed=>true)
S = QQ[q]; interlacePolynomial(D,n,S)

--Example 5.3
restart
load "KThryDeltaMat_upload.m2"
n = 7
G = graph{{1,2},{1,3},{2,3},{3,4},{4,5},{5,6},{5,7},{6,7}}
A = sub(adjacencyMatrix G,GF(2))
D = select(subsets n, s -> #s == 0 or determinant A_s^s != 0)
--uncomment below to run. Caution: takes about 3600 seconds on germain.math.harvard.edu
--fastPushPull(D,n,Timed=>true)
S = QQ[q]; interlacePolynomial(D,n,S)
 
