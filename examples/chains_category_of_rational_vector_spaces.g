LoadPackage( "LinearAlgebra" );
LoadPackage( "ModelCategories" );

 Q := HomalgFieldOfRationals( );
 vec_spaces := MatrixCategory( Q: FinalizeCategory := false );
 AddIsProjective( vec_spaces, ReturnTrue );
 AddEpimorphismFromSomeProjectiveObject( vec_spaces, IdentityMorphism );
 SetIsAbelianCategoryWithEnoughProjectives( vec_spaces, true );
 Finalize( vec_spaces );

 chains := ChainComplexCategory( vec_spaces : FinalizeCategory := false );
 ModelStructureOnChainComplexes( chains );
 Finalize( chains );

 K := VectorSpaceObject( 1, Q );
 id := IdentityMorphism( K );
 P := DirectSum( List( [ 1 .. 10 ], i -> ChainComplex( [ i*id ], i ) ) );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 11>
 P := DirectSum( [ P, ShiftLazy( P, 1 ), ShiftLazy( P, -1 ) ] );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -2 and active upper bound 12>
 P := DirectSum( [ P, ShiftLazy( P, 1 ), ShiftLazy( P, -1 ) ] );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -3 and active upper bound 13>
 A := DirectSum( [ ChainComplex( [ id ], 1 ), StalkChainComplex( K, 2 ), StalkChainComplex( K, 5 ), StalkChainComplex( K, 9 ) ] );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 10>
 quit();
 f := InjectionOfCofactorOfDirectSum( [ A, P ], 1 );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 10>
 IsWellDefined( f );
 # true
 XX := DirectSum( [ ChainComplex( [ id ], -1 ), StalkChainComplex( K, 1 ), StalkChainComplex( K, 6 ), StalkChainComplex( K, 8 ) ] );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -3 and active upper bound 9>
 internal_hom_A_XX := InternalHomOnObjects( A, XX );
 #<A bounded object in chain complexes category over category of matrices over Q with active lower bound -12 and active upper bound 9>
 Source( CyclesAt( internal_hom_A_XX, 0 ) );
 #<A vector space object over Q of dimension 1>
 gg := ChainMorphism( StalkChainComplex( K, 0 ), internal_hom_A_XX, [ CyclesAt( internal_hom_A_XX, 0 ) ], 0 );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 1>
 u := InternalHomToTensorProductAdjunctionMap( A, XX, gg );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 9>
 Source( u ) = A;
 #true
 Range( u ) = XX;
 #true
 t := PreCompose(ProjectionInFactorOfDirectSum( [ A, P ], 1 ), u );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound -1 and active upper bound 9>
 g := ProjectionInFactorOfDirectSum( [ ChainComplex( [ id ], -1 ), StalkChainComplex( K, 1 ), StalkChainComplex( K, 6 ), StalkChainComplex( K, 8 ) ], 3 );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound 5 and active upper bound 7>
 v := PreCompose( t, g );
 #<A bounded morphism in chain complexes category over category of matrices over Q with active lower bound 5 and active upper bound 7>
 IsEqualForMorphisms( PreCompose( u, g ), PreCompose( f, v ) );
 #true
 
IsAcyclicCofibration( f );
IsFibration( g );
t := Lifting( f, g, u, v );
IsEqualForMorphisms( PreCompose( f, t ), u );
IsEqualForMorphisms( PreCompose( t, g ), v );

# Or you can try

# IsCofibration( f );
# IsAcyclicFibration( g );
# t := Lifting( f, g, u, v );
# IsEqualForMorphisms( PreCompose( f, t ), u );
# IsEqualForMorphisms( PreCompose( t, g ), v );

IsAcyclicFibration( f );
t := FactorThroughAcyclicFibration( f );
u := t[ 1 ];
v := t[ 2 ];
IsCofibration( u );
Q := Source( v );
Display( Q[ 4 ] );
Display( Q[ 13 ] );
Display( Q[ 14 ] );
SetUpperBound( Q, 13 );
IsAcyclicFibration( v );


