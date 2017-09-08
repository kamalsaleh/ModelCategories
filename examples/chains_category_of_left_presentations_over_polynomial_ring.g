
LoadPackage( "ModelCategories" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ModulePresentations" );

R := HomalgFieldOfRationalsInSingular( )*"x,y,z";;
cat := LeftPresentations( R: FinalizeCategory := false );
#! Category of left presentations of Q[x,y,z]
AddEpimorphismFromSomeProjectiveObject( cat, CoverByFreeModule );
SetHasEnoughProjectives( cat, true );
AddIsProjective( cat, function( P ) 
                      return not Lift( IdentityMorphism( P ), CoverByFreeModule( P ) ) = fail;
                      end );
Finalize( cat );
chains := ChainComplexCategory( cat : FinalizeCategory := false );
ModelStructureOnChainComplexes( chains );
Finalize( chains );

F := FreeLeftPresentation( 1, R );

C := ChainComplex( [ IdentityMorphism( F ) ], 1 );

YY := DirectSum( [ C, ShiftLazy( C, -1 ) ] );

XX := DirectSum( [ YY, ShiftLazy( C, 1 ) ] );

g := ProjectionInFactorOfDirectSum( [ YY, ShiftLazy( C, 1 ) ], 1 );

A := DirectSum( XX, ShiftLazy( C, 2 ) );

u := ProjectionInFactorOfDirectSum( [ XX, ShiftLazy( C, 2 ) ], 1 );

P := DirectSum( [ C, ShiftLazy( C, 1 ), ShiftLazy( C, -1 ), ShiftLazy( C, -2 ) ] );

B := DirectSum( A, P );

f := InjectionOfCofactorOfDirectSum( [ A, P ], 1 );

v := PreCompose( [ ProjectionInFactorOfDirectSum( [ A, P ], 1 ), u , g ] );

#            u
#       A -----> XX
#       |        | 
#     f |        | g
#       |        | 
#       V        V
#       B -----> YY
#            v

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
Display( Q[ 3 ] );
Display( Q[ 4 ] );
Display( Q[ 5 ] );
SetUpperBound( Q, 4 );
IsAcyclicFibration( v );


