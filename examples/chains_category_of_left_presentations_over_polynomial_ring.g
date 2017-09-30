
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

M := HomalgMatrix( "[ x,y,0,z,-x,y ]", 2, 3, R );
N := HomalgMatrix( "[ x+y,x-y,\
> z,y,\
> 0,-x,\
> 0,z ]", 4, 2, R );
A := HomalgMatrix( "[ \
> x+y,0,\
> x+y,-x,\
> -x-y-z,2x ]", 3, 2, R );
M := AsLeftPresentation( M );
N := AsLeftPresentation( N );
phi := PresentationMorphism( M, A, N );
MM := StalkChainComplex( M, 1 );
NN := StalkChainComplex( N, 1 );
psi := ChainMorphism( MM, NN, [ phi ], 1 );
t := FactorThroughAcyclicCofibration( psi );
# [ <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>, 
#  <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2> ]
u := t[ 1 ];
#<A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
v := t[ 2 ];
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
IsEqualForMorphisms( psi, PreCompose( u, v ) );
# false
IsCongruentForMorphisms( psi, PreCompose( u, v ) );
# true
Range( u );
# <A bounded from below object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound -1>
IsZero( Range( u )[ 3 ] );
# true
IsZero( Range( u )[ 4 ] );
# true
IsZero( Range( u )[ 2 ] );
# false
SetUpperBound( Range( u ), 3 );
IsAcyclicCofibration( u );
# true
IsFibration( v );
# true
s := FactorThroughAcyclicFibration( psi );
# [ <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>, 
#   <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2> ]
u := s[ 1 ];
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
v := s[ 2 ];
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
IsEqualForMorphisms( psi, PreCompose( u, v ) );
# true
Range( u );
# <A bounded from below object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0>
IsZero( Range( u )[ 3 ] );
# false
IsZero( Range( u )[ 4 ] );
# false
IsZero( Range( u )[ 5 ] );
# true
IsZero( Range( u )[ 6 ] );
# true
SetUpperBound( Range( u ), 5 );
IsCofibration( u );
# true
IsAcyclicFibration( v );
# true