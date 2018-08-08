# Please pull the branch devel2 or mohamed of QPA2 at https://github.com/kamalsaleh/QPA2
ReadPackage( "ModelCategories", "examples/left_homotopy_in_chains_of_rep_over_quiver.g" );

field := Rationals;

# There are still methods in qpa that don't work with homalg fields.

# field := HomalgFieldOfRationals();

# function to create the required data for the Beilinson quiver of D(P^2).

# Beilinson Quiver for P^d, d= 2

#         x10            x20
#  1 ---  x11 ---> 2 --- x21 ---> 3
#         x12            x22

P := BeilinsonQuiverWithRelations( field, 2 );;

Q := P[1];

kQ := P[2];

AQ := P[3];

cat := CategoryOfQuiverRepresentations( AQ: FinalizeCategory := false );

SetIsAbelianCategoryWithEnoughProjectives( cat, true );

AddEpimorphismFromSomeProjectiveObject( cat, ProjectiveCover );

AddIsProjective( cat, function( R )
                        return IsIsomorphism( ProjectiveCover( R ) ) ;
                      end );

AddLift( cat, compute_lift_in_quiver_rep );

AddColift( cat, compute_colift_in_quiver_rep );

Finalize( cat );

chains := ChainComplexCategory( cat: FinalizeCategory := false );

AddLift( chains, compute_lifts_in_complexes );

AddColift( chains, compute_colifts_in_complexes );

AddIsNullHomotopic( chains, phi -> not Colift( NaturalInjectionInMappingCone( IdentityMorphism( Source( phi ) ) ), phi ) = fail );

AddHomotopyMorphisms( chains, compute_homotopy_chain_morphisms_for_null_homotopic_morphism );

ModelStructureOnChainComplexes( chains );

AddAreLeftHomotopic( chains,
    function( phi, psi )
        return IsNullHomotopic( phi - psi );
    end );

Finalize( chains );

homotopy_chains := HomotopyCategory( chains );

AddTriangulatedStructure( homotopy_chains );

# The indecomposable projective objects of the quiver

indec_projectives := IndecProjRepresentations( AQ );

p1 := indec_projectives[1];

p2 := indec_projectives[2];

p3 := indec_projectives[3];

C1 := StalkChainComplex( p1, 0 );

C2 := StalkChainComplex( p2, 0 );

C3 := StalkChainComplex( p3, 0 );

B21 := BasisOfExternalHom( C2, C1 );

B32 := BasisOfExternalHom( C3, C2 );

B31 := BasisOfExternalHom( C3, C1 );

f := Random( B32 );

IsNullHomotopic( f );

IsMonomorphism( f );

IsEpimorphism( f );

K := CokernelObject( f );

hK := AsObjectInHomotopyCategory( K );

IsIdenticalObj( UnderlyingObject( hK ), K );

rep_hK := UnderlyingReplacement( hK );

# so each object in the homotopy category has an underlying object and underlying replacement.

hf := AsMorphismInHomotopyCategory( f );

IsZeroForMorphisms( hf );

Display( hf );

IsWellDefined( hf );

IsIdenticalObj( UnderlyingMorphism( hf), f );

rep_hf := UnderlyingReplacement( hf );

Display( rep_hf );

# each morphism in the homotopy category has an underlying replacement, but not always an underying morphism.

# Until now the homotopy category is "standard" triangulated category.
# i.e., 
# * We have an algorithm that completes a morphism to an exact triangle ( we call it standard exact triangle )
# * Every output that is supposed to be exact triangle should have evidence that it is indeed exact, i.e., 
#   a morphism from/to a standard exact triangle.
# * In order to have a full computable triangulated category (as in the case of stable of lp over exterior algebra)
#   we need a method LiftColift
# * In a standard triangulated category we may compute some axioms on exact triangles that have isomorphisms into/from
#   standard triangles.

tr_hf := CompleteMorphismToStandardExactTriangle( hf );

IsWellDefined( tr_hf );

Display( tr_hf );

tr_hf[0];tr_hf[1]; tr_hf[2];tr_hf[3];

tr_hf^0; tr_hf^1; tr_hf^2;

rot_tr_hf := RotationOfStandardExactTriangle( tr_hf );

IsStandardExactTriangle( rot_tr_hf );

IsomorphismIntoStandardExactTriangle( rot_tr_hf );

IsomorphismFromStandardExactTriangle( rot_tr_hf );

rot_rot_tr_hf := RotationOfExactTriangle( rot_tr_hf );

IsomorphismIntoStandardExactTriangle( rot_rot_tr_hf );

IsomorphismFromStandardExactTriangle( rot_rot_tr_hf );

ShiftOfObject( hK );

ReverseShiftOfObject( hK );

f := Random( B32 );

g := Random( B21 );

hf := AsMorphismInHomotopyCategory( f );

hg := AsMorphismInHomotopyCategory( g );

# computing Octahedral axiom may take 

octa_hf_hg := OctahedralAxiom( hf, hg );

IsWellDefined( octa_hf_hg );

i := IsomorphismFromStandardExactTriangle( octa_hf_hg );

Display( i );

j := IsomorphismIntoStandardExactTriangle( octa_hf_hg );

Display( j );