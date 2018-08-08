
LoadPackage( "ModulePresentations" );
LoadPackage( "ModelCategories" );
LoadPackage( "TriangulatedCategoriesForCAP" );

ReadPackage( "ModelCategories", "examples/left_homotopy_in_complexes_of_l_p_over_comm_homalg_ring.g" );
ReadPackage( "ModelCategories", "examples/Triangulated_Structure.g" );

R := HomalgFieldOfRationalsInSingular()*"x,y,z";;
cat := LeftPresentations( R: FinalizeCategory := false );
AddEpimorphismFromSomeProjectiveObject( cat, CoverByFreeModule );
SetIsAbelianCategoryWithEnoughProjectives( cat, true );
AddIsProjective( cat, function( P ) 
                        return not Lift( IdentityMorphism( P ), CoverByFreeModule( P ) ) = fail;
                      end );
Finalize( cat );

chains := ChainComplexCategory( cat : FinalizeCategory := false );
ModelStructureOnChainComplexes( chains );
AddLift( chains, compute_lifts_in_chains );
AddColift( chains, compute_colifts_in_chains );

## These are general categorical operation, not only in context of Model categories.
AddIsNullHomotopic( chains, phi -> not Colift( NaturalInjectionInMappingCone( IdentityMorphism( Source( phi ) ) ), phi ) = fail );
AddHomotopyMorphisms( chains, compute_homotopy_chain_morphisms_for_null_homotopic_morphism );

AddAreLeftHomotopic( chains, 
    function( phi, psi )
        return IsNullHomotopic( phi - psi );
        #return is_left_homotopic_to_null( phi - psi );
    end );

Finalize( chains );

homotopy_chains := HomotopyCategory( chains :FinalizeCategory := false );
AddTriangulatedStructure( homotopy_chains );
Finalize( homotopy_chains );

m := HomalgMatrix( "[ x,y,0,z,-x,y ]", 2, 3, R );

n := HomalgMatrix( "[ x+y,x-y,z,y,0,-x,0,z ]", 4, 2, R );

p := HomalgMatrix( "[ x-y,x+y, 2x,y,z,y+z,-x,0,-x,z,0,z ]", 4, 3, R );

M := AsLeftPresentation( m );

N := AsLeftPresentation( n );

P := AsLeftPresentation( p );

CM := StalkChainComplex( M, 1 );

CN := StalkChainComplex( N, 1 );

CP := StalkChainComplex( P, 1 );

G_MN := GeneratorsOfExternalHom( CM, CN );

G_NP := GeneratorsOfExternalHom( CN, CP );

f := Random( G_MN );

g := Random( G_NP );

hf := AsMorphismInHomotopyCategory( f );

hg := AsMorphismInHomotopyCategory( g );

tr := OctahedralAxiom( hf, hg );

IsStandardExactTriangle( tr );

i := IsomorphismIntoStandardExactTriangle( tr );

j := IsomorphismFromStandardExactTriangle( tr );

ij := PreCompose(i,j);

ji := PreCompose(j,i);

IsCongruentForMorphisms( ij, IdentityMorphism( Source(i) ) );

IsIsomorphism( ji );

rot_tr := RotationOfExactTriangle(tr);

IsWellDefined( rot_tr );