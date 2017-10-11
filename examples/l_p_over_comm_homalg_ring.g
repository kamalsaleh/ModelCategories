
Read( "/home/saleh/Documents/gap_packages/local/pkg/ModelCategories/examples/left_homotopy_in_complexes_of_l_p_over_comm_homalg_ring.g" );

LoadPackage( "ModelCategories" );

R := HomalgRingOfIntegers( );;
cat := LeftPresentations( R: FinalizeCategory := false );
AddEpimorphismFromSomeProjectiveObject( cat, CoverByFreeModule );
SetHasEnoughProjectives( cat, true );
AddIsProjective( cat, function( P ) 
                      return not Lift( IdentityMorphism( P ), CoverByFreeModule( P ) ) = fail;
                      end );
Finalize( cat );
chains := ChainComplexCategory( cat : FinalizeCategory := false );
ModelStructureOnChainComplexes( chains );
AddAreLeftHomotopic( chains, 
    function( phi, psi )
        return is_left_homotopic_to_null( phi - psi );
    end );
Finalize( chains );

A := FreeLeftPresentation( 1, R );
id_A := IdentityMorphism( A );
phi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 10*id_A ], 1 );
psi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 5*id_A ], 1 );

phi_ := AsMorphismInHomotopyCategory( phi );
psi_ := AsMorphismInHomotopyCategory( psi );


