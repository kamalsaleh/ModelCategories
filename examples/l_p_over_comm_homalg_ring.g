
Read( "/home/saleh/Documents/gap_packages/local/pkg/ModelCategories/examples/left_homotopy_in_complexes_of_l_p_over_comm_homalg_ring.g" );

LoadPackage( "ModelCategories" );

ZZ := HomalgRingOfIntegers( );;
cat := LeftPresentations( ZZ: FinalizeCategory := false );
AddEpimorphismFromSomeProjectiveObject( cat, CoverByFreeModule );
SetIsAbelianCategoryWithEnoughProjectives( cat, true );
AddIsProjective( cat, function( P ) 
                      return not Lift( IdentityMorphism( P ), CoverByFreeModule( P ) ) = fail;
                      end );
Finalize( cat );

Z6 := AsLeftPresentation( HomalgMatrix( "[ [ 6 ] ]", 1, 1, ZZ ) );

chains := ChainComplexCategory( cat : FinalizeCategory := false );
ModelStructureOnChainComplexes( chains );
AddAreLeftHomotopic( chains, 
    function( phi, psi )
        return is_left_homotopic_to_null( phi - psi );
    end );
Finalize( chains );

Tensor_product_with_Z6 := CapFunctor( "Tensor product with Z/<6>", cat, cat );
AddObjectFunction( Tensor_product_with_Z6, 
    function( obj )
    return TensorProductOnObjects( obj, Z6 );
    end );
AddMorphismFunction( Tensor_product_with_Z6, 
    function( obj1, mor, obj2 )
    return TensorProductOnMorphisms( mor, IdentityMorphism( Z6 ) );
    end );
    
Tensor_product_with_Z6_in_chains := ExtendFunctorToChainComplexCategoryFunctor( Tensor_product_with_Z6 );

Z4 := AsLeftPresentation( HomalgMatrix( "[ [ 4 ] ]", 1, 1, ZZ ) );

C_Z4 := StalkChainComplex( Z4, 0 );

proj_res_of_Z4 := ProjectiveResolution( C_Z4 );

proj_res_of_Z4_tenor_Z6 := ApplyFunctor( Tensor_product_with_Z6_in_chains, proj_res_of_Z4 );

# Now in theory, we have the following facts
# Tor_0( Z/<m>, Z/<n> ) = Z/<m> tensor Z/<n> = Z/<gcd(m,n)> 
# Tor_1( Z/<m>, Z/<n> ) = Z/<gcd(m,n)> 

Tor_0 := HomologyAt( proj_res_of_Z4_tenor_Z6, 0 );
Display( Tor_0 );
# [ [   2 ],
#   [  -6 ] ]
# 
# An object in Category of left presentations of Z

#                      [  2 ]            [ 2 ]
# I.e., Tor_0 = Coker( [ -6 ] ) = Coker( [ 0 ] ) = Z/<2>

Tor_1 := HomologyAt( proj_res_of_Z4_tenor_Z6, 1 );
Display( Tor_1 );
# [ [  -2 ] ]
# 
# An object in Category of left presentations of Z
quit();

A := FreeLeftPresentation( 1, ZZ );
id_A := IdentityMorphism( A );
phi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 10*id_A ], 1 );
psi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 5*id_A ], 1 );

phi_ := AsMorphismInHomotopyCategory( phi );
psi_ := AsMorphismInHomotopyCategory( psi );


