
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

# The functor: __ tensor Z/<6>
Tensor_product_with_Z6 := CapFunctor( "Tensor product with Z/<6>", cat, cat );
AddObjectFunction( Tensor_product_with_Z6, 
    function( obj )
    return TensorProductOnObjects( obj, Z6 );
    end );
AddMorphismFunction( Tensor_product_with_Z6, 
    function( obj1, mor, obj2 )
    return TensorProductOnMorphisms( mor, IdentityMorphism( Z6 ) );
    end );
    
# The functor: Hom( __, Z/<6> ) as covariant functor
Hom_Obj_Z6 := CapFunctor( "Hom(_,ZZ/<6>) functor", Opposite( cat ), cat );
AddObjectFunction( Hom_Obj_Z6,
    function( obj )
    return InternalHomOnObjects( Opposite( obj ), Z6 );
    end );
AddMorphismFunction( Hom_Obj_Z6,
    function( obj1, mor, obj2 )
    return InternalHomOnMorphisms( Opposite( mor ), IdentityMorphism( Z6 ) );
    end );

Tensor_product_with_Z6_in_chains := ExtendFunctorToChainComplexCategoryFunctor( Tensor_product_with_Z6 );
Hom_Obj_Z6_from_cochains_to_cochains := ExtendFunctorToCochainComplexCategoryFunctor( Hom_Obj_Z6 );
Hom_Obj_Z6_from_chains_to_cochains := 
    PreCompose( ChainCategoryToCochainCategoryOfOppositeCategory( cat ), Hom_Obj_Z6_from_cochains_to_cochains );

Z4 := AsLeftPresentation( HomalgMatrix( "[ [ 4 ] ]", 1, 1, ZZ ) );

C_Z4 := StalkChainComplex( Z4, 0 );

proj_res_of_Z4 := ProjectiveResolution( C_Z4 );

tenor_Z6_applied_on_proj_res_of_Z4 := ApplyFunctor( Tensor_product_with_Z6_in_chains, proj_res_of_Z4 );
hom_applied_on_proj_res_of_Z4 := ApplyFunctor( Hom_Obj_Z6_from_chains_to_cochains, proj_res_of_Z4 );

# Now in theory, we have the following facts
# Tor_0( Z/<m>, Z/<n> ) = Z/<m> tensor Z/<n> = Z/<gcd(m,n)> = Hom( Z/<m>, Z/<n> )  = Ext_0( Z/<m>, Z/<n> ) 
# Tor_1( Z/<m>, Z/<n> ) = Z/<gcd(m,n)> = Ext_1( Z/<m>, Z/<n> )

Tor_0 := HomologyAt( tenor_Z6_applied_on_proj_res_of_Z4, 0 );
Display( Tor_0 );
# [ [   2 ],
#   [  -6 ] ]
# 
# An object in Category of left presentations of Z

#                      [  2 ]            [ 2 ]
# I.e., Tor_0 = Coker( [ -6 ] ) = Coker( [ 0 ] ) = Z/<2>

Tor_1 := HomologyAt( tenor_Z6_applied_on_proj_res_of_Z4, 1 );
Display( Tor_1 );
# [ [  -2 ] ]
# 
# An object in Category of left presentations of Z

ext_0 := CohomologyAt( hom_applied_on_proj_res_of_Z4, 0 );;
Display( ext_0 );
# [ [  -2 ] ]
# 
# An object in Category of left presentations of Z

ext_1 := CohomologyAt( hom_applied_on_proj_res_of_Z4, 1 );;
# [ [   2 ],
#   [  -6 ] ]
# 
# An object in Category of left presentations of Z

quit;

A := FreeLeftPresentation( 1, ZZ );
id_A := IdentityMorphism( A );
phi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 10*id_A ], 1 );
psi := ChainMorphism( [ 6*id_A ], 1, [ 4*id_A ], 2, [ 5*id_A ], 1 );

phi_ := AsMorphismInHomotopyCategory( phi );
psi_ := AsMorphismInHomotopyCategory( psi );


