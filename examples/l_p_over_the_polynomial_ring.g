
Read( "left_homotopy_in_complexes_of_l_p_over_comm_homalg_ring.g" );

LoadPackage( "ModulePresentations" );
LoadPackage( "ModelCategories" );
LoadPackage( "TriangulatedCategoriesForCAP" );

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

twist_functor := ShiftFunctor( chains, -1 );
reverse_twist_functor := ShiftFunctor( chains, 1 );

homotopy_chains := HomotopyCategory( chains );
SetIsTriangulatedCategory( homotopy_chains, true );
SetIsTriangulatedCategoryWithShiftAutomorphism( homotopy_chains, true );

## Adding the shift and reverse shift functors
AddShiftOfObject( homotopy_chains, 
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsObjectInHomotopyCategory( ApplyFunctor( twist_functor, replacement )  );
end );

##
AddShiftOfMorphism( homotopy_chains, 
    function( phi )
    local replacement;
    replacement := UnderlyingReplacement( phi );
    return AsMorphismInHomotopyCategory( ApplyFunctor( twist_functor, replacement ) );
end );

##
AddReverseShiftOfObject( homotopy_chains, 
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsObjectInHomotopyCategory( ApplyFunctor( reverse_twist_functor, replacement )  );
end );

##
AddReverseShiftOfMorphism( homotopy_chains, 
    function( phi )
    local replacement;
    replacement := UnderlyingReplacement( phi );
    return AsMorphismInHomotopyCategory( ApplyFunctor( reverse_twist_functor, replacement ) );
end );

##
AddIsomorphismIntoShiftOfReverseShift( homotopy_chains,
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsMorphismInHomotopyCategoryByReplacement( 
        UnderlyingObject( C ),
        IdentityMorphism( replacement ),
        UnderlyingReplacement( C )
    );
end );

AddIsomorphismFromShiftOfReverseShift( homotopy_chains,
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsMorphismInHomotopyCategoryByReplacement( 
        UnderlyingReplacement( C ),
        IdentityMorphism( replacement ),
        UnderlyingObject( C )
    );
end );

AddIsomorphismIntoReverseShiftOfShift( homotopy_chains,
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsMorphismInHomotopyCategoryByReplacement( 
        UnderlyingObject( C ),
        IdentityMorphism( replacement ),
        UnderlyingReplacement( C )
    );
end );

AddIsomorphismFromReverseShiftOfShift( homotopy_chains,
    function( C )
    local replacement;
    replacement := UnderlyingReplacement( C );
    return AsMorphismInHomotopyCategoryByReplacement( 
        UnderlyingReplacement( C ),
        IdentityMorphism( replacement ),
        UnderlyingObject( C )
    );
end );

AddConeObject( homotopy_chains,
    function( phi )
    return AsObjectInHomotopyCategory( MappingCone( UnderlyingReplacement( phi ) ) );
end );

##
AddCompleteMorphismToStandardExactTriangle( homotopy_chains,
    function( phi )
    local replacement, i, p;
    replacement := UnderlyingReplacement( phi );
    i := NaturalInjectionInMappingCone( replacement );
    p := NaturalProjectionFromMappingCone( replacement );

    i := AsMorphismInHomotopyCategoryByReplacement(
            UnderlyingObject( Range( phi ) ),
            i,
            MappingCone( replacement )
    );

    p := AsMorphismInHomotopyCategoryByReplacement(
            MappingCone( replacement ),
            p,
            UnderlyingObject( ShiftOfObject( Source( phi ) ) )
    );

    return CreateStandardExactTriangle( phi, i, p );

end );

##
AddCompleteToMorphismOfStandardExactTriangles( homotopy_chains,
    function( tr1, tr2, phi_, psi_ )
    local phi, psi, maps, s, f, g;
    f := UnderlyingReplacement( tr1^0 );
    g := UnderlyingReplacement( tr2^0 ); 
    phi := UnderlyingReplacement( phi_ );
    psi := UnderlyingReplacement( psi_ );

    s := HomotopyMorphisms( UnderlyingReplacement( PreCompose( tr1^0, psi_ ) - PreCompose( phi_, tr2^0 ) ) );
    
    maps := MapLazy( IntegersList,  
            function( i )
            return MorphismBetweenDirectSums( [
                [ phi[ i - 1 ], s[ i - 1 ] ],
                [ ZeroMorphism( Source( psi )[ i ], Range( phi )[ i - 1 ] ), psi[ i ] ]
            ] );
            end, 1 );

    maps := AsMorphismInHomotopyCategory( ChainMorphism( 
        UnderlyingReplacement( tr1[2] ), 
        UnderlyingReplacement( tr2[2] ),
        maps ) );

    return CreateTrianglesMorphism( tr1, tr2, phi_, psi_, maps );
end );

##
AddRotationOfStandardExactTriangle( homotopy_chains,
    function( tr )
    local rot, standard_rot, X, Y, maps, map, f;

    rot := CreateExactTriangle( tr^1, tr^2, AdditiveInverse( ShiftOfMorphism( tr^0 ) ) );
    standard_rot := CompleteMorphismToStandardExactTriangle( tr^1 );
    f := UnderlyingReplacement( tr^0 );
    X := UnderlyingReplacement( tr[0] );
    Y := UnderlyingReplacement( tr[1] );
    maps := MapLazy( IntegersList,  
            function( i )
            return MorphismBetweenDirectSums(
                [ 
                    [ AdditiveInverse( f[ i - 1 ] ), IdentityMorphism( X[ i - 1 ] ), ZeroMorphism( X[ i - 1 ], Y[ i ] ) ]
                ]
            );
            end, 1 );
    map := ChainMorphism( UnderlyingReplacement( rot[ 2 ] ), UnderlyingReplacement( standard_rot[ 2 ] ), maps );
    map := AsMorphismInHomotopyCategory( map );
    map := CreateTrianglesMorphism( 
                rot, standard_rot, IdentityMorphism( tr[ 1 ] ), IdentityMorphism( tr[ 2 ] ), map 
                );
    SetIsomorphismIntoStandardExactTriangle( rot, map );

    maps := MapLazy( IntegersList,  
            function( i )
            return MorphismBetweenDirectSums(
                [ 
                    [ ZeroMorphism( Y[ i - 1 ], X[ i - 1 ] ) ],
                    [ IdentityMorphism( X[ i - 1 ] )         ], 
                    [ ZeroMorphism( Y[ i ], X[ i - 1 ] )     ]
                ]
            );
            end, 1 );
    map := ChainMorphism( UnderlyingReplacement( standard_rot[ 2 ] ), UnderlyingReplacement( rot[ 2 ] ), maps );
    map := AsMorphismInHomotopyCategory( map );
    map := CreateTrianglesMorphism( 
                standard_rot, rot, IdentityMorphism( tr[ 1 ] ), IdentityMorphism( tr[ 2 ] ), map 
                );
    SetIsomorphismFromStandardExactTriangle( rot, map );

    return rot;
end );



m := HomalgMatrix( "[ x,y,0,z,-x,y ]", 2, 3, R );
# <A 2 x 3 matrix over an external ring>
n := HomalgMatrix( "[ x+y,x-y,z,y,0,-x,0,z ]", 4, 2, R );
# <A 4 x 2 matrix over an external ring>
a := HomalgMatrix( "[ x+y,0,x+y,-x,-x-y-z,2x ]", 3, 2, R );
# <A 3 x 2 matrix over an external ring>
M := AsLeftPresentation( m );
# <An object in Category of left presentations of Q[x,y,z]>
N := AsLeftPresentation( n );
# <An object in Category of left presentations of Q[x,y,z]>
f1 := PresentationMorphism( M, a, N );
# <A morphism in Category of left presentations of Q[x,y,z]>
CM := StalkChainComplex( M, 1 );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
CN := StalkChainComplex( N, 1 );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
phi := ChainMorphism( CM, CN, [ f1 ], 1 );
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>

quit;

IsWellDefined( phi );
# true
CM_cofib := CofibrantModel( CM );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
CN_cofib := CofibrantModel( CN );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 5>
phi_cofib := MorphismBetweenCofibrantModels( phi );
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
IsWellDefined( phi_cofib, 0, 10 );
# true
Display( phi_cofib, 0, 10 );
# In index 0
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 1
# 
# Morphism is
# x+y,   0, 
# x+y,   -x,
# -x-y-z,2*x
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 2
# 
# Morphism is
# -y,z,   x+y-z,-y, 
# -y,-x+z,x+y-z,-x-y
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 3
# 
# Morphism is
# (an empty 0 x 3 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 4
# 
# Morphism is
# (an empty 0 x 1 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 5
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 6
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 7
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 8
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 9
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 10
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
H := InternalHomOnObjects( CM_cofib, CN_cofib );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound -2 and active upper bound 4>
kernel_mor_of_H := CyclesAt( H, 0 );
# <A monomorphism in Category of left presentations of Q[x,y,z]>
kernel_obj_of_H := Source( kernel_mor_of_H );
# <An object in Category of left presentations of Q[x,y,z]>
homology_of_H := HomologyAt( H, 0 );
# <An object in Category of left presentations of Q[x,y,z]>
ker_to_homology := CokernelProjection( KernelLift( H^0, BoundariesAt( H, 0 ) ) );
# <An epimorphism in Category of left presentations of Q[x,y,z]>
IsEqualForObjects( homology_of_H, Range( ker_to_homology ) );
# true
NrColumns( UnderlyingMatrix( homology_of_H ) );
# 14
morphisms_from_R_to_homology := List( [ 1 .. 14 ], i-> StandardGeneratorMorphism( homology_of_H, i ) );;
List( morphisms_from_R_to_homology, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
morphisms_from_R_to_kernel := List( morphisms_from_R_to_homology, m -> ProjectiveLift( m, ker_to_homology ) );;
List( morphisms_from_R_to_kernel, IsZero );
# [ false, false, false, false, false, false, false, false, false, false, false, false, false, false ]
T := TensorUnit( chains );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound -1 and active upper bound 1>
morphisms_from_T_to_H := List( morphisms_from_R_to_kernel, m -> ChainMorphism( T, H, [ PreCompose( m, kernel_mor_of_H) ], 0 ) );;
List( morphisms_from_T_to_H, IsWellDefined );
# [ true, true, true, true, true, true, true, true, true, true, true, true, true, true ]
morphisms_between_M_cofib_N_cofib := List( morphisms_from_T_to_H, m-> InternalHomToTensorProductAdjunctionMap( CM_cofib, CN_cofib, m ) );;
morphisms_between_M_cofib_N_cofib_homotopy_cat := List( morphisms_between_M_cofib_N_cofib, AsMorphismInHomotopyCategory );;
List( morphisms_between_M_cofib_N_cofib, IsZero );
# [ false, false, false, false, false, false, false, false, false, false, false, false, false, false ]
List( morphisms_between_M_cofib_N_cofib_homotopy_cat, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
List( morphisms_from_R_to_homology, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
Display( morphisms_between_M_cofib_N_cofib[ 10 ], 0, 5 );
# In index 0
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split epimorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 1
# 
# Morphism is
# z,0, 
# z,-z,
# z,0  
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 2
# 
# Morphism is
# 0,-z, z, 0,    
# 0,2*x,-z,-2*y-z
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 3
# 
# Morphism is
# (an empty 0 x 3 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 4
# 
# Morphism is
# (an empty 0 x 1 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 5
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
