DeclareGlobalFunction( "AddTriangulatedStructure" );
InstallGlobalFunction( AddTriangulatedStructure,

function( homotopy_chains )
local twist_functor, reverse_twist_functor, chains;

chains := UnderlyingModelCategory( homotopy_chains );
twist_functor := ShiftFunctor( chains, -1 );
reverse_twist_functor := ShiftFunctor( chains, 1 );

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

AddOctahedralAxiom( homotopy_chains,
    function( f_, g_ )
    local h_, f, g, h, X, Y, Z, t0, t1, t2, t, tf_, th_, tr, i, j, standard_tr;
    h_ := PreCompose( f_, g_ );
    f := UnderlyingReplacement( f_ );
    g := UnderlyingReplacement( g_ );
    h := UnderlyingReplacement( h_ );
    X := Source( f );
    Y := Range( f );
    Z := Range( g );

    tf_ := CompleteMorphismToStandardExactTriangle( f_ );
    th_ := CompleteMorphismToStandardExactTriangle( h_ );

    t := CompleteToMorphismOfStandardExactTriangles( tf_, th_, IdentityMorphism( Source( f_ ) ), g_ );
    t0 := t[ 2 ];

    t1 := MapLazy( IntegersList, 
            function( i ) 
                return MorphismBetweenDirectSums(
                    [
                        [ f[ i - 1 ], ZeroMorphism( X[ i - 1 ], Z[ i ] )],
                        [ ZeroMorphism( Z[ i ], Y[ i - 1 ] ), IdentityMorphism( Z[ i ] ) ]
                    ]
                );
            end, 1 );
    t1 := ChainMorphism( MappingCone( h ), MappingCone( g ), t1 );
    t1 := AsMorphismInHomotopyCategory( t1 );

    t2 := MapLazy( IntegersList, 
            function( i ) 
                return MorphismBetweenDirectSums(
                    [
                        [ ZeroMorphism( Y[ i - 1 ], X[ i - 2 ] ), IdentityMorphism( Y[ i - 1 ] ) ],
                        [ ZeroMorphism( Z[ i ], X[ i - 2 ] ), ZeroMorphism( Z[ i ], Y[ i - 1 ] ) ]
                    ]
                );
            end, 1 );
    t2 := ChainMorphism( MappingCone( g ), ShiftLazy( MappingCone( f ), -1 ), t2 );
    t2 := AsMorphismInHomotopyCategory( t2 );


    tr := CreateExactTriangle( t0, t1, t2 );

    standard_tr := CompleteMorphismToStandardExactTriangle( t0 );

    i := MapLazy( IntegersList, 
            function( i )
            return MorphismBetweenDirectSums( 
                [
                    [ ZeroMorphism( Y[i-1], X[i-2] ), IdentityMorphism( Y[i-1] ), ZeroMorphism( Y[i-1], X[i-1] ), ZeroMorphism( Y[i-1], Z[i] ) ],
                    [ ZeroMorphism( Z[i], X[i-2] ), ZeroMorphism( Z[i], Y[i-1] ), ZeroMorphism( Z[i], X[i-1] ), IdentityMorphism( Z[i] ) ] 
                ]
            );
            end, 1 );
    i := ChainMorphism( MappingCone( g ), MappingCone( UnderlyingMorphism( t0 ) ), i );
    i := AsMorphismInHomotopyCategory( i );
    i := CreateTrianglesMorphism( tr, standard_tr, IdentityMorphism( tr[0] ), IdentityMorphism( tr[1] ), i );

    j := MapLazy( IntegersList, 
            function( i )
            return MorphismBetweenDirectSums( 
                [
                    [  ZeroMorphism( X[i-2], Y[i-1] ), ZeroMorphism(  X[i-2], Z[i] ) ],
                    [  IdentityMorphism( Y[i-1] ),     ZeroMorphism(  Y[i-1], Z[i] ) ],
                    [  f[i-1], ZeroMorphism(  X[i-1], Z[i] ) ],
                    [  ZeroMorphism( Z[i], Y[i-1]   ), IdentityMorphism( Z[i] ) ] 
                ]
            );
            end, 1 );
    
    j := ChainMorphism( MappingCone( UnderlyingMorphism( t0 ) ), MappingCone( g ), j );
    j := AsMorphismInHomotopyCategory( j );
    j := CreateTrianglesMorphism( standard_tr, tr, IdentityMorphism( tr[0] ), IdentityMorphism( tr[1] ), j );

    SetIsomorphismIntoStandardExactTriangle( tr, i );
    SetIsomorphismFromStandardExactTriangle( tr, j );
    
    return tr;

end );

Finalize( homotopy_chains );

end );

