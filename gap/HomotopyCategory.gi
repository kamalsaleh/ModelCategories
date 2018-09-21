##########################################################
# HomotopyCategories                    Kamal Saleh
#
# Gap packages                       siegen, 2017
#
##########################################################

DeclareRepresentation( "IsHomotopyCapCategoryObjectRep",
                        IsComponentObjectRep and IsAttributeStoringRep,
                        [ ] );

DeclareRepresentation( "IsHomotopyCapCategoryMorphismRep",
                        IsComponentObjectRep and IsAttributeStoringRep,
                        [ ] );

BindGlobal( "FamilyOfHomotopyCapCategoryObjects",
             NewFamily( "model categories objects" ) );

BindGlobal( "FamilyOfHomotopyCapCategoryMorphisms",
             NewFamily( "model categories morphisms" ) );

BindGlobal( "TheTypeOfHomotopyCapCategoryObject",
             NewType( FamilyOfHomotopyCapCategoryObjects,
                      IsHomotopyCapCategoryObject and IsHomotopyCapCategoryObjectRep ) );

BindGlobal( "TheTypeOfHomotopyCapCategoryMorphism",
             NewType( FamilyOfHomotopyCapCategoryMorphisms,
                      IsHomotopyCapCategoryMorphism and IsHomotopyCapCategoryMorphismRep ) );

###
InstallMethod( HomotopyCategory,
               [ IsCapCategory and IsModelCategory ],
    function( cat )
    local homotopy_category, to_be_finalized;

    homotopy_category := CreateCapCategory( Concatenation( "Homotopy category of ", Big_to_Small( Name( cat ) ) ) );

    SetUnderlyingModelCategory( homotopy_category, cat );

    INSTALL_METHODS_FOR_HOMOTOPY_CATEGORIES( homotopy_category );

    to_be_finalized := ValueOption( "FinalizeCategory" );

    if to_be_finalized = true then

       Finalize( homotopy_category );

    fi;

    return homotopy_category;

end );

##
InstallMethod( AsObjectInHomotopyCategory,
               [ IsCapCategoryObject ],
    function( obj )
    local A;

    A := rec( );

    ObjectifyWithAttributes( A, TheTypeOfHomotopyCapCategoryObject,
                             UnderlyingObj, obj );

    AddObject( HomotopyCategory( CapCategory( obj ) ), A );

    return A;

end );

##
InstallMethod( AsMorphismInHomotopyCategory,
               [ IsCapCategoryMorphism ],
    function( morphism )
    local phi;

    phi := rec( );

    ObjectifyWithAttributes( phi, TheTypeOfHomotopyCapCategoryMorphism,
                             UnderlyingMor, morphism,
                             Source, AsObjectInHomotopyCategory( Source( morphism ) ),
                             Range, AsObjectInHomotopyCategory( Range( morphism ) )  );

    AddMorphism( HomotopyCategory( CapCategory( morphism ) ), phi );

    return phi;

end );

##
InstallMethod( AsMorphismInHomotopyCategoryByReplacement,
               [ IsCapCategoryObject, IsCapCategoryMorphism, IsCapCategoryObject ],
    function( M, morphism, N )
    local phi;

    if not IsEqualForObjects( Source( morphism ), FibrantModel( CofibrantModel( M ) ) ) or
        not IsEqualForObjects( Range( morphism ), FibrantModel( CofibrantModel( N ) ) ) then
            Error( "Input is not compatible" );
    fi;

    phi := rec( );

    ObjectifyWithAttributes( phi, TheTypeOfHomotopyCapCategoryMorphism,
                             UnderlyingReplacement, morphism,
                             Source, AsObjectInHomotopyCategory( M ),
                             Range, AsObjectInHomotopyCategory( N )  );

    AddMorphism( HomotopyCategory( CapCategory( morphism ) ), phi );

    return phi;

end );

##
InstallMethod( UnderlyingReplacement,
               [ IsHomotopyCapCategoryCell and IsCapCategoryObject ],
    function( obj )

    return FibrantModel( CofibrantModel( UnderlyingObj( obj ) ) );

end );

##
InstallMethod( UnderlyingReplacement,
               [ IsHomotopyCapCategoryCell and IsCapCategoryMorphism ],
    function( morphism )

    return MorphismBetweenFibrantModels( MorphismBetweenCofibrantModels( UnderlyingMor( morphism ) ) );

end );

InstallGlobalFunction( INSTALL_METHODS_FOR_HOMOTOPY_CATEGORIES,
    function( homotopy_category )
    local is_equal_for_morphisms, cat;

    SetIsAdditiveCategory( homotopy_category, true );
    cat := UnderlyingModelCategory( homotopy_category );

    if CanCompute( cat, "AreLeftHomotopic" ) then
       is_equal_for_morphisms :=
            function( morphism1, morphism2 )
                return AreLeftHomotopic( morphism1, morphism2 );
            end;
    elif CanCompute( cat, "AreRightHomotopic" ) then
       is_equal_for_morphisms :=
            function( morphism1, morphism2 )
                return AreRightHomotopic( morphism1, morphism2 );
            end;
    else

        Error( "We can not decide equality between two morphisms" );

    fi;

    AddIsWellDefinedForObjects( homotopy_category,
        function( obj )
        return IsWellDefined( UnderlyingObj( obj ) );
    end );

    AddIsWellDefinedForMorphisms( homotopy_category,
        function( morphism )
        if HasUnderlyingMor( morphism ) then
            return IsWellDefined( UnderlyingMor( morphism ) );
        else
            return IsWellDefined( UnderlyingReplacement( morphism ) ) and
                    IsEqualForObjects( UnderlyingReplacement( Source( morphism ) ), Source( UnderlyingReplacement( morphism ) ) ) and
                    IsEqualForObjects( UnderlyingReplacement( Range( morphism ) ), Range( UnderlyingReplacement( morphism ) ) );
        fi;
    end );

    # IsEqualForObjects
    AddIsEqualForObjects( homotopy_category,
        function( obj1, obj2 )
            return IsEqualForObjects( UnderlyingObj( obj1 ), UnderlyingObj( obj2 ) );
        end );
    # IsEqualForMorphisms
    AddIsEqualForMorphisms( homotopy_category,
        function( morphism1, morphism2 )
            if HasUnderlyingMor( morphism1 ) and HasUnderlyingMor( morphism2 ) then
                return is_equal_for_morphisms( UnderlyingMor( morphism1 ), UnderlyingMor( morphism2 ) );
            else
                return is_equal_for_morphisms( UnderlyingReplacement( morphism1 ), UnderlyingReplacement( morphism2 ) );
            fi;
        end );

    AddIsCongruentForMorphisms( homotopy_category, IsEqualForMorphisms );

    # Methods on morphisms
    AddPreCompose( homotopy_category,
        function( morphism1, morphism2 )
        local morphism;

        # if HasUnderlyingMor( morphism1 ) and HasUnderlyingMor( morphism2 ) then
        #     morphism := PreCompose( UnderlyingMor( morphism1 ), UnderlyingMor( morphism2 ) );
        #     AddToToDoList( ToDoListEntry( [ [ morphism1, "UnderlyingReplacement" ], [ morphism2, "UnderlyingReplacement" ]  ],
        #                                 function( )
        #                                 if not HasUnderlyingReplacement( morphism ) then
        #                                     SetUnderlyingReplacement( morphism, PreCompose( UnderlyingReplacement( morphism1 ), UnderlyingReplacement( morphism2 ) ) );
        #                                 fi;
        #                                 end ) );
        #     return AsMorphismInHomotopyCategory( morphism );
        # else
            morphism := PreCompose( UnderlyingReplacement( morphism1 ), UnderlyingReplacement( morphism2 ) );
            return AsMorphismInHomotopyCategoryByReplacement(
                UnderlyingObj( Source( morphism1 ) ), morphism, UnderlyingObj( Range( morphism2 ) )
            );
        # fi;
    end );


    ## IdentityMorphisms
    AddIdentityMorphism( homotopy_category,

      function( object )

        return AsMorphismInHomotopyCategory( IdentityMorphism( UnderlyingObj( object ) ) );

    end );

    ## Addition for morphisms
    AddAdditionForMorphisms( homotopy_category,

      function( morphism1, morphism2 )
        local sum;

        sum := AdditionForMorphisms( UnderlyingReplacement( morphism1 ),
                                     UnderlyingReplacement( morphism2 ) );

        return AsMorphismInHomotopyCategoryByReplacement(
            UnderlyingObj( Source( morphism1 ) ), sum, UnderlyingObj( Range( morphism1 ) )
            );

    end );

    ## IsZeroForMorphisms
    AddIsZeroForMorphisms( homotopy_category,

        function( morphism )
        local underlying_rep;
        # Here we must take the underlying replacement. In some cases (for example dynkin quivers A_n)
        # The morphism itself is not null-homotopic but its replacement is.
        # To create example take any exact complex and find if its zero or not.
	underlying_rep := UnderlyingReplacement( morphism );
        if HasIsZero( underlying_rep ) and IsZero( underlying_rep ) then
           return true;
        else
           return is_equal_for_morphisms( underlying_rep, ZeroMorphism( Source( underlying_rep ), Range( underlying_rep ) ) );
        fi;

    end );

    ## IsZeroForObjects
    AddIsZeroForObjects( homotopy_category,

    function( obj )
    local underlying_obj;

       underlying_obj := UnderlyingObj( obj );

       if HasIsZero( underlying_obj ) and IsZero( underlying_obj ) then

          return true;

       else

          return IsZero( IdentityMorphism( obj ) );

       fi;

    end );

    ## Additive inverse for morphisms
    AddAdditiveInverseForMorphisms( homotopy_category,

      function( morphism )
        local new_mor;

        new_mor := AdditiveInverseForMorphisms( UnderlyingReplacement( morphism ) );

        return AsMorphismInHomotopyCategoryByReplacement(
            UnderlyingObj( Source( morphism ) ), new_mor, UnderlyingObj( Range( morphism ) )
             );
    end );

    ## Zero morphism
    AddZeroMorphism( homotopy_category,

      function( source, range )
        local zero_mor;

        zero_mor := ZeroMorphism( UnderlyingObj( source ), UnderlyingObj( range ) );

        return AsMorphismInHomotopyCategory( zero_mor );

    end );

    ## isomorphism
    AddIsIsomorphism( homotopy_category,
        function( mor )
        if HasUnderlyingMor( mor ) then
            return IsWeakEquivalence( UnderlyingMor( mor ) );
        else

            return IsWeakEquivalence( UnderlyingReplacement( mor ) );
        fi;
        end );

    ## Inverse
     AddInverse( homotopy_category,
         function( mor )
         local f, A, B, q, p, C, r, s, sr;

         f := UnderlyingReplacement( mor );

         A := Source( f );

         B := Range( f );

         q := FactorThroughAcyclicCofibration( f )[ 1 ];

         p := FactorThroughAcyclicCofibration( f )[ 2 ];

         C := Range( q );

         Assert( 5, IsWeakEquivalence( p ) );

         # Axiom
         SetIsWeakEquivalence( p, true );

         r := Lifting( q, UniversalMorphismIntoTerminalObject( A ), IdentityMorphism( A ), UniversalMorphismIntoTerminalObject( C ) );

         s := Lifting( UniversalMorphismFromInitialObject( B ), p, UniversalMorphismFromInitialObject( C ), IdentityMorphism( B ) );

         # this is wrong, the output here is not in the correct category
         # corrected, but there is maybe a better way ..
         return AsMorphismInHomotopyCategoryByReplacement( UnderlyingObj( Range( mor ) ), PreCompose( s, r ), UnderlyingObj( Source( mor ) ) );

         end );

    if CanCompute( cat, "HomotopyMorphisms" ) then
        AddInverse( homotopy_category,
        function( phi )
        local rep_phi, p, H, i, lower_bound, upper_bound, morphisms, rep_inverse;
        rep_phi := UnderlyingReplacement( phi );
        p := NaturalProjectionFromMappingCone( rep_phi );
        if not IsNullHomotopic( p ) then
            Error( "A morphism which should be null homotopic is not null homotopic" );
        fi;
        H := HomotopyMorphisms( p );
        i := NaturalInjectionInMappingCone( rep_phi );
        lower_bound := ActiveLowerBound( Range( rep_phi ) );
        upper_bound := ActiveUpperBound( Range( rep_phi ) );
        morphisms := MapLazy( IntegersList, j -> PreCompose( i[j], H[j] ), 1 );
        rep_inverse := ChainMorphism( Range( rep_phi ), Source( rep_phi ), morphisms );
        return AsMorphismInHomotopyCategoryByReplacement( UnderlyingObj( Range( phi ) ), rep_inverse, UnderlyingObj( Source( phi ) ) );
        end, 100 );
    fi;

    ## Zero object
    AddZeroObject( homotopy_category,

        function( )
        local zero_obj;

        zero_obj := ZeroObject( UnderlyingModelCategory( homotopy_category ) );

        return AsObjectInHomotopyCategory( zero_obj );

    end );

    ##

    ## direct sum
    AddDirectSum( homotopy_category,

      function( obj_list )
        local underlying_list, underlying_sum;

        underlying_list := List( obj_list, UnderlyingObj );

        underlying_sum := CallFuncList( DirectSum, underlying_list );

        return AsObjectInHomotopyCategory( underlying_sum );

    end );

    AddInjectionOfCofactorOfDirectSum( homotopy_category,
        function( L, n )
        local underlying_list, i;

        underlying_list := List( L, i-> UnderlyingObj( i ) );

        i := InjectionOfCofactorOfDirectSum( underlying_list, n );

        return AsMorphismInHomotopyCategory( i );

    end );

    AddProjectionInFactorOfDirectSum( homotopy_category,
        function( L, n )
        local underlying_list, i;

        underlying_list := List( L, i-> UnderlyingObj( i ) );

        i := ProjectionInFactorOfDirectSum( underlying_list, n );

        return AsMorphismInHomotopyCategory( i );

    end );

    AddDirectSumFunctorialWithGivenDirectSums( homotopy_category,
        function( source, L, range )
        local maps, morphism, morphism1, morphism2, sources, ranges;

        maps := List( L, i-> UnderlyingReplacement( i ) );

        morphism := DirectSumFunctorial( maps );

        # now the source of morphism is the direct sum of replacements of sources in L and 
        # the same holds for the range.
        # so we need to somehow to find isomorphism from the replacement of direct sum to the direct sum of replacements...

        sources := List( L, Source );
        morphism1 := MorphismBetweenDirectSums( [ 
            List( [ 1 .. Length( sources ) ], i -> UnderlyingReplacement( ProjectionInFactorOfDirectSum( sources, i ) ) )
        ] );

        ranges := List( L, Range );
        morphism2 := MorphismBetweenDirectSums( 
            List( [ 1 .. Length( ranges ) ],  i-> [ UnderlyingReplacement( InjectionOfCofactorOfDirectSum( ranges, i ) ) ] )
          );

        morphism := PreCompose( [ morphism1, morphism, morphism2 ] );
        return AsMorphismInHomotopyCategoryByReplacement( UnderlyingObj( source ), morphism, UnderlyingObj( range ) );
    end );

    AddUniversalMorphismIntoDirectSum( homotopy_category,
        function( objects_list, morphisms_list  )
        local underlying_list, morphism;

        underlying_list := List( morphisms_list, i -> UnderlyingMor( i ) );

        morphism := UniversalMorphismIntoDirectSum( underlying_list );

        return AsMorphismInHomotopyCategory( morphism );

        end );

    AddUniversalMorphismFromDirectSum( homotopy_category,
        function( objects_list, morphisms_list )
        local underlying_list, morphism;

        underlying_list := List( morphisms_list, i -> UnderlyingMor( i ) );

        morphism := UniversalMorphismFromDirectSum( underlying_list );

        return AsMorphismInHomotopyCategory( morphism );

        end );

end );

##
InstallMethod( Display,
    [ IsHomotopyCapCategoryMorphism ],
    function( phi )
    Print( "A morphism in ", Name( CapCategory( phi ) ), " given by the underlying " );
    if HasUnderlyingMor( phi ) then
        Print( TextAttr.4, TextAttr.underscore, "morphism", TextAttr.reset, ":\n" );
        Display( UnderlyingMor( phi ) );
    else
        Print( TextAttr.4, TextAttr.underscore, "replacement", TextAttr.reset, ":\n" );
        Display( UnderlyingReplacement( phi ) );
    fi;
end );

##
InstallMethod( Display,
    [ IsHomotopyCapCategoryObject ],
    function( obj )
    Print( "An object in ", Name( CapCategory( obj ) ), " given by the underlying " );
        Print( TextAttr.4, TextAttr.underscore, "object", TextAttr.reset, ":\n" );
        Display( UnderlyingObj( obj ) );
end );
