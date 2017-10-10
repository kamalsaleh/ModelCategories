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
    local homotopy_category, is_equal_for_morphisms;
    
    homotopy_category := CreateCapCategory( Concatenation( "Homotopy category of ", Big_to_Small( Name( cat ) ) ) );
    
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
        
       is_equal_for_morphisms := ReturnTrue;
       
    fi;
    
    # Methods on objects
    
    AddIsEqualForObjects( homotopy_category,
        function( obj1, obj2 )
            return IsEqualForObjects( UnderlyingObject( obj1 ), UnderlyingObject( obj2 ) );
        end );
     
    AddIsEqualForMorphisms( homotopy_category,
        function( morphism1, morphism2 )
        return is_equal_for_morphisms( UnderlyingMorphism( morphism1 ), UnderlyingMorphism( morphism2 ) );
        end );
        
    # Methods on morphisms
    AddPreCompose( homotopy_category, 
        function( morphism1, morphism2 )
        local morphism;
        
        morphism := PreCompose( UnderlyingMorphism( morphism1 ), UnderlyingMorphism( morphism2 ) );
        
        AddToToDoList( ToDoListEntry( [ [ morphism1, "UnderlyingReplacement" ], [ morphism2, "UnderlyingReplacement" ]  ],
                                    function( )

                                    if not HasUnderlyingReplacement( morphism ) then

                                        SetUnderlyingReplacement( morphism, PreCompose( UnderlyingReplacement( morphism1 ), UnderlyingReplacement( morphism2 ) ) );

                                    fi;

                                    end ) );
        return AsMorphismInHomotopyCategory( morphism );
        
        end );
    
    return homotopy_category;
    
end );

##
InstallMethod( AsObjectInHomotopyCategory, 
               [ IsCapCategoryObject ],
    function( obj )
    local A;
    
    A := rec( );
    
    ObjectifyWithAttributes( A, TheTypeOfHomotopyCapCategoryObject,
                             UnderlyingObject, obj );
                             
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
                             UnderlyingMorphism, morphism,
                             Source, AsObjectInHomotopyCategory( Source( morphism ) ),
                             Range, AsObjectInHomotopyCategory( Range( morphism ) )  );
    
    AddMorphism( HomotopyCategory( CapCategory( morphism ) ), phi );
    
    return phi;
    
end );

##
InstallMethod( UnderlyingReplacement,
               [ IsHomotopyCapCategoryCell and IsCapCategoryObject ],
    function( obj )

    return FibrantModel( CofibrantModel( UnderlyingObject( obj ) ) );

end );

##
InstallMethod( UnderlyingReplacement,
               [ IsHomotopyCapCategoryCell and IsCapCategoryMorphism ],
    function( morphism )

    return MorphismBetweenFibrantModels( MorphismBetweenCofibrantModels( UnderlyingMorphism( morphism ) ) );

end );
