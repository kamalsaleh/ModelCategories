##########################################################
# ModelCategories                    Kamal Saleh
#
# Gap packages                       siegen, April 2017
#
##########################################################

InstallValue( CAP_INTERNAL_MODEL_CATEGORIES_BASIC_OPERATIONS, rec( ) );

InstallValue( MODEL_CATEGORIES_METHOD_NAME_RECORD, rec(

## Basic Operations for Model Categories

  IsWeakEquivalence := rec(
  installation_name := "IsWeakEquivalence",
  filter_list := [ "morphism" ],
  cache_name := "IsWeakEquivalence",
  return_type := "bool" ),

  IsFibration := rec(
  installation_name := "IsFibration",
  filter_list := [ "morphism" ],
  cache_name := "IsFibration",
  return_type := "bool" ),

  IsAcyclicFibration := rec(
  installation_name := "IsAcyclicFibration",
  filter_list := [ "morphism" ],
  cache_name := "IsAcyclicFibration",
  return_type := "bool" ),

  IsCofibration := rec(
  installation_name := "IsCofibration",
  filter_list := [ "morphism" ],
  cache_name := "IsCofibration",
  return_type := "bool" ),

  IsAcyclicCofibration := rec(
  installation_name := "IsAcyclicCofibration",
  filter_list := [ "morphism" ],
  cache_name := "IsAcyclicCofibration",
  return_type := "bool" ),

  IsFibrant := rec(
  installation_name := "IsFibrant",
  filter_list := [ "object" ],
  cache_name := "IsFibrant",
  return_type := "bool",
  post_function := function( obj, is_fibrant )
    if is_fibrant <> fail then 
        if is_fibrant = true then 
            SetIsFibration( UniversalMorphismIntoTerminalObject( obj ), true );
        fi;
    fi;
    end ),

  IsCofibrant := rec(
  installation_name := "IsCofibrant",
  filter_list := [ "object" ],
  cache_name := "IsCofibrant",
  return_type := "bool",
  post_function := function( obj, is_cofibrant )
    if is_cofibrant <> fail then 
        if is_cofibrant = true then 
            SetIsCofibration( UniversalMorphismFromInitialObject( obj ), true );
        fi;
    fi;
    end ),

  IsFibrantAndCofibrant := rec(
  installation_name := "IsFibrantAndCofibrant",
  filter_list := [ "object" ],
  cache_name := "IsFibrantAndCofibrant",
  return_type := "bool" ),

  Lifting := rec(
  installation_name := "Lifting",
  filter_list := [ "morphism", "morphism", "morphism", "morphism" ],
  cache_name := "Lifting",
  return_type := "morphism" ),

  FactorThroughAcyclicFibration := rec(
  installation_name := "FactorThroughAcyclicFibration",
  filter_list := [ "morphism" ],
  cache_name := "FactorThroughAcyclicFibration",
  return_type := [ "morphism", "morphism" ],
  post_function :=  function( mor, return_value )
                    SetIsCofibration( return_value[ 1 ], true );
                    SetIsAcyclicFibration( return_value[ 2 ], true );
                    end ),

  FactorThroughAcyclicCofibration := rec(
  installation_name := "FactorThroughAcyclicCofibration",
  filter_list := [ "morphism" ],
  cache_name := "FactorThroughAcyclicCofibration",
  return_type := [ "morphism", "morphism" ],
  post_function :=  function( mor, return_value )
                    SetIsAcyclicCofibration( return_value[ 1 ], true );
                    SetIsFibration( return_value[ 2 ], true );
                    end ),
  
  FibrantModel := rec(
  installation_name := "FibrantModel",
  filter_list := [ "object" ],
  cache_name := "FibrantModel",
  return_type := [ "object" ] ),
  
  AcyclicCofibrationIntoFibrantModel := rec(
  installation_name := "AcyclicCofibrationIntoFibrantModel",
  filter_list := [ "object" ],
  cache_name := "AcyclicCofibrationIntoFibrantModel",
  return_type := [ "morphism" ],
  post_function := function( obj, return_value )
                   SetIsAcyclicCofibration( return_value, true );
                   end ),
  
  
  CofibrantModel := rec(
  installation_name := "CofibrantModel",
  filter_list := [ "object" ],
  cache_name := "CofibrantModel",
  return_type := [ "object" ] ),
  
  AcyclicFibrationFromCofibrantModel := rec(
  installation_name := "AcyclicFibrationFromCofibrantModel",
  filter_list := [ "object" ],
  cache_name := "AcyclicFibrationFromCofibrantModel",
  return_type := [ "morphism" ],
  post_function := function( obj, return_value )
                   SetIsAcyclicFibration( return_value, true );
                   end ),
  
    MorphismBetweenCofibrantModels := rec( 
    installation_name := "MorphismBetweenCofibrantModels",
    filter_list := [ "morphism" ],
    cache_name := "MorphismBetweenCofibrantModels",
    return_type := [ "morphism" ],
    post_function :=  function( mor, return_value )
                    SetIsCofibrant( Source( return_value ), true );
                    
                    SetIsCofibrant( Range( return_value ), true );
                    
                    AddToToDoList( 
                        ToDoListEntry( [ [ mor, "IsWeakEquivalence" ] ], 
                            function( )
                            SetIsWeakEquivalence( return_value, IsWeakEquivalence( mor )  );
                            end ) );
                    AddToToDoList( 
                        ToDoListEntry( [ [ return_value, "IsWeakEquivalence" ] ], 
                            function( )
                            SetIsWeakEquivalence( mor, IsWeakEquivalence( mor )  );
                            end ) );
                    end ),
    
    MorphismBetweenFibrantModels := rec( 
    installation_name := "MorphismBetweenFibrantModels",
    filter_list := [ "morphism" ],
    cache_name := "MorphismBetweenFibrantModels",
    return_type := [ "morphism" ],
    post_function :=  function( mor, return_value )

                    SetIsFibrant( Source( return_value ), true );
                    
                    SetIsFibrant( Range( return_value ), true );
                    
                    AddToToDoList( 
                        ToDoListEntry( [ [ mor, "IsWeakEquivalence" ] ], 
                            function( )
                            SetIsWeakEquivalence( return_value, IsWeakEquivalence( mor )  );
                            end ) );
                    AddToToDoList( 
                        ToDoListEntry( [ [ return_value, "IsWeakEquivalence" ] ], 
                            function( )
                            SetIsWeakEquivalence( mor, IsWeakEquivalence( mor )  );
                            end ) );
                    end ),
  
  AreLeftHomotopic := rec(
  installation_name := "AreLeftHomotopic",
  filter_list := [ "morphism", "morphism" ],
  cache_name := "AreLeftHomotopic",
  return_type := "bool" ),
  
  LeftHomotopy := rec(
  installation_name := "LeftHomotopy",
  filter_list := [ "morphism", "morphism" ],
  cache_name := "LeftHomotopy",
  return_type := "morphism" ),

  AreRightHomotopic := rec(
  installation_name := "AreRightHomotopic",
  filter_list := [ "morphism", "morphism" ],
  cache_name := "AreRightHomotopic",
  return_type := "bool" ),
  
  RightHomotopy := rec(
  installation_name := "RightHomotopy",
  filter_list := [ "morphism", "morphism" ],
  cache_name := "RightHomotopy",
  return_type := "morphism" ),
  
  ) );

CAP_INTERNAL_ENHANCE_NAME_RECORD( MODEL_CATEGORIES_METHOD_NAME_RECORD );

CAP_INTERNAL_INSTALL_ADDS_FROM_RECORD( MODEL_CATEGORIES_METHOD_NAME_RECORD );

#####################################
##
## Immediate Methods and Attributes 
##
#####################################

InstallImmediateMethod( INSTALL_LOGICAL_IMPLICATIONS_AND_THEOREMS_FOR_MODEL_CATEGORY,
            IsCapCategory and IsModelCategory, 
            0,
    function( category )
   
    AddPredicateImplicationFileToCategory( category,
        Filename(
            DirectoriesPackageLibrary( "ModelCategories", "LogicForModelCategories" ),
            "PredicateImplicationsForModelCategories.tex" ) );
   
    AddTheoremFileToCategory( category,
        Filename(
            DirectoriesPackageLibrary( "ModelCategories", "LogicForModelCategories" ),
        "PropositionsForModelCategories.tex" ) );
     
    TryNextMethod( );
     
end );
