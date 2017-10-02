##########################################################
# ModelCategories                    Kamal Saleh
#
# Gap packages                       siegen, April 2017
#
##########################################################

InstallValue( CAP_INTERNAL_MODEL_CATEGORIES_BASIC_OPERATIONS, rec( ) );

InstallValue( MODEL_CATEGORIES_METHOD_NAME_RECORD, rec(

## Basic Operations for Model Categories
  
  ProjectiveLift := rec( 
  installation_name := "ProjectiveLift",
  filter_list := [ "morphism", "morphism" ],
  cache_name := "ProjectiveLift",
  return_type := [ "morphism" ] ),

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
  return_type := "bool" ),

  IsCofibrant := rec(
  installation_name := "IsCofibrant",
  filter_list := [ "object" ],
  cache_name := "IsCofibrant",
  return_type := "bool" ),

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
  return_type := [ "morphism", "morphism" ] ),

  FactorThroughAcyclicCofibration := rec(
  installation_name := "FactorThroughAcyclicCofibration",
  filter_list := [ "morphism" ],
  cache_name := "FactorThroughAcyclicCofibration",
  return_type := [ "morphism", "morphism" ] ),
  
  FibrantModel := rec(
  installation_name := "FibrantModel",
  filter_list := [ "object" ],
  cache_name := "FibrantModel",
  return_type := [ "object" ] ),
  
  AcyclicCofibrationIntoFibrantModel := rec(
  installation_name := "AcyclicCofibrationIntoFibrantModel",
  filter_list := [ "object" ],
  cache_name := "AcyclicCofibrationIntoFibrantModel",
  return_type := [ "morphism" ] ),
  
  
  CofibrantModel := rec(
  installation_name := "CofibrantModel",
  filter_list := [ "object" ],
  cache_name := "CofibrantModel",
  return_type := [ "object" ] ),
  
  AcyclicFibrationFromCofibrantModel := rec(
  installation_name := "AcyclicFibrationFromCofibrantModel",
  filter_list := [ "object" ],
  cache_name := "AcyclicFibrationFromCofibrantModel",
  return_type := [ "morphism" ] ),
  
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
