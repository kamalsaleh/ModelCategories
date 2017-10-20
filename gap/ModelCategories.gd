##########################################################
# ModelCategories                    Kamal Saleh
#
# Gap packages                       siegen, April 2017
#
##########################################################

DeclareProperty( "IsModelCategory", IsCapCategory );

DeclareGlobalVariable( "CAP_INTERNAL_MODEL_CATEGORIES_BASIC_OPERATIONS" );
DeclareGlobalVariable( "MODEL_CATEGORIES_METHOD_NAME_RECORD" );

DeclareAttribute( "INSTALL_LOGICAL_IMPLICATIONS_AND_THEOREMS_FOR_MODEL_CATEGORY", IsCapCategory );

DeclareFamilyProperty( "IsWeakEquivalence",
                       IsCapCategoryMorphism, "morphism" : reinstall := false );
                       
DeclareOperation( "AddIsWeakEquivalence",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsWeakEquivalence",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsWeakEquivalence",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsWeakEquivalence",
                  [ IsCapCategory, IsList ] );

DeclareFamilyProperty( "IsFibration",
                       IsCapCategoryMorphism, "morphism" : reinstall := false );
                       
DeclareOperation( "AddIsFibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsFibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsFibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsFibration",
                  [ IsCapCategory, IsList ] );

DeclareFamilyProperty( "IsAcyclicFibration",
                       IsCapCategoryMorphism, "morphism" : reinstall := false );
                       
DeclareOperation( "AddIsAcyclicFibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsAcyclicFibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsAcyclicFibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsAcyclicFibration",
                  [ IsCapCategory, IsList ] );

DeclareFamilyProperty( "IsCofibration",
                       IsCapCategoryMorphism, "morphism" : reinstall := false );
                       
DeclareOperation( "AddIsCofibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsCofibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsCofibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsCofibration",
                  [ IsCapCategory, IsList ] );
                
DeclareFamilyProperty( "IsAcyclicCofibration",
                       IsCapCategoryMorphism, "morphism" : reinstall := false );
                       
DeclareOperation( "AddIsAcyclicCofibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsAcyclicCofibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsAcyclicCofibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsAcyclicCofibration",
                  [ IsCapCategory, IsList ] );
                  
DeclareFamilyProperty( "IsFibrant",
                       IsCapCategoryObject, "object" : reinstall := false );
                       
DeclareOperation( "AddIsFibrant",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsFibrant",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsFibrant",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsFibrant",
                  [ IsCapCategory, IsList ] );

DeclareFamilyProperty( "IsCofibrant",
                       IsCapCategoryObject, "object" : reinstall := false );
                       
DeclareOperation( "AddIsCofibrant",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsCofibrant",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsCofibrant",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsCofibrant",
                  [ IsCapCategory, IsList ] );

##
DeclareFamilyProperty( "IsFibrantAndCofibrant",
                       IsCapCategoryObject, "object" : reinstall := false );
                       
DeclareOperation( "AddIsFibrantAndCofibrant",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddIsFibrantAndCofibrant",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddIsFibrantAndCofibrant",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddIsFibrantAndCofibrant",
                  [ IsCapCategory, IsList ] );

##
DeclareOperation( "Lifting", [ IsCapCategoryMorphism, IsCapCategoryMorphism, IsCapCategoryMorphism, IsCapCategoryMorphism ] );

DeclareOperation( "AddLifting",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddLifting",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddLifting",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddLifting",
                  [ IsCapCategory, IsList ] );


##
DeclareOperation( "FactorThroughAcyclicFibration", [ IsCapCategoryMorphism ] );

DeclareOperation( "AddFactorThroughAcyclicFibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddFactorThroughAcyclicFibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddFactorThroughAcyclicFibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddFactorThroughAcyclicFibration",
                  [ IsCapCategory, IsList ] );

##
DeclareOperation( "FactorThroughAcyclicCofibration", [ IsCapCategoryMorphism ] );

DeclareOperation( "AddFactorThroughAcyclicCofibration",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddFactorThroughAcyclicCofibration",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddFactorThroughAcyclicCofibration",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddFactorThroughAcyclicCofibration",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "FibrantModel", IsCapCategoryObject );

DeclareOperation( "AddFibrantModel",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddFibrantModel",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddFibrantModel",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddFibrantModel",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "AcyclicCofibrationIntoFibrantModel", IsCapCategoryObject );

DeclareOperation( "AddAcyclicCofibrationIntoFibrantModel",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddAcyclicCofibrationIntoFibrantModel",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddAcyclicCofibrationIntoFibrantModel",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddAcyclicCofibrationIntoFibrantModel",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "AcyclicFibrationFromCofibrantModel", IsCapCategoryObject );

DeclareOperation( "AddAcyclicFibrationFromCofibrantModel",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddAcyclicFibrationFromCofibrantModel",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddAcyclicFibrationFromCofibrantModel",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddAcyclicFibrationFromCofibrantModel",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "CofibrantModel", IsCapCategoryObject );

DeclareOperation( "AddCofibrantModel",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddCofibrantModel",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddCofibrantModel",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddCofibrantModel",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "MorphismBetweenCofibrantModels", IsCapCategoryMorphism );

DeclareOperation( "AddMorphismBetweenCofibrantModels",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddMorphismBetweenCofibrantModels",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddMorphismBetweenCofibrantModels",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddMorphismBetweenCofibrantModels",
                  [ IsCapCategory, IsList ] );

##
DeclareAttribute( "MorphismBetweenFibrantModels", IsCapCategoryMorphism );

DeclareOperation( "AddMorphismBetweenFibrantModels",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddMorphismBetweenFibrantModels",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddMorphismBetweenFibrantModels",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddMorphismBetweenFibrantModels",
                  [ IsCapCategory, IsList ] );

##
DeclareOperation( "AreLeftHomotopic", [ IsCapCategoryMorphism, IsCapCategoryMorphism ] );

DeclareOperation( "AddAreLeftHomotopic",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddAreLeftHomotopic",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddAreLeftHomotopic",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddAreLeftHomotopic",
                  [ IsCapCategory, IsList ] );
                  
##
DeclareOperation( "AreRightHomotopic", [ IsCapCategoryMorphism, IsCapCategoryMorphism ] );

DeclareOperation( "AddAreRightHomotopic",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddAreRightHomotopic",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddAreRightHomotopic",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddAreRightHomotopic",
                  [ IsCapCategory, IsList ] );
                 
##
DeclareOperation( "LeftHomotopy", [ IsCapCategoryMorphism, IsCapCategoryMorphism ] );

DeclareOperation( "AddLeftHomotopy",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddLeftHomotopy",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddLeftHomotopy",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddLeftHomotopy",
                  [ IsCapCategory, IsList ] );

##
DeclareOperation( "RightHomotopy", [ IsCapCategoryMorphism, IsCapCategoryMorphism ] );

DeclareOperation( "AddRightHomotopy",
                  [ IsCapCategory, IsFunction ] );

DeclareOperation( "AddRightHomotopy",
                  [ IsCapCategory, IsFunction, IsInt ] );

DeclareOperation( "AddRightHomotopy",
                  [ IsCapCategory, IsList, IsInt ] );

DeclareOperation( "AddRightHomotopy",
                  [ IsCapCategory, IsList ] );
                  
##
##
# DeclareOperation( "ProjectiveLift", [ IsCapCategoryMorphism, IsCapCategoryMorphism ] );
# 
# DeclareOperation( "AddProjectiveLift",
#                   [ IsCapCategory, IsFunction ] );
# 
# DeclareOperation( "AddProjectiveLift",
#                   [ IsCapCategory, IsFunction, IsInt ] );
# 
# DeclareOperation( "AddProjectiveLift",
#                   [ IsCapCategory, IsList, IsInt ] );
# 
# DeclareOperation( "AddProjectiveLift",
#                   [ IsCapCategory, IsList ] );

