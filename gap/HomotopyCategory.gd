##########################################################
# ModelCategories                    Kamal Saleh
#
# Gap packages                       siegen, 2017
#
##########################################################

####################
#
# Categories
#
####################

DeclareCategory( "IsHomotopyCapCategoryCell", IsCapCategoryCell );

DeclareCategory( "IsHomotopyCapCategoryObject", IsHomotopyCapCategoryCell and IsCapCategoryObject );

DeclareCategory( "IsHomotopyCapCategoryMorphism", IsHomotopyCapCategoryCell and IsCapCategoryMorphism );


####################
#
# Attributes
#
####################

DeclareAttribute( "HomotopyCategory", IsCapCategory and IsModelCategory );

DeclareAttribute( "UnderlyingReplacement", IsHomotopyCapCategoryCell );

DeclareAttribute( "UnderlyingObject", IsHomotopyCapCategoryObject );

DeclareAttribute( "UnderlyingMorphism", IsHomotopyCapCategoryMorphism );

DeclareAttribute( "AsObjectInHomotopyCategory", IsCapCategoryObject );

DeclareAttribute( "AsMorphismInHomotopyCategory", IsCapCategoryMorphism );

