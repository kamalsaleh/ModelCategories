LoadPackage( "GradedModulePresentations" );
LoadPackage( "ModelCategories" );
LoadPackage( "TriangulatedCategoriesForCAP" );

dimension_of_projective_space := InputFromUser( "Over which P^n we are going to work? n := ");

ReadPackage( "BBGG", "examples/glp_over_g_exterior_algebra/stable_cat_of_glp_over_exterior_algebra.g" );
ReadPackage( "ModelCategories", "examples/tools/Triangulated_Structure.g" );
homotopy_chains_graded_lp_cat_sym := HomotopyCategory( chains_graded_lp_cat_sym :FinalizeCategory := false );
AddTriangulatedStructure( homotopy_chains_graded_lp_cat_sym );
Finalize( homotopy_chains_graded_lp_cat_sym );

# Please pull the branch devel2 or mohamed of QPA2 at https://github.com/kamalsaleh/QPA2
ReadPackage( "ModelCategories", "examples/tools/left_homotopy_in_chains_of_rep_over_quiver.g" );
field := Rationals;

# There are still methods in qpa that don't work with homalg fields.

# field := HomalgFieldOfRationals();

# function to create the required data for the Beilinson quiver of D(P^2).

# Beilinson Quiver for P^n, n = 1

#         x10
#  1 ---  x11 ---> 2
#      

P := CotangentBeilinsonQuiverWithRelations( field, dimension_of_projective_space );;

Q := P[1];

kQ := P[2];

AQ := QuotientOfPathAlgebra( kQ, P[3] ); 

quiver_representations := CategoryOfQuiverRepresentations( AQ: FinalizeCategory := false );

SetIsAbelianCategoryWithEnoughProjectives( quiver_representations, true );

AddEpimorphismFromSomeProjectiveObject( quiver_representations, ProjectiveCover );

AddIsProjective( quiver_representations, function( R )
                        return IsIsomorphism( ProjectiveCover( R ) ) ;
                      end );

AddLift( quiver_representations, compute_lift_in_quiver_rep );

AddColift( quiver_representations, compute_colift_in_quiver_rep );

AddGeneratorsOfExternalHom( quiver_representations, BasisOfHom );

Finalize( quiver_representations );

chains_quiver_representations := ChainComplexCategory( quiver_representations: FinalizeCategory := false );

AddLift( chains_quiver_representations, compute_lifts_in_complexes_of_quiver_reps );

AddColift( chains_quiver_representations, compute_colifts_in_complexes_of_quiver_reps );

AddGeneratorsOfExternalHom( chains_quiver_representations, generators_of_hom_for_chains_of_quiver_reps );

ModelStructureOnChainComplexes( chains_quiver_representations );

AddAreLeftHomotopic( chains_quiver_representations,
    function( phi, psi )
        return IsNullHomotopic( phi - psi );
    end );

Finalize( chains_quiver_representations );

homotopy_chains_quiver_representations := HomotopyCategory( chains_quiver_representations );

AddTriangulatedStructure( homotopy_chains_quiver_representations );

Finalize( homotopy_chains_quiver_representations );
# The indecomposable projective objects of the quiver
