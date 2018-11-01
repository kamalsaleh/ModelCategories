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

CP := CotangentBeilinsonQuiverWithRelations( field, dimension_of_projective_space );;

CQ := CP[1];

k_CQ := CP[2];

A_CQ := QuotientOfPathAlgebra( k_CQ, CP[3] ); 

cotangent_bundles_quiver_reps := CategoryOfQuiverRepresentations( A_CQ: FinalizeCategory := false );

SetIsAbelianCategoryWithEnoughProjectives( cotangent_bundles_quiver_reps, true );

AddEpimorphismFromSomeProjectiveObject( cotangent_bundles_quiver_reps, ProjectiveCover );

AddIsProjective( cotangent_bundles_quiver_reps, function( R )
                        return IsIsomorphism( ProjectiveCover( R ) ) ;
                      end );

AddLift( cotangent_bundles_quiver_reps, compute_lift_in_quiver_rep );

AddColift( cotangent_bundles_quiver_reps, compute_colift_in_quiver_rep );

AddGeneratorsOfExternalHom( cotangent_bundles_quiver_reps, BasisOfHom );

Finalize( cotangent_bundles_quiver_reps );

chains_cotangent_bundles_quiver_reps := ChainComplexCategory( cotangent_bundles_quiver_reps: FinalizeCategory := false );

AddLift( chains_cotangent_bundles_quiver_reps, compute_lifts_in_complexes_of_quiver_reps );

AddColift( chains_cotangent_bundles_quiver_reps, compute_colifts_in_complexes_of_quiver_reps );

AddGeneratorsOfExternalHom( chains_cotangent_bundles_quiver_reps, generators_of_hom_for_chains_of_quiver_reps );

ModelStructureOnChainComplexes( chains_cotangent_bundles_quiver_reps );

AddAreLeftHomotopic( chains_cotangent_bundles_quiver_reps,
    function( phi, psi )
        return IsNullHomotopic( phi - psi );
    end );

Finalize( chains_cotangent_bundles_quiver_reps );

homotopy_chains_cotangent_bundles_quiver_reps := HomotopyCategory( chains_cotangent_bundles_quiver_reps );

AddTriangulatedStructure( homotopy_chains_cotangent_bundles_quiver_reps );

Finalize( homotopy_chains_cotangent_bundles_quiver_reps );
# The indecomposable projective objects of the quiver

OP := BeilinsonQuiverWithRelations( field, dimension_of_projective_space );;

OQ := OP[1];

k_OQ := OP[2];

A_OQ := QuotientOfPathAlgebra( k_OQ, OP[3] ); 

vector_bundles_quiver_reps := CategoryOfQuiverRepresentations( A_OQ: FinalizeCategory := false );

SetIsAbelianCategoryWithEnoughProjectives( vector_bundles_quiver_reps, true );

AddEpimorphismFromSomeProjectiveObject( vector_bundles_quiver_reps, ProjectiveCover );

AddIsProjective( vector_bundles_quiver_reps, function( R )
                        return IsIsomorphism( ProjectiveCover( R ) ) ;
                      end );

AddLift( vector_bundles_quiver_reps, compute_lift_in_quiver_rep );

AddColift( vector_bundles_quiver_reps, compute_colift_in_quiver_rep );

AddGeneratorsOfExternalHom( vector_bundles_quiver_reps, BasisOfHom );

Finalize( vector_bundles_quiver_reps );

chains_vector_bundles_quiver_reps := ChainComplexCategory( vector_bundles_quiver_reps: FinalizeCategory := false );

AddLift( chains_vector_bundles_quiver_reps, compute_lifts_in_complexes_of_quiver_reps );

AddColift( chains_vector_bundles_quiver_reps, compute_colifts_in_complexes_of_quiver_reps );

AddGeneratorsOfExternalHom( chains_vector_bundles_quiver_reps, generators_of_hom_for_chains_of_quiver_reps );

ModelStructureOnChainComplexes( chains_vector_bundles_quiver_reps );

AddAreLeftHomotopic( chains_vector_bundles_quiver_reps,
    function( phi, psi )
        return IsNullHomotopic( phi - psi );
    end );

Finalize( chains_vector_bundles_quiver_reps );

homotopy_chains_vector_bundles_quiver_reps := HomotopyCategory( chains_vector_bundles_quiver_reps );

AddTriangulatedStructure( homotopy_chains_vector_bundles_quiver_reps );

Finalize( homotopy_chains_vector_bundles_quiver_reps );
# The indecomposable projective objects of the quiver

Eq_cotangent_to_vector_bundles := CapFunctor( "some name", homotopy_chains_cotangent_bundles_quiver_reps, homotopy_chains_vector_bundles_quiver_reps );
AddObjectFunction( Eq_cotangent_to_vector_bundles, 
    function( h_rep )
    local F, ChF, a, G, ChG;
    F := FromQuiverRepsToGradedLeftPresFunctor_CotangentBundles( A_CQ, S );
    ChF := ExtendFunctorToChainComplexCategoryFunctor( F );
    a := ApplyFunctor( ChF, UnderlyingReplacement( h_rep ) );
    a := CofibrantModel( a );
    G := FromGradedLeftPresToQuiverRepsFunctor_VectorBundles( S, A_OQ );
    ChG := ExtendFunctorToChainComplexCategoryFunctor( G );
    return AsObjectInHomotopyCategory( ApplyFunctor( ChG, a ) );
end );

AddMorphismFunction( Eq_cotangent_to_vector_bundles, 
    function( source, phi, range )
    local F, ChF, a, G, ChG;
    F := FromQuiverRepsToGradedLeftPresFunctor_CotangentBundles( A_CQ, S );
    ChF := ExtendFunctorToChainComplexCategoryFunctor( F );
    a := ApplyFunctor( ChF, UnderlyingReplacement( phi ) );
    a := MorphismBetweenCofibrantModels( a );
    G := FromGradedLeftPresToQuiverRepsFunctor_VectorBundles( S, A_OQ );
    ChG := ExtendFunctorToChainComplexCategoryFunctor( G );
    return AsMorphismInHomotopyCategory( ApplyFunctor( ChG, a ) );
end );

FromVectorBundlesToVectorBundles := function( S, A )
local F, n;
n := Length( IndecProjRepresentations( A ) );
F := CapFunctor( "some name", vector_bundles_quiver_reps, vector_bundles_quiver_reps );
AddObjectFunction( F, 
    function( rep )
    local i, K, G;
    if IsZeroForObjects( rep ) then 
        return rep;
    fi;

    for i in [ -n .. -2 ] do
        if IsEqualForObjects( rep, StandardVectorBundle( A, i ) ) then
            return StandardVectorBundle( A, i + 1 );
        fi;
    od;
    
    if rep = StandardVectorBundle( A, -1 ) then
        K := Source( KoszulChainMorphism( S ) );
        G := FromGradedLeftPresToQuiverRepsFunctor_VectorBundles(S, A);
        G := ExtendFunctorToChainComplexCategoryFunctor( G );
        K := ApplyFunctor( G, K );
        return HomologyAt( K, 0 );
    fi;

    return DirectSum( List( PartitionOfProjRep_Vector_Bundles( rep ), r -> ApplyFunctor( F, r ) ) );
end );

AddMorphismFunction( F, 
    function( source_, phi, range_ )
    local s, r, AQ, indec_projectives, source, range, i, j, mat;
    s := fail;
    r := fail;

    if IsZeroForMorphisms( phi ) then
        return ZeroMorphism( source_, range_ );
    fi;

    for i in [ -n .. -2 ] do
        if IsEqualForObjects( Source( phi ), StandardVectorBundle( A, i ) ) then
            s := i;
        fi;

        if IsEqualForObjects( Range( phi ), StandardVectorBundle( A, i ) ) then
            r := i;
        fi;

        if s <> fail and r <> fail then
            break;
        fi;
    od;

    if s <> fail and r <> fail then
        return solve( phi )*BasisBetweenVectorBundles( A, s + 1, r + 1 );
    fi;

    if IsEqualForObjects( Source( phi ), StandardVectorBundle( A, -1 ) ) then s := -1; fi;
    if IsEqualForObjects( Range( phi ),  StandardVectorBundle( A, -1 ) ) then r := -1; fi;

    if s = -1 and r = -1 then
        return RowsOfMatrix( RightMatrixOfLinearTransformation( MapForVertex( phi, 1 ) ) )[1]*[ IdentityMorphism( source ) ];
    fi;

    if s = -1 or r = -1 then
        return solve( phi )* BasisBetweenVectorBundles( S, A, s + 1, r + 1 );
    fi;

    indec_projectives := Concatenation( IndecProjRepresentations( A ), [ ZeroObject( phi ) ] );

    source := PartitionOfProjRep_Vector_Bundles( Source( phi ) );
    range := PartitionOfProjRep_Vector_Bundles( Range( phi ) );

    if Length( source ) = 1 and Length( range ) = 1 then
        i := Position( indec_projectives, source[ 1 ] );
        j := Position( indec_projectives, range[ 1 ] );

        if i = n + 1 or j = n + 1 then  
            return [ [ rec( coefficients := [ ], indices := [ -i, -j ] ) ] ];
        else
            return [ [ rec( coefficients := solve( phi ), indices := [ -i, -j ] ) ] ];
        fi;
    fi;

    mat := List( [ 1 .. Length( source ) ], 
        i -> List( [ 1 .. Length( range ) ],
            j -> ApplyFunctor( F, PreCompose(
                [
                    InjectionOfCofactorOfDirectSum(source, i),
                    phi,
                    ProjectionInFactorOfDirectSum(range, j )
                ]
    ) ) ) );

    return MorphismBetweenDirectSums( mat );
end );

return F;

end;


# Autofunctor_VectorBundles := CapFunctor( "Autofunctor on the homotopy category of standard Beilinson quiver",
# homotopy_chains_vector_bundles_quiver_reps, homotopy_chains_vector_bundles_quiver_reps );
# F := FromVectorBundlesToVectorBundles( S, A_OQ );
# ChF := ExtendFunctorToChainComplexCategoryFunctor( F );
# H0 := HomologyFunctorAt( chains_vector_bundles_quiver_reps, vector_bundles_quiver_reps, 0 );
# AddObjectFunction( Autofunctor_VectorBundles,
#     function( C )
#     local rep_C;
#     rep_C := UnderlyingReplacement( C );
#     ChF_rep_C := ApplyFunctor( ChF, rep_C );
#     
# end );