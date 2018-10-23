LoadPackage( "GradedModulePresentations" );
LoadPackage( "ModelCategories" );
LoadPackage( "TriangulatedCategoriesForCAP" );
LoadPackage( "FunctorCategories" );
LoadPackage( "LinearAlgebraForCAP" );

dimension_of_projective_space := 2;
ReadPackage( "BBGG", "examples/glp_over_g_exterior_algebra/stable_cat_of_glp_over_exterior_algebra.g" );
ReadPackage( "ModelCategories", "examples/tools/Triangulated_Structure.g" );
homotopy_chains_graded_lp_cat_sym := HomotopyCategory( chains_graded_lp_cat_sym :FinalizeCategory := false );
AddTriangulatedStructure( homotopy_chains_graded_lp_cat_sym );
Finalize( homotopy_chains_graded_lp_cat_sym );

# Please pull the branch devel2 or mohamed of QPA2 at https://github.com/kamalsaleh/QPA2
ReadPackage( "ModelCategories", "examples/tools/left_homotopy_in_chains_of_rep_over_quiver.g" );

homalg_field := HomalgFieldOfRationals( );
quiver_field := Rationals;

# Beilinson Quiver for P^n, n = 2

#         x10            x20         
#  1 ---  x11 ---> 2 --- x21 ---> 3
#         x12            x22         

homalg_P := CotangentBeilinsonQuiverWithRelations_FC( homalg_field, dimension_of_projective_space );;
quiver_P := CotangentBeilinsonQuiverWithRelations_FC( quiver_field, dimension_of_projective_space );;


quiver := quiver_P[1];

k_quiver := quiver_P[2];

A_quiver := QuotientOfPathAlgebra( quiver_P[2], quiver_P[3] );


k_homalg := homalg_P[2];

A_homalg := QuotientOfPathAlgebra( homalg_P[2], homalg_P[3] );

B := Algebroid( k_homalg, homalg_P[3] );

matrix_cat := MatrixCategory( homalg_field );

quiver_reps_cat := CategoryOfQuiverRepresentations( A_quiver: FinalizeCategory := true );
functors_cat := Hom( B, matrix_cat: FinalizeCategory := true );

DeclareOperation( "FromRepsCatToFunctorsCat", [ IsQuiverRepresentationCategory, IsCapCategory ] );
InstallMethodWithCache( FromRepsCatToFunctorsCat,
                        [ IsQuiverRepresentationCategory, IsCapCategory ],
function( quiver_representations_cat, functors_cat )
local rep_cat_to_func_cat, B, AQ, quiver, homalg_field;
rep_cat_to_func_cat := CapFunctor( "from representations cat to functors cat", quiver_representations_cat, functors_cat );
B := Source( functors_cat );
AQ := UnderlyingQuiverAlgebra( B );
quiver := UnderlyingQuiver( B );
homalg_field := CommutativeRingOfLinearCategory( Range( functors_cat ) );

AddObjectFunction( rep_cat_to_func_cat,
function( rep )
local obj,  dimension_vec, mor, matrices, i;
obj := rec( );
dimension_vec := DimensionVector( rep );

for i in [ 1 .. Length( dimension_vec ) ] do 
obj!.( String( Vertex( quiver, i ) ) ) := VectorSpaceObject( dimension_vec[ i ], homalg_field );
od;

mor := rec( );
matrices := MatricesOfRepresentation( rep );
matrices := List( matrices, mat -> 
    HomalgMatrix( RowsOfMatrix( mat ), DimensionsMat( mat )[1], DimensionsMat( mat )[2], homalg_field ) );

for i in [ 1 .. Length( matrices ) ] do;
mor!.( String( Arrow( quiver, i ) ) ) := 
    VectorSpaceMorphism( obj!.( String( Source( Arrow( quiver, i ) ) )  ), 
                        matrices[i],
                         obj!.( String( Target( Arrow( quiver, i ) ) )  ) );
od;

return AsObjectInHomCategory( B, obj, mor );
end );

AddMorphismFunction( rep_cat_to_func_cat,
    function( source, rep_mor, range )
    local matrices, mor, i;
    matrices := MatricesOfRepresentationHomomorphism( rep_mor );
    matrices := List( matrices, mat -> 
        HomalgMatrix( RowsOfMatrix( mat ), DimensionsMat( mat )[1], DimensionsMat( mat )[2], homalg_field ) );
    
    mor := rec( );
    for i in [ 1 .. Length( matrices ) ] do
    mor!.( String( Vertex( quiver, i ) ) ) := 
        VectorSpaceMorphism( 
            VectorSpaceObject( NrRows( matrices[ i ] ), homalg_field ),
            matrices[ i ],
            VectorSpaceObject( NrColumns( matrices[ i ] ), homalg_field )
        );
    od;
    return AsMorphismInHomCategory( source, mor, range );
    end );

return rep_cat_to_func_cat;
end );

DeclareOperation( "FromFunctorsCatToRepsCat", [ IsCapCategory, IsQuiverRepresentationCategory ] );
InstallMethodWithCache( FromFunctorsCatToRepsCat,
                        [ IsCapCategory, IsQuiverRepresentationCategory ],
    function( functors_cat, quiver_representations_cat )
    local func_cat_to_rep_cat, B, AQ, quiver, quiver_field;

    func_cat_to_rep_cat := CapFunctor( "some name", functors_cat, quiver_representations_cat );
    B := Source( functors_cat );
    AQ := AlgebraOfCategory( quiver_representations_cat );
    quiver := UnderlyingQuiver( B );

    quiver_field := LeftActingDomain( PathAlgebra( AQ ) );
    
    AddObjectFunction( func_cat_to_rep_cat, 
    function( func )
    local U, V, L;
    U := UnderlyingCapTwoCategoryCell( func );
    V := List( Vertices( quiver ), 
        v -> Dimension( ApplyFunctor( U, B.( String( v ) ) ) ) );
    L := List( Arrows( quiver ), l -> UnderlyingMatrix( 
                        ApplyFunctor( U, B.( String( l ) ) ) ) );

    L := List( L, l -> MatrixByRows( quiver_field, [ NrRows( l ), NrColumns( l ) ],
                EntriesOfHomalgMatrixAsListList( l ) ) );
    return QuiverRepresentation( AQ, V, L );
    end );

    AddMorphismFunction( func_cat_to_rep_cat, 
    function( source, mor, range )
    local U, V;
    U := UnderlyingCapTwoCategoryCell( mor );

    V := List( Vertices( quiver ), v -> UnderlyingMatrix( 
                    ApplyNaturalTransformation( U, B.( String( v ) ) ) ) );

    V := List( V, v -> MatrixByRows( quiver_field, [ NrRows( v ), NrColumns( v ) ],
            EntriesOfHomalgMatrixAsListList( v ) ) );
    return QuiverRepresentationHomomorphism( source, range, V );
    end );
    return func_cat_to_rep_cat;
end );

quit;