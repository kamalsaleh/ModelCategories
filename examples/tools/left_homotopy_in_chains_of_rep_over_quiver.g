
# This example requires QPA2 in my devel2 branch in github: https://github.com/kamalsaleh/QPA2.git
LoadPackage( "QPA" );
LoadPackage( "ComplexesForCAP" );
LoadPackage( "ModelCategories" );
LoadPackage( "TriangulatedCategoriesForCAP");
LoadPackage( "RingsForHomalg" );
ReadPackage( "ModelCategories", "examples/tools/Triangulated_Structure.g" );

DeclareOperation( "LinearQuiver", [ IsDirection, IsObject, IsInt, IsInt ] );
DeclareOperation( "LinearRightQuiver", [ IsObject, IsInt, IsInt ] );
DeclareOperation( "LinearLeftQuiver", [ IsObject, IsInt, IsInt ] );
DeclareOperation( "ArrowsBetweenTwoVertices", [ IsVertex, IsVertex ] );
DeclareOperation( "BasisOfHom", [ IsQuiverRepresentation, IsQuiverRepresentation ] );


# The natural place for this is file matrix.gi in QPA.
InstallMethod( KroneckerProduct, "for two QPA matrices",
    [ IsQPAMatrix, IsQPAMatrix ],
  function( M1, M2 )
  local k, dim1, dim2, mat;

  k := BaseDomain( M1 );

  if not IsIdenticalObj( k, BaseDomain( M2 ) ) then
    Error( "Base domains of the given matrices are not identical" );
  fi;

  dim1 := DimensionsMat( M1 );
  dim2 := DimensionsMat( M2 );

  if dim1[1]*dim2[1] = 0 or dim1[2]*dim2[2] = 0 then
        return MatrixByRows( k, [ dim1[1]*dim2[1], dim1[2]*dim2[2] ], [] );
  fi;

  mat := KroneckerProduct( RowsOfMatrix( M1 ), RowsOfMatrix( M2 ) );

  return MatrixByRows( k, [ dim1[1]*dim2[1], dim1[2]*dim2[2] ], mat );

end );

compute_basis_of_external_hom := function( S, R )
local A, Q, field, S_dimensions, R_dimensions, nr_cols_in_block1, nr_cols_in_block3,
nr_cols_in_block5, nr_of_vertices, nr_of_arrows, nr_rows_of_block, mat, L, vector,
block_1, block_2, block_3, block_4, block_5, block, i, u, v, matrices, id_1, id_2,
source_of_arrow, range_of_arrow, S_i, R_i, Vec, hom;

A := AlgebraOfRepresentation( S );
Q := QuiverOfAlgebra( A );

field := LeftActingDomain( A );

Vec := function( M )
    return MatrixByCols( field, [ Product( DimensionsMat( M ) ), 1 ], [ Concatenation( ColsOfMatrix( M ) ) ] );
end;

S_dimensions := DimensionVector( S );
R_dimensions := DimensionVector( R );

nr_of_vertices := Length( S_dimensions );

mat := MakeZeroMatrix( field, 0, S_dimensions*R_dimensions );

nr_of_arrows := NumberOfArrows( Q );

for i in [ 1 .. nr_of_arrows ] do

    source_of_arrow := VertexNumber( Source( Arrow( Q, i ) ) );
    range_of_arrow := VertexNumber( Target( Arrow( Q, i ) ) );

    S_i := RightMatrixOfLinearTransformation( MapForArrow( S, i ) );
    R_i := RightMatrixOfLinearTransformation( MapForArrow( R, i ) );

    id_1 := IdentityMatrix( field, DimensionsMat( S_i )[ 1 ] );
    id_2 := IdentityMatrix( field, DimensionsMat( R_i )[ 2 ] );

    nr_rows_of_block := DimensionsMat( S_i )[ 1 ]*DimensionsMat( R_i )[ 2 ];

    u := Minimum( source_of_arrow, range_of_arrow );
    v := Maximum( source_of_arrow, range_of_arrow );

    if u = 1 then
        nr_cols_in_block1 := 0;
    else
        nr_cols_in_block1 := S_dimensions{[1..u-1]}*R_dimensions{[1..u-1]};
    fi;

    block_1 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block1 );

    if u = source_of_arrow then
        block_2 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
    elif u = range_of_arrow then
        block_2 := KroneckerProduct( id_2, S_i );
    fi;

    if v-u in [ 0, 1 ] then
        nr_cols_in_block3 := 0;
    else
        nr_cols_in_block3 := S_dimensions{[u+1..v-1]}*R_dimensions{[u+1..v-1]};
    fi;

    block_3 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block3 );

    if v = source_of_arrow then
        block_4 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
    elif v = range_of_arrow then
        block_4 := KroneckerProduct( id_2, S_i );
    fi;

    if v = nr_of_vertices then
        nr_cols_in_block5 := 0;
    else
        nr_cols_in_block5 := S_dimensions{[v+1..nr_of_vertices]}*R_dimensions{[v+1..nr_of_vertices]};
    fi;

    block_5 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block5 );

    block := StackMatricesHorizontally( [ block_1, block_2, block_3, block_4, block_5 ] );

    mat := StackMatricesVertically( mat, block );
od;
mat := NullspaceMat( TransposedMat( mat ) );

if mat = fail then
    return [ ];
fi;

hom := [ ];

for L in RowsOfMatrix( mat ) do
matrices := [ ];
    for i in [ 1 .. nr_of_vertices ] do
        mat := L{[1..S_dimensions[i]*R_dimensions[i]]};
        Add( matrices, MatrixByCols( field, [ S_dimensions[i], R_dimensions[i] ], mat ) );
        L := L{[S_dimensions[i]*R_dimensions[i]+1 .. Length( L ) ]};
    od;
    Add( hom, QuiverRepresentationHomomorphism( S, R, matrices ) );
od;
return hom;
end;

InstallMethodWithCache( BasisOfHom,
                [ IsQuiverRepresentation, IsQuiverRepresentation ],
    function( rep1, rep2 )
    #return BasisVectors( CanonicalBasis( Hom( rep1, rep2 ) ) );
    return compute_basis_of_external_hom( rep1, rep2 );
end );

InstallMethod( LinearQuiver,
	[ IsDirection, IsObject, IsInt, IsInt ],
  function( d, k, m, n )
    local L, kL, c, l, constructor;
    if d = RIGHT then
      	constructor := "RightQuiver";
    else
        constructor := "LeftQuiver";
    fi;

    if m<=n then
    	L := ValueGlobal(constructor)(  Concatenation( "L(v", String(m), ")[d", String(m), "]" ), n - m + 1,
    		List( [ m .. n - 1 ], i-> [ Concatenation( "v", String(i) ), Concatenation( "v", String(i+1) ) ]  ) );
    	kL := PathAlgebra( k, L );
    	c := ArrowLabels( L );
    	l := List( [ 1 .. Length( c )-1 ], i -> [ c[i], c[i+1] ] );
	if d = RIGHT then
    	    l := List( l, label -> PrimitivePathByLabel( L, label[1] )*PrimitivePathByLabel( L, label[2] ) );
	else
	    l := List( l, label -> PrimitivePathByLabel( L, label[2] )*PrimitivePathByLabel( L, label[1] ) );
	fi;
    	l := List( l, r -> QuiverAlgebraElement( kL, [1], [r] ) );
    	return [ L, kL, l ];
    else
        L := ValueGlobal(constructor)(  Concatenation( "L(v", String(n), ")[d", String(n+1), "]" ), m - n + 1,
	        List( [ n .. m - 1 ], i-> [ Concatenation( "v", String(i+1) ), Concatenation( "v", String(i) ) ]  ) );
        kL := PathAlgebra( k, L );
	c := ArrowLabels( L );
	l := List( [ 1 .. Length( c )-1 ], i -> [ c[i+1], c[i] ] );
	if d = RIGHT then
	    l := List( l, label -> PrimitivePathByLabel( L, label[1] )*PrimitivePathByLabel( L, label[2] ) );
	else
	    l := List( l, label -> PrimitivePathByLabel( L, label[2] )*PrimitivePathByLabel( L, label[1] ) );
	fi;
	l := List( l, r -> QuiverAlgebraElement( kL, [1], [r] ) );
	L!.("m") := m;
	L!.("n") := n;
	return [ L, kL, l ];
    fi;
end );

InstallMethod( LinearRightQuiver,
	[ IsObject, IsInt, IsInt ],
  function( k, m, n )
    return LinearQuiver( RIGHT, k, m, n );
end );

InstallMethod( LinearLeftQuiver,
	[ IsObject, IsInt, IsInt ],
  function( k, m, n )
    return LinearQuiver( LEFT, k, m, n );
end );

InstallMethod( ArrowsBetweenTwoVertices,
		[ IsVertex, IsVertex ],
  function( v1, v2 )
    return Intersection( OutgoingArrows( v1 ), IncomingArrows( v2 ) );
end );

product_of_algebras := function( Aq, m, n )
    local k, Lmn, AL;
    k := LeftActingDomain( Aq );
    Lmn := LinearRightQuiver( k, m, n );
    if Lmn[3] = [ ] then
        AL := Lmn[2];
    else
        AL := QuotientOfPathAlgebra( Lmn[2], Lmn[3] );
    fi;
    return TensorProductOfAlgebras( AL, Aq );
end;

convert_chain_or_cochain_to_representation :=
    function( C, A  )
    local L, m, n, Q, dimension_vector, matrices1, matrices2, matrices;

    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
    if IsChainComplex( C ) then
        Q := QuiverOfAlgebra( A );
        dimension_vector := Concatenation( List( [ m .. n ], i-> DimensionVector( C[ i ] ) ) );
        matrices1 := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentation( C[ i ] ) ) );
        matrices2 := Concatenation( List( [ m + 1 .. n ], i-> MatricesOfRepresentationHomomorphism( C^i ) ) );
        matrices := Concatenation( matrices1, matrices2 );
        return QuiverRepresentation( A, dimension_vector, Arrows( Q ), matrices );
    else
        Q := QuiverOfAlgebra( A );
        dimension_vector := Concatenation( List( [ m .. n ], i-> DimensionVector( C[ i ] ) ) );
        matrices1 := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentation( C[ i ] ) ) );
        matrices2 := Concatenation( List( [ m .. n - 1 ], i-> MatricesOfRepresentationHomomorphism( C^i ) ) );
        matrices := Concatenation( matrices1, matrices2 );
        return QuiverRepresentation( A, dimension_vector, Arrows( Q ), matrices );
    fi;

end;

convert_chain_or_cochain_mor_to_representation_mor :=
    function( phi, A )
    local L,m,n, matrices, r1, r2;
    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
    matrices := Concatenation( List( [ m .. n ], i -> MatricesOfRepresentationHomomorphism( phi[ i ] ) ) );
    r1 := convert_chain_or_cochain_to_representation( Source( phi ), A );
    r2 := convert_chain_or_cochain_to_representation( Range( phi ), A );
    return QuiverRepresentationHomomorphism( r1, r2, matrices );
end;


convert_rep_mor_to_complex_mor :=
    function( C1, C2, mor, A )
    local Q, L, q, m, n, mats;
    # Do the compatibility stuff
    Q := QuiverOfAlgebra( A );
    L := QuiverOfAlgebra( TensorProductFactors( A )[1] );
    q := QuiverOfAlgebra( TensorProductFactors( A )[2] );
    m := ShallowCopy( Label( Vertex( L, 1 ) ) );
    RemoveCharacters( m, "v" );
    m := Int(m);
    n := m + NumberOfVertices( L ) - 1;
#     maps := MatricesOfRepresentationHomomorphism( mor );
    mats := MatricesOfRepresentationHomomorphism( mor );
    mats := List( [ 1 .. NumberOfVertices( L ) ],
                i -> List( [ 1 .. NumberOfVertices( q ) ],
                        j-> mats[ (i-1)*NumberOfVertices( q ) + j ] ) );
    mats := List( [ m .. n ], k -> QuiverRepresentationHomomorphism( C1[k], C2[k], mats[k-m+1] ) );
    if IsChainComplex( C1 ) then
        return ChainMorphism( C1, C2, mats, m );
    else
        return CochainMorphism( C1, C2, mats, m );
    fi;
end;

generators_of_hom_for_chains_of_quiver_reps :=
    function( C1, C2 )
    local m, n, A, R1, R2, B;

    m := Minimum( ActiveLowerBound( C1 ), ActiveLowerBound( C2 ) ) + 1;
    n := Maximum( ActiveUpperBound( C1 ), ActiveUpperBound( C2 ) ) - 1;
    if IsChainComplex( C1 ) then
        A := product_of_algebras( AlgebraOfRepresentation( C1[m] ), n, m );
    else
        A := product_of_algebras( AlgebraOfRepresentation( C1[m] ), m, n );
    fi;
    R1 := convert_chain_or_cochain_to_representation( C1, A );
    R2 := convert_chain_or_cochain_to_representation( C2, A );
    B := BasisOfHom( R1, R2 );
    return List( B, mor -> convert_rep_mor_to_complex_mor( C1, C2, mor, A ) );
end;

compute_lift_in_quiver_rep :=
    function( f, g )
    local homs_basis, Q, k, V, homs_basis_composed_with_g, L, vector, mat, sol, lift, h;

    if IsZeroForObjects( Range( f ) ) then
        return ZeroMorphism( Source( f ), Source( g ) );
    fi;

    homs_basis := BasisOfHom( Source( f ), Source( g ) );
    # if homs_basis = [] then there is only the zero morphism between source(f) and source(g)
    # Thus f must be zero in order for lift to exist.
    if homs_basis = [ ] then
      if IsZeroForMorphisms( f ) then
        return ZeroMorphism( Source( f ), Source( g ) );
      else
        return fail;
      fi;
    fi;
    Q := QuiverOfRepresentation( Source( f ) );
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    V := Vertices( Q );
    homs_basis_composed_with_g := List( homs_basis, m -> PreCompose( m, g ) );
    L := List( V, v -> Concatenation( [ RightMatrixOfLinearTransformation( MapForVertex( f, v ) ) ],
                                        List( homs_basis_composed_with_g, h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
    L := Filtered( L, l -> ForAll( l, m -> not IsZero( DimensionsMat( m )[ 1 ]*DimensionsMat( m )[ 2 ] ) ) );
    L := List( L, l ->  List( l, m -> MatrixByCols( k, [ Concatenation( ColsOfMatrix( m ) ) ] ) ) );

    L := List( TransposedMat( L ), l -> StackMatricesVertically( l ) );
    vector := StandardVector( k, ColsOfMatrix( L[ 1 ] )[ 1 ] );
    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( L ) ], i -> L[ i ] ) ) );
    sol := SolutionMat( mat, vector );

    if sol = fail then
        return fail;
    else

    sol := ShallowCopy( AsList( sol ) );

    lift := ZeroMorphism( Source( f ), Source( g ) );
    for h in homs_basis do
         if not IsZero( sol[ 1 ] ) then
             lift := lift + sol[ 1 ]*h;
         fi;
    Remove( sol, 1 );
    od;
    fi;
    return lift;
end;

compute_colift_in_quiver_rep :=
    function( f, g )
    local homs_basis, Q, k, V, homs_basis_composed_with_f, L, vector, mat, sol, colift, h;

    homs_basis := BasisOfHom( Range( f ), Range( g ) );
    # if homs_basis = [] then there is only the zero morphism between range(f) and range(g)
    # Thus g must be zero in order for colift to exist.
    if homs_basis = [ ] then
      if IsZeroForMorphisms( g ) then
	    return ZeroMorphism( Range( f ), Range( g ) );
      else
	    return fail;
      fi;
    fi;
    Q := QuiverOfRepresentation( Source( f ) );
    k := LeftActingDomain( AlgebraOfRepresentation( Source( f ) ) );
    V := Vertices( Q );
    homs_basis_composed_with_f := List( homs_basis, m -> PreCompose( f, m ) );
    L := List( V, v -> Concatenation( [ RightMatrixOfLinearTransformation( MapForVertex( g, v ) ) ],
                                        List( homs_basis_composed_with_f, h -> RightMatrixOfLinearTransformation( MapForVertex( h, v ) ) ) ) );
    # this line is added because I get errors when MatrixByCols recieve empty matrix
    # it is still true since i only delete zero matrices from the equation system.
    L := Filtered( L, l -> ForAll( l, m -> not IsZero( DimensionsMat( m )[ 1 ]*DimensionsMat( m )[ 2 ] ) ) );
    L := List( L, l ->  List( l, m -> MatrixByCols( k, [ Concatenation( ColsOfMatrix( m ) ) ] ) ) );

    L := List( TransposedMat( L ), l -> StackMatricesVertically( l ) );
    vector := StandardVector( k, ColsOfMatrix( L[ 1 ] )[ 1 ] );
    mat := TransposedMat( StackMatricesHorizontally( List( [ 2 .. Length( L ) ], i -> L[ i ] ) ) );
    sol := SolutionMat( mat, vector );

    if sol = fail then
     return fail;
    else
    sol := ShallowCopy( AsList( sol ) );
    colift := ZeroMorphism( Range( f ), Range( g ) );
    for h in homs_basis do
        if not IsZero( sol[ 1 ] ) then
            colift := colift + sol[ 1 ]*h;
        fi;
    Remove( sol, 1 );
    od;

    fi;
    return colift;
end;


dual_functor :=
    function( cat )
    local A, Q, A_op, Q_op, cat_op, dual, cat_of_op_quiver;

    cat_op := Opposite( cat );
    A := AlgebraOfCategory( cat );
    Q := QuiverOfAlgebra( A );
    A_op := OppositeAlgebra( A );
    Q_op := QuiverOfAlgebra( A_op );
    cat_of_op_quiver := CategoryOfQuiverRepresentations( A_op );
    dual := CapFunctor( "Dual functor", cat_op, cat_of_op_quiver );
    AddObjectFunction( dual,
        function( r )
        return QuiverRepresentation( A_op, DimensionVector( Opposite(r) ), Arrows( Q_op ), List( MatricesOfRepresentation( Opposite(r) ), TransposedMat ) );
        end );
    AddMorphismFunction( dual,
        function( new_source, phi, new_range )
        return QuiverRepresentationHomomorphism( new_source, new_range, List( MatricesOfRepresentationHomomorphism( Opposite( phi ) ), TransposedMat ) );
        end );
    return dual;
end;

compute_lifts_in_complexes_of_quiver_reps :=
    function( f, g )
    local m, n, A, f_, g_, lift;
    m := Minimum( ActiveLowerBound( Source(f) ), ActiveLowerBound( Source(g) ) ) + 1;
    n := Maximum( ActiveUpperBound( Source(f) ), ActiveUpperBound( Source(g) ) ) - 1;

    if IsChainMorphism( f ) then
        A := product_of_algebras( AlgebraOfRepresentation( Source(f[ m ]) ), n, m );
    else
        A := product_of_algebras( AlgebraOfRepresentation( Source(f[ m ]) ), m, n );
    fi;

    f_ := convert_chain_or_cochain_mor_to_representation_mor( f, A );
    g_ := convert_chain_or_cochain_mor_to_representation_mor( g, A );

    lift := compute_lift_in_quiver_rep( f_, g_ );

    if lift = fail then
        return fail;
    else
        return convert_rep_mor_to_complex_mor( Source(f), Source( g ), lift, A );
    fi;
end;

compute_colifts_in_complexes_of_quiver_reps :=
    function( f, g )
    local m, n, A, f_, g_, colift;
    m := Minimum( ActiveLowerBound( Range(f) ), ActiveLowerBound( Range(g) ) ) + 1;
    n := Maximum( ActiveUpperBound( Range(f) ), ActiveUpperBound( Range(g) ) ) - 1;

    if IsChainMorphism( f ) then
        A := product_of_algebras( AlgebraOfRepresentation( Source(f[ m ]) ), n, m );
    else
        A := product_of_algebras( AlgebraOfRepresentation( Source(f[ m ]) ), m, n );
    fi;

    f_ := convert_chain_or_cochain_mor_to_representation_mor( f, A );
    g_ := convert_chain_or_cochain_mor_to_representation_mor( g, A );

    colift := compute_colift_in_quiver_rep( f_, g_ );

    if colift = fail then
        return fail;
    else
        return convert_rep_mor_to_complex_mor( Range(f), Range( g ), colift, A );
    fi;
end;

quit;

BeilinsonQuiverWithRelations := function( field, n )
local i,j,u,v,arrows,kQ,AQ,Q,s;

s := "";
for i in [ -n-1 .. -1 ] do
if i <> -1 then
    s := Concatenation( [ s, "O(", String( i ), ") --", String( n + 1 ), "--> " ] );
else
    s := Concatenation( [ s, "O(", String( i ), ")" ] );
fi;
od;

u := "";
for i in [ 1 .. n ] do
for j in [ 0 .. n ] do
u := Concatenation( u,"x",String(i),String(j),":",String(i),"->",String(i+1),"," );
od;
od;
Remove( u, Length( u ) );
u := Concatenation( "Q(", String(n+1),")[",u,"]" );
Q := RightQuiver( u );
Q!.String := s;
arrows := Arrows( Q );
kQ := PathAlgebra( field, Q );
v := [ ];
for i in [ 1 .. n-1 ] do
for j in Combinations( [ 0 .. n ], 2 ) do
Add( v, kQ.(Concatenation( "x", String(i),String(j[1])) )* kQ.(Concatenation( "x", String(i+1),String(j[2]) ) )-
        kQ.(Concatenation( "x",String(i),String(j[2]) ) )* kQ.(Concatenation( "x", String(i+1),String(j[1]) ) ) );
od;
od;
#AQ := QuotientOfPathAlgebra( kQ, v );
return [Q,kQ,v];
end;

CotangentBeilinsonQuiverWithRelations := function( field, n )
local i,j,u,v,arrows,kQ,AQ,Q,s;

s := "";
for i in Reversed( [ 0 .. n ] ) do
if i <> 0 then
    s := Concatenation(s, "Ω^", String(i), "(", String(i), ") --",String( n + 1 ),"--> " );
else
    s := Concatenation( s, "Ω^", String(i), "(", String(i), ")" );
fi;
od;

u := "";
for i in [ 1 .. n ] do
for j in [ 0 .. n ] do
u := Concatenation( u,"y",String(i),String(j),":",String(i),"->",String(i+1),"," );
od;
od;
Remove( u, Length( u ) );
u := Concatenation( "Q(", String(n+1),")[",u,"]" );
Q := RightQuiver( u );
Q!.String := s;
arrows := Arrows( Q );
kQ := PathAlgebra( field, Q );
v := [ ];
for i in [ 1 .. n-1 ] do
for j in Combinations( [ 0 .. n ], 2 ) do
Add( v, kQ.(Concatenation( "y", String(i),String(j[1])) )* kQ.(Concatenation( "y", String(i+1),String(j[2]) ) )+
        kQ.(Concatenation( "y",String(i),String(j[2]) ) )* kQ.(Concatenation( "y", String(i+1),String(j[1]) ) ) );
od;
od;

for i in [ 1 .. n-1 ] do
for j in [ 0 .. n ] do
Add( v, kQ.(Concatenation( "y", String(i),String(j)) )* kQ.(Concatenation( "y", String(i+1),String(j) ) ) );
od;
od;
#AQ := QuotientOfPathAlgebra( kQ, v );
return [Q,kQ,v];
end;

CotangentBeilinsonQuiverWithRelations_FC := function( field, n )
local i,j,u,v,arrows,kQ,AQ,Q;

for i in [ 0 .. n ] do
for j in [ 1 .. n ] do
Print( "→ " );
od;
Print( "\n" );
od;

u := "";
for i in [ 1 .. n ] do
for j in [ 0 .. n ] do
u := Concatenation( u,"x",String(i),String(j),":",String(i),"->",String(i+1),"," );
od;
od;
Remove( u, Length( u ) );
u := Concatenation( "Q(", String(n+1),")[",u,"]" );
Q := RightQuiver( u );
arrows := Arrows( Q );
kQ := PathAlgebra( field, Q );
v := [ ];
for i in [ 1 .. n-1 ] do
for j in Combinations( [ 0 .. n ], 2 ) do
Add( v, kQ.(Concatenation( "x", String(i),String(j[1])) )* kQ.(Concatenation( "x", String(i+1),String(j[2]) ) )+
        kQ.(Concatenation( "x",String(i),String(j[2]) ) )* kQ.(Concatenation( "x", String(i+1),String(j[1]) ) ) );
od;
od;

for i in [ 1 .. n-1 ] do
for j in [ 0 .. n ] do
Add( v, kQ.(Concatenation( "x", String(i),String(j)) )* kQ.(Concatenation( "x", String(i+1),String(j) ) ) );
od;
od;
# AQ := Algebroid( kQ, v );
return [Q,kQ,v];
end;

DeclareAttribute( "kamal", IsQuiverAlgebra );

InstallMethod( kamal, [ IsQuiverAlgebra ],
function( AQ )
local indec_projectives, n, morphisms, j, k, l, current;
indec_projectives := Reversed( IndecProjRepresentations( AQ ) );
n := Length( indec_projectives );
morphisms := List( [ 1 .. n-1 ], i -> BasisOfHom( indec_projectives[i], indec_projectives[i+1] ) );

for j in [ 2 .. n-1] do
    current := [ ];
    for k in [ 1 .. n ] do
    for l in [ 1 .. n ] do
        if IsZeroForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ) ) then
            current[k] := morphisms[j][l];
        fi;
    od;
    od;
    morphisms[ j ] := current;
od;

for j in [ 2 .. n-1] do
    for k in [ 1 .. n ] do
    for l in [ 1 .. n ] do
        if k <> l and IsEqualForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ),
             PreCompose( morphisms[j-1][l], morphisms[j][k] ) ) then
            morphisms[ j ][ l ] := -morphisms[ j ][ l ];
        elif k <> l and not IsEqualForMorphisms( PreCompose( morphisms[j-1][k], morphisms[j][l] ),
             -PreCompose( morphisms[j-1][l], morphisms[j][k] ) ) then
            Print( "unexpected!");
        fi;
    od;
    od;
od;

return morphisms;
end );

DeclareAttribute( "saleh", IsQuiverAlgebra );

InstallMethod( saleh, [ IsQuiverAlgebra ],
function( AQ )
local projectives, n;

projectives := Reversed( IndecProjRepresentations( AQ ) );
n := Length( projectives );
return List( [ 1 .. n - 1 ], i -> BasisOfHom( projectives[i], projectives[i+1] ) );
end );


DeclareOperation( "BasisBetweenCotangentBundles", [ IsQuiverAlgebra, IsInt, IsInt ] );
InstallMethodWithCache( BasisBetweenCotangentBundles, 
        "this should return the basis of Hom( p_i,p_j )",
        [ IsQuiverAlgebra, IsInt, IsInt ],
    function( AQ, i, j )
    local G, n, index, combinations, L, projectives;
    if i<j then
        return [ ];
    fi;
    
    projectives := Reversed( IndecProjRepresentations( AQ ) );

    n := Length( projectives );

    if i = j then
        return [ IdentityMorphism( projectives[ n - i ] ) ];
    fi;

    G := kamal( AQ );
    
    index := n - i;

    combinations := Combinations( [ 1 .. n ], i - j );
    combinations := List( combinations, comb -> Reversed( comb ) );
    L := List( combinations, comb -> List( [ 1 .. i - j ], k-> G[index+k-1][comb[k]] ) );
    return List( L, l -> PreCompose(l) );
end );

DeclareOperation( "BasisBetweenVectorBundles", [ IsQuiverAlgebra, IsInt, IsInt ] );
InstallMethodWithCache( BasisBetweenVectorBundles, 
        "this should return the basis of Hom( p_i,p_j )",
        [ IsQuiverAlgebra, IsInt, IsInt ],
    function( AQ, i, j )
    local n, L, source_index, range_index, d, indices, index, projectives;

    projectives := Reversed( IndecProjRepresentations( AQ ) );

    n := Length( projectives );

    if i >= 0 or j >= 0 or i < -n or j < -n then
        Error( "wrong input\n");
    fi;

    if i > j then
        return [ ];
    fi;

    source_index := Position( [ -n .. -1 ], i );
    range_index := Position( [ -n .. -1 ], j );

    if i = j then
        return [ IdentityMorphism( projectives[ source_index ] ) ];
    fi;
    
    L := saleh( AQ );

    d := range_index - source_index;

    indices := Cartesian( List( [ 1 .. d ], i -> [ 1 .. n ] ) );;
    for index in indices do
        Sort( index );
    od;

    indices := Set( indices );;

    return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], i -> L[i+source_index-1][index[i]]) ) );
end );

DeclareOperation( "BasisBetweenVectorBundles", [ IsHomalgGradedRing, IsQuiverAlgebra, IsInt, IsInt ] );
InstallMethodWithCache( BasisBetweenVectorBundles, 
        "this should return the basis of Hom( p_i,p_j )",
        [ IsHomalgGradedRing, IsQuiverAlgebra, IsInt, IsInt ],
    function( S, AQ, i, j )
    local n, L, source_index, range_index, d, indices, index, projectives, F, VB0, vector_bundles;

    if i <> 0 and j <> 0 then
        return BasisBetweenVectorBundles( AQ, i, j );
    fi;


    vector_bundles := Reversed( IndecProjRepresentations( AQ ) );

    n := Length( vector_bundles );

    F := FromVectorBundlesToVectorBundles( S, AQ );

    VB0 := ApplyFunctor( F, StandardVectorBundle( AQ, -1 ) );

    Add( vector_bundles, VB0 );

    if i > 0 or j > 0 or i < -n or j < -n then
        Error( "wrong input\n");
    fi;

    if i > j then
        return [ ];
    fi;

    source_index := Position( [ -n .. 0 ], i );
    range_index := Position( [ -n .. 0 ], j );

    if i = j then
        return [ IdentityMorphism( vector_bundles[ source_index ] ) ];
    fi;
    
    L := Concatenation( saleh( AQ ), [ BasisOfHom( vector_bundles[ n ], VB0 ) ] );

    d := range_index - source_index;

    indices := Cartesian( List( [ 1 .. d ], i -> [ 1 .. n ] ) );;
    for index in indices do
        Sort( index );
    od;

    indices := Set( indices );;
    
    return List( indices, index -> 
        PreCompose( List( [ 1 .. d ], i -> L[i+source_index-1][index[i]]) ) );
end );


KeyDependentOperation( "TwistedCotangentBundle", IsQuiverAlgebra, IsInt, ReturnTrue );
InstallMethod( TwistedCotangentBundleOp, [ IsQuiverAlgebra, IsInt ],
function( A, i )
    return Source( BasisBetweenCotangentBundles( A, i, i )[1] );
end );

KeyDependentOperation( "StandardVectorBundle", IsQuiverAlgebra, IsInt, ReturnTrue );
InstallMethod( StandardVectorBundleOp, [ IsQuiverAlgebra, IsInt ],
function( A, i )
    return Source( BasisBetweenVectorBundles( A, i, i )[1] );
end );

DeclareAttribute( "solve", IsQuiverRepresentationHomomorphism );
InstallMethod( solve, [ IsQuiverRepresentationHomomorphism ],
function( phi )
local position_of_1;

position_of_1 := Position( DimensionVector( Source( phi ) ), 1 );
return RowsOfMatrix( RightMatrixOfLinearTransformation( MapForVertex( phi, position_of_1 ) ) )[1];
end );



DeclareOperation( "morphism_between_projectives_cotangent_bundles", [ IsQuiverAlgebra, IsRecord ] );
InstallMethodWithCache( morphism_between_projectives_cotangent_bundles,
    [ IsQuiverAlgebra, IsRecord ],
function( AQ, record )
local cat, projectives, i, j, coefficients;

cat := CategoryOfQuiverRepresentations( AQ );
projectives := Concatenation( [ ZeroObject( cat ) ], IndecProjRepresentations( AQ ) );
i := record!.indices[ 1 ];
j := record!.indices[ 2 ];

if record!.coefficients = [] then
    return ZeroMorphism( projectives[ i + 2 ], projectives[ j + 2 ] );
else
    coefficients := List( record!.coefficients, c -> Rat( String( c ) ) );
    return coefficients*BasisBetweenCotangentBundles(AQ, i, j);
fi;

end );

DeclareOperation( "morphism_between_projectives_vector_bundles", [ IsQuiverAlgebra, IsRecord ] );
InstallMethodWithCache( morphism_between_projectives_vector_bundles,
    [ IsQuiverAlgebra, IsRecord ],
function( AQ, record )
local cat, projectives, i, j, coefficients;

cat := CategoryOfQuiverRepresentations( AQ );
projectives := Concatenation( IndecProjRepresentations( AQ ), [ ZeroObject( cat ) ]  );
i := record!.indices[ 1 ];
j := record!.indices[ 2 ];

if record!.coefficients = [] then
    return ZeroMorphism( projectives[ -i ], projectives[ -j ] );
else
    coefficients := List( record!.coefficients, c -> Rat( String( c ) ) );
    return coefficients*BasisBetweenVectorBundles(AQ, i, j);
fi;

end );


DeclareOperation( "ListOfRecordsToMorphism_Cotangents", [ IsQuiverAlgebra, IsList ] );
InstallMethod( ListOfRecordsToMorphism_Cotangents, [ IsQuiverAlgebra, IsList ],
function( AQ, L )
return MorphismBetweenDirectSums( List( L, l -> List( l, r -> morphism_between_projectives_cotangent_bundles( AQ, r ) ) ) ); 
end ); 

DeclareOperation( "ListOfRecordsToMorphism_Vectors", [ IsQuiverAlgebra, IsList ] );
InstallMethod( ListOfRecordsToMorphism_Vectors, [ IsQuiverAlgebra, IsList ],
function( AQ, L )
return MorphismBetweenDirectSums( List( L, l -> List( l, r -> morphism_between_projectives_vector_bundles( AQ, r ) ) ) ); 
end ); 


DeclareAttribute( "PartitionOfProjRep_Cotangent_Bundles", IsQuiverRepresentation );
InstallMethod( PartitionOfProjRep_Cotangent_Bundles, [ IsQuiverRepresentation ],
function( rep )
local AQ, indec_projectives, n, L, sol;
AQ := AlgebraOfRepresentation( rep );
indec_projectives := IndecProjRepresentations( AQ );
n := Length( indec_projectives );
L := List( indec_projectives, DimensionVector );
sol := SolutionIntMat( L, DimensionVector( rep ) );
if IsZero( sol ) then
    return [ ZeroObject( rep ) ];
else
    return Concatenation( List( [ 1 .. n ], i -> List( [ 1 .. sol[i] ], j-> indec_projectives[i] ) ) );
fi;
end );

DeclareAttribute( "PartitionOfProjRep_Vector_Bundles", IsQuiverRepresentation );
InstallMethod( PartitionOfProjRep_Vector_Bundles, [ IsQuiverRepresentation ],
function( M )
local n, projectives, L, i, j, indices, P, A, LM, positions, current_position;

if IsZeroForObjects( M ) then 
    return [ M ];
fi;

A := AlgebraOfRepresentation( M );
n := Length( IndecProjRepresentations( A ) );
projectives := List( [ 1 .. n ], i -> StandardVectorBundle( A, -i ) );
L := List( projectives, 
    p -> List( ColsOfMatrix( RightMatrixOfLinearTransformation( Sum( List( [ (n-2)*n+1 .. (n-1)*n ], 
    i -> MapForArrow( p, i ) ) ) ) ), 
                col -> Sum( col ) ) );
LM := List( ColsOfMatrix( RightMatrixOfLinearTransformation( Sum( List( [ (n-2)*n+1 .. (n-1)*n ], 
    i -> MapForArrow( M, i ) ) ) ) ), col -> Sum( col ) );

indices := [ ];
for i in [ 1 .. n ] do

    positions := [ ];
    while PositionSublist( LM, L[i] ) <> fail do
    current_position := PositionSublist( LM, L[i] );
    P := [ current_position .. current_position + Length( L[i] ) -1 ];
    for j in P do
        LM[ j ] := -i;
    od;
    Add( positions, current_position );
    od;
    indices := Concatenation( indices, Cartesian( [ i ], positions ) );
od;
Sort( indices, function(u,v) return u[2]<v[2]; end );
return List( indices, i -> projectives[ i[ 1 ] ] );
end );


DeclareAttribute( "PartitionOfProjRepMor_Cotangent_Bundles", IsQuiverRepresentationHomomorphism );
InstallMethod( PartitionOfProjRepMor_Cotangent_Bundles, [ IsQuiverRepresentationHomomorphism ],
function( phi )
local AQ, indec_projectives, source, range, i, j;
AQ := AlgebraOfRepresentation( Source( phi ) );
indec_projectives := Concatenation( [ ZeroObject( phi ) ], IndecProjRepresentations( AQ ) );

source := PartitionOfProjRep_Cotangent_Bundles( Source( phi ) );
range := PartitionOfProjRep_Cotangent_Bundles( Range( phi ) );

if Length( source ) = 1 and Length( range ) = 1 then
    i := Position( indec_projectives, source[ 1 ] ) - 2;
    j := Position( indec_projectives, range[ 1 ] ) - 2;

    if i=-1 or j = -1 then
        return [ [ rec( coefficients := [ ], indices := [ i, j ] ) ] ];
    else
        return [ [ rec( coefficients := solve( phi ), indices := [ i, j ] ) ] ];
    fi;
fi;

return List( [ 1 .. Length( source ) ], 
    i -> List( [ 1 .. Length( range ) ],
        j -> PartitionOfProjRepMor_Cotangent_Bundles( PreCompose(
            [
                InjectionOfCofactorOfDirectSum(source, i),
                phi,
                ProjectionInFactorOfDirectSum(range, j )
            ]
) )[1][1] ) );

end );

DeclareAttribute( "PartitionOfProjRepMor_Vector_Bundles", IsQuiverRepresentationHomomorphism );
InstallMethod( PartitionOfProjRepMor_Vector_Bundles, [ IsQuiverRepresentationHomomorphism ],
function( phi )
local AQ, indec_projectives, source, range, i, j, n;
AQ := AlgebraOfRepresentation( Source( phi ) );
indec_projectives := Concatenation( IndecProjRepresentations( AQ ), [ ZeroObject( phi ) ] );

n := Length( indec_projectives ) - 1;

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

return List( [ 1 .. Length( source ) ], 
    i -> List( [ 1 .. Length( range ) ],
        j -> PartitionOfProjRepMor_Vector_Bundles( PreCompose(
            [
                InjectionOfCofactorOfDirectSum(source, i),
                phi,
                ProjectionInFactorOfDirectSum(range, j )
            ]
) )[1][1] ) );

end );


DeclareOperation( "FromGradedLeftPresToQuiverRepsFunctor_CotangentBundles",
    [ IsHomalgGradedRing, IsQuiverAlgebra ] );
InstallMethodWithCache( FromGradedLeftPresToQuiverRepsFunctor_CotangentBundles,
    [ IsHomalgGradedRing, IsQuiverAlgebra ],
    function( S, AQ )
    local quiver_representations, graded_lp_cat_sym, F;
    quiver_representations := CategoryOfQuiverRepresentations( AQ );
    graded_lp_cat_sym := GradedLeftPresentations( S );

    F := CapFunctor( "From graded lp cat to quiver representations functor (cotangent bundles)", graded_lp_cat_sym, quiver_representations );
    AddObjectFunction( F, 
        function( M )
        local u;
        u := UniversalMorphismIntoZeroObject( M );
        u := ListOfRecordsToMorphism_Cotangents( AQ, MorphismToListOfRecords_Cotangents( u) );
        return Source( u );
    end );

    AddMorphismFunction( F, 
        function( source, phi, range )
        return ListOfRecordsToMorphism_Cotangents( AQ, MorphismToListOfRecords_Cotangents( phi ) );
    end );
    
    return F;
end );


DeclareOperation( "FromGradedLeftPresToQuiverRepsFunctor_VectorBundles",
    [ IsHomalgGradedRing, IsQuiverAlgebra ] );
InstallMethodWithCache( FromGradedLeftPresToQuiverRepsFunctor_VectorBundles,
    [ IsHomalgGradedRing, IsQuiverAlgebra ],
    function( S, AQ )
    local quiver_representations, graded_lp_cat_sym, F;
    quiver_representations := CategoryOfQuiverRepresentations( AQ );
    graded_lp_cat_sym := GradedLeftPresentations( S );

    F := CapFunctor( "From graded lp cat to quiver representations functor (vector bundles)", graded_lp_cat_sym, quiver_representations );
    AddObjectFunction( F, 
        function( M )
        local u;
        u := UniversalMorphismIntoZeroObject( M );
        u := ListOfRecordsToMorphism_Vectors( AQ, MorphismToListOfRecords_VectorBundles( u) );
        return Source( u );
    end );

    AddMorphismFunction( F, 
        function( source, phi, range )
        return ListOfRecordsToMorphism_Vectors( AQ, MorphismToListOfRecords_VectorBundles( phi ) );
    end );
    
    return F;
end );

DeclareOperation( "FromQuiverRepsToGradedLeftPresFunctor_CotangentBundles",
    [ IsQuiverAlgebra, IsHomalgGradedRing ] );
InstallMethodWithCache( FromQuiverRepsToGradedLeftPresFunctor_CotangentBundles,
    [ IsQuiverAlgebra, IsHomalgGradedRing ],
    function( AQ, S )
    local quiver_representations, graded_lp_cat_sym, F;
    quiver_representations := CategoryOfQuiverRepresentations( AQ );
    graded_lp_cat_sym := GradedLeftPresentations( S );

    F := CapFunctor( "From to quiver representations to graded lp cat functor", 
        quiver_representations, graded_lp_cat_sym );
    AddObjectFunction( F, 
        function( rep )
        local u;
        u := UniversalMorphismIntoZeroObject( rep );
        u := ListOfRecordsToMorphism_Cotangents( S, PartitionOfProjRepMor_Cotangent_Bundles( u ) );
        return Source( u );
    end );

    AddMorphismFunction( F, 
        function( source, phi, range )
        return ListOfRecordsToMorphism_Cotangents( S, PartitionOfProjRepMor_Cotangent_Bundles( phi ) );
    end );
    
    return F;
end );

DeclareOperation( "FromQuiverRepsToGradedLeftPresFunctor_VectorBundles",
    [ IsQuiverAlgebra, IsHomalgGradedRing ] );
InstallMethodWithCache( FromQuiverRepsToGradedLeftPresFunctor_VectorBundles,
    [ IsQuiverAlgebra, IsHomalgGradedRing ],
    function( AQ, S )
    local quiver_representations, graded_lp_cat_sym, F;
    quiver_representations := CategoryOfQuiverRepresentations( AQ );
    graded_lp_cat_sym := GradedLeftPresentations( S );

    F := CapFunctor( "From to quiver representations to graded lp cat functor", 
        quiver_representations, graded_lp_cat_sym );
    AddObjectFunction( F, 
        function( rep )
        local u;
        u := UniversalMorphismIntoZeroObject( rep );
        u := ListOfRecordsToMorphism_Vectors( S, PartitionOfProjRepMor_Vector_Bundles( u ) );
        return Source( u );
    end );

    AddMorphismFunction( F, 
        function( source, phi, range )
        return ListOfRecordsToMorphism_Vectors( S, PartitionOfProjRepMor_Vector_Bundles( phi ) );
    end );
    
    return F;
end );


computing_lift_second_method := function( alpha, beta )
local S, R, A, Q, field, S_dimensions, R_dimensions, nr_cols_in_block1, nr_cols_in_block3,
nr_cols_in_block5, nr_of_vertices, nr_of_arrows, nr_rows_of_block, mat, L, vector,
block_1, block_2, block_3, block_4, block_5, block, i, u, v, matrices, cols, Id, id_1, id_2,
source_of_arrow, range_of_arrow, alpha_i, beta_i, S_i, R_i, Vec;

S := Source( alpha );
R := Source( beta );

A := AlgebraOfRepresentation( S );
Q := QuiverOfAlgebra( A );

field := LeftActingDomain( A );

Vec := function( M )
    return MatrixByCols( field, [ Product( DimensionsMat( M ) ), 1 ], [ Concatenation( ColsOfMatrix( M ) ) ] );
end;

S_dimensions := DimensionVector( S );
R_dimensions := DimensionVector( R );

nr_of_vertices := Length( S_dimensions );

mat := MatrixByRows( field, [ 0, S_dimensions*R_dimensions + 1 ], [] );

for i in [ 1 .. nr_of_vertices ] do
    beta_i := RightMatrixOfLinearTransformation( MapForVertex( beta, i ) );
    alpha_i := RightMatrixOfLinearTransformation( MapForVertex( alpha, i ) );
    Id := IdentityMatrix( field, S_dimensions[i] );

    nr_rows_of_block := Product( DimensionsMat( alpha_i ) );

    if i in [ 2 .. nr_of_vertices ] then
        nr_cols_in_block1 := S_dimensions{[1..i-1]}*R_dimensions{[1..i-1]};
    else
        nr_cols_in_block1 := 0;
    fi;
    block_1 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block1 );
    
    block_2 := KroneckerProduct( TransposedMat( beta_i ), Id );

    if i in [ 1 .. nr_of_vertices - 1 ] then
        nr_cols_in_block3 := S_dimensions{ [ i+1..nr_of_vertices ] } * R_dimensions{ [ i+1..nr_of_vertices ] };
    else
        nr_cols_in_block3 := 0;
    fi;
    block_3 := MakeZeroMatrix( field, nr_rows_of_block, nr_cols_in_block3);
    
    block := StackMatricesHorizontally( [ block_1, block_2, block_3, Vec( alpha_i ) ] );

    mat := StackMatricesVertically( mat, block );
od;

nr_of_arrows := NumberOfArrows( Q );

for i in [ 1 .. nr_of_arrows ] do

    source_of_arrow := VertexNumber( Source( Arrow( Q, i ) ) );
    range_of_arrow := VertexNumber( Target( Arrow( Q, i ) ) );

    S_i := RightMatrixOfLinearTransformation( MapForArrow( S, i ) );
    R_i := RightMatrixOfLinearTransformation( MapForArrow( R, i ) );

    id_1 := IdentityMatrix( field, DimensionsMat( S_i )[ 1 ] );
    id_2 := IdentityMatrix( field, DimensionsMat( R_i )[ 2 ] );

    nr_rows_of_block := DimensionsMat( S_i )[ 1 ]*DimensionsMat( R_i )[ 2 ];

    u := Minimum( source_of_arrow, range_of_arrow );
    v := Maximum( source_of_arrow, range_of_arrow );

    if u = 1 then
        nr_cols_in_block1 := 0;
    else
        nr_cols_in_block1 := S_dimensions{[1..u-1]}*R_dimensions{[1..u-1]};
    fi;

    block_1 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block1 );

    if u = source_of_arrow then
        block_2 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
    elif u = range_of_arrow then
        block_2 := KroneckerProduct( id_2, S_i );
    fi;

    if v-u in [ 0, 1 ] then
        nr_cols_in_block3 := 0;
    else
        nr_cols_in_block3 := S_dimensions{[u+1..v-1]}*R_dimensions{[u+1..v-1]};
    fi;

    block_3 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block3 );

    if v = source_of_arrow then
        block_4 := -KroneckerProduct( TransposedMat( R_i ), id_1 );
    elif v = range_of_arrow then
        block_4 := KroneckerProduct( id_2, S_i );
    fi;

    if v = nr_of_vertices then
        nr_cols_in_block5 := 0;
    else
        nr_cols_in_block5 := S_dimensions{[v+1..nr_of_vertices]}*R_dimensions{[v+1..nr_of_vertices]};
    fi;

    block_5 := MakeZeroMatrix( field, nr_rows_of_block,  nr_cols_in_block5 + 1 );

    block := StackMatricesHorizontally( [ block_1, block_2, block_3, block_4, block_5 ] );

    mat := StackMatricesVertically( mat, block );
od;

cols := ShallowCopy( ColsOfMatrix( mat ) );
vector := StandardVector( Rationals, cols[Length(cols)] );
mat := MatrixByRows( Rationals, cols{[1..Length(cols)-1]} );
mat := SolutionMat( mat, vector );

if mat = fail then
    return fail;
fi;

L := ShallowCopy( AsList( mat ) );
matrices := [ ];
for i in [ 1 .. nr_of_vertices ] do
    mat := L{[1..S_dimensions[i]*R_dimensions[i]]};
    Add( matrices, MatrixByCols( field, [ S_dimensions[i], R_dimensions[i] ], mat ) );
    L := L{[S_dimensions[i]*R_dimensions[i]+1 .. Length( L ) ]};
od;

return QuiverRepresentationHomomorphism( S, R, matrices );

end;




