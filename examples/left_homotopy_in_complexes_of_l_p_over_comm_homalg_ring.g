LoadPackage( "ModulePresentation" );
LoadPackage( "RingsForHomalg" );
LoadPackage( "ComplexesForCAP" );

############### computing homotopy ###########################

Compute_Homotopy := 
  function( phi, s, n )
  local A, B, ring, r, mat, j, k, l,i, current_mat, t, b, current_b, list, var, sol, union_of_columns, union_of_rows;

  A := Source( phi );

  B := Range( phi );

  ring := HomalgRing( UnderlyingMatrix( phi [ s ] ) );

    if not HasIsCommutative( ring ) then 
        Error( "The underlying computable ring is not known to be commutative" );
    elif HasIsCommutative( ring ) and not IsCommutative( ring ) then 
        Error( "The underlying computable ring must be commutative" );
    fi;
    
  # Here we find which variables should be actually compute. h_i, x_i or y_i.

  var := [ ];

  for j in [ s + 1 .. n ] do 

    t := NrColumns( UnderlyingMatrix( A[ j ] ) )*NrColumns( UnderlyingMatrix( B[ j -1 ] ) );

    if t<>0 then Add( var, [ "h",j, [ NrColumns( UnderlyingMatrix( B[ j -1 ] ) ), NrColumns( UnderlyingMatrix( A[ j ] ) )  ] ] );fi;

  od;

  for k in [ s .. n ] do

    t := NrRows( UnderlyingMatrix( phi[ k ] ) )* NrRows( UnderlyingMatrix( B[ k ] ) );

    if t<>0 then Add( var, [ "x", k, [ NrRows( UnderlyingMatrix( phi[ k ] ) ), NrRows( UnderlyingMatrix( B[ k ] ) )  ] ] );fi;

  od;

  for l in [ s .. n - 1 ] do

    t := NrRows( UnderlyingMatrix( A[ l + 1 ] ) )*NrRows( UnderlyingMatrix( B[ l ] ) );

    if t<>0 then Add( var, [ "y", l, [ NrRows( UnderlyingMatrix( A[ l + 1 ] ) ), NrRows( UnderlyingMatrix( B[ l ] ) )  ] ] );fi;

  od;

  # the first equation
  mat := 0;
  b := 0;

  union_of_columns := function( m, n )
                      local new_m;
                      new_m := m;
                      if m=0 then new_m := HomalgZeroMatrix( NrRows( n ), 0, ring );fi;
                      return UnionOfColumns( new_m, n );
                      end;

  union_of_rows := function( m, n )
                      local new_m;
                      new_m := m;
                      if m=0 then new_m := HomalgZeroMatrix( 0, NrColumns( n ), ring );fi;
                      return UnionOfRows( new_m, n );
                      end;

  r := NrColumns( UnderlyingMatrix( phi[ s ] ) )* NrRows( UnderlyingMatrix( phi[ s ] ) );

  if r<>0 then

  list := List( [ 1 .. NrColumns( UnderlyingMatrix( phi[ s ] ) ) ], c -> CertainColumns( UnderlyingMatrix( phi[ s ] ), [ c ] ) );

  if Length( list ) = 1 then 
     b := list[ 1 ];
  else
     b := Iterated( list, UnionOfRows );
  fi;

  mat := HomalgZeroMatrix( r, 0, ring );

  for j in [ s + 1 .. n ] do

    t := NrColumns( UnderlyingMatrix( A[ j ] ) )*NrColumns( UnderlyingMatrix( B[ j -1 ] ) );

    if j = s + 1 and t <>0 then

       mat := union_of_columns( mat, KroneckerMat( HomalgIdentityMatrix( NrColumns( UnderlyingMatrix( phi[ s ] ) ), ring ), UnderlyingMatrix( A^s ) ) );

    elif t <> 0 then 

       mat := union_of_columns( mat, HomalgZeroMatrix( r, t, ring ) );

    fi;

  od;


  for k in [ s .. n ] do 

    t := NrRows( UnderlyingMatrix( phi[ k ] ) )* NrRows( UnderlyingMatrix( B[ k ] ) );

    if k = s and t<>0 then 

    mat := union_of_columns( mat, KroneckerMat( Involution( UnderlyingMatrix( B[ s ] ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( phi[ s ] ) ), ring ) ) );
    elif t<>0 then

    mat := union_of_columns( mat, HomalgZeroMatrix( r, t, ring ) );
    fi;

  od;

  for l in [ s .. n - 1 ] do 
    t := NrRows( UnderlyingMatrix( A[ l + 1 ] ) )*NrRows( UnderlyingMatrix( B[ l ] ) );
    if t<>0 then
    mat := union_of_columns( mat, HomalgZeroMatrix( r, t, ring ) );
    fi;
  od;

  fi;

  for i in [ s + 1 .. n - 1 ] do

      r := NrColumns( UnderlyingMatrix( phi[ i ] ) )* NrRows( UnderlyingMatrix( phi[ i ] ) );

      if r <> 0 then 

         list := List( [ 1 .. NrColumns( UnderlyingMatrix( phi[ i ] ) ) ], c -> CertainColumns( UnderlyingMatrix( phi[ i ] ), [ c ] ) );
         if Length( list ) = 1 then 
            current_b := list[ 1 ];
         else
            current_b := Iterated( list, UnionOfRows );
         fi;

      current_mat := HomalgZeroMatrix( r, 0, ring );

      for j in [ s + 1 .. n ] do

          t := NrColumns( UnderlyingMatrix( A[ j ] ) )*NrColumns( UnderlyingMatrix( B[ j - 1 ] ) );

          if j = i and t<>0 then

             current_mat := UnionOfColumns( current_mat, KroneckerMat( Involution( UnderlyingMatrix( B^(i - 1) ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( phi[ i ] ) ), ring ) ) );
          elif j = i + 1 and t<>0 then

             current_mat := UnionOfColumns( current_mat, KroneckerMat( HomalgIdentityMatrix( NrColumns( UnderlyingMatrix( phi[ i ] ) ), ring ), UnderlyingMatrix( A^i ) ) );
          elif t<>0 then

             current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
          fi; 
      od;


      for k in [ s .. n ] do 

          t := NrRows( UnderlyingMatrix( phi[ k ] ) )* NrRows( UnderlyingMatrix( B[ k ] ) );

          if k = i and t<>0 then 

             current_mat := UnionOfColumns( current_mat, KroneckerMat( Involution( UnderlyingMatrix( B[ i ] ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( phi[ i ] ) ), ring ) ) );
          elif t<>0 then

             current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
          fi;

      od;

     for l in [ s .. n - 1 ] do 
         t := NrRows( UnderlyingMatrix( A[ l + 1 ] ) )*NrRows( UnderlyingMatrix( B[ l ] ) );
         if t<>0 then
         current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
         fi;
     od;

  if not IsZero( current_mat ) then  mat := union_of_rows( mat, current_mat ); b := union_of_rows( b, current_b ); fi;

  fi;

  od;

  #again for the last non-zero morphism

  r := NrColumns( UnderlyingMatrix( phi[ n ] ) )* NrRows( UnderlyingMatrix( phi[ n ] ) );

  if r<>0 then 

         list :=  List( [ 1 .. NrColumns( UnderlyingMatrix( phi[ n ] ) ) ], c -> CertainColumns( UnderlyingMatrix( phi[ n ] ), [ c ] ) );
         if Length( list ) = 1 then 
            current_b := list[ 1 ];
         else
            current_b := Iterated( list, UnionOfRows );
         fi;

  current_mat := HomalgZeroMatrix( r, 0, ring );

  for j in [ s + 1 .. n ] do

    t := NrColumns( UnderlyingMatrix( A[ j ] ) )*NrColumns( UnderlyingMatrix( B[ j -1 ] ) );

    if j = n and t<>0 then

       current_mat := UnionOfColumns( current_mat, KroneckerMat( Involution( UnderlyingMatrix( B^(n-1) ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( phi[ n ] ) ), ring ) ) );
    elif t<> 0 then

       current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
    fi;

  od;


  for k in [ s .. n ] do 

    t := NrRows( UnderlyingMatrix( phi[ k ] ) )* NrRows( UnderlyingMatrix( B[ k ] ) );

    if k = n and t<>0 then 

    current_mat := UnionOfColumns( current_mat, KroneckerMat( Involution( UnderlyingMatrix( B[ n ] ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( phi[ n ] ) ), ring ) ) );
    elif t<>0 then

    current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
    fi;

  od;

  for l in [ s .. n - 1 ] do 
         t := NrRows( UnderlyingMatrix( A[ l + 1 ] ) )*NrRows( UnderlyingMatrix( B[ l ] ) );
         if t<>0 then
         current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
         fi; 
  od;

  if not IsZero( current_mat ) then  mat := union_of_rows( mat, current_mat ); b := union_of_rows( b, current_b ); fi;

  fi;

  # Now the equations that make sure that the maps h_i's are well defined

  for i in [ s .. n - 1 ] do

    r := NrRows( UnderlyingMatrix( A[ i + 1 ] ) ) * NrColumns( UnderlyingMatrix( B[ i ] ) );

    if r <> 0 then

    current_mat := HomalgZeroMatrix( r, 0, ring );

    for j in [ s + 1 .. n ] do 

      t := NrColumns( UnderlyingMatrix( A[ j ] ) )*NrColumns( UnderlyingMatrix( B[ j -1 ] ) );
      if j = i + 1 and t<>0 then 

        current_mat := UnionOfColumns( current_mat, KroneckerMat( HomalgIdentityMatrix( NrColumns( UnderlyingMatrix( B[ i ] ) ), ring ), UnderlyingMatrix( A[ i + 1 ] ) ) );
      elif t<>0 then

        current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
      fi;

    od;

    for k in [ s .. n ] do 
    t :=  NrRows( UnderlyingMatrix( phi[ k ] ) )* NrRows( UnderlyingMatrix( B[ k ] ) );
    if t<> 0 then 
    current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
    fi;
    od;

    for l in [ s .. n - 1 ] do
        t := NrRows( UnderlyingMatrix( A[ l + 1 ] ) )*NrRows( UnderlyingMatrix( B[ l ] ) );
        if l = i and t<>0 then

           current_mat := UnionOfColumns( current_mat, KroneckerMat( Involution( UnderlyingMatrix( B[ i ] ) ), HomalgIdentityMatrix( NrRows( UnderlyingMatrix( A[ i + 1 ] ) ), ring ) ) );
        elif t<>0 then

           current_mat := UnionOfColumns( current_mat, HomalgZeroMatrix( r, t, ring ) );
        fi;

    od;

  current_b := HomalgZeroMatrix( r, 1, ring );

  if not IsZero( current_mat ) then  mat := union_of_rows( mat, current_mat ); b := union_of_rows( b, current_b ); fi;

  fi;

  od;

sol := LeftDivide(mat, b);

if sol = fail then 
   return [ false, sol, mat, b, var ];
else 
   return [ true, sol, mat, b, var ]; 
fi;

end;

compute_left_homotopy_in_left_presentations := function( phi, m, n )
local cat, underlying_cat, T, psi, sol, new_var;

cat := CapCategory( phi );

underlying_cat := UnderlyingCategory( cat );

if IsCochainComplexCategory( cat ) then 

   return Compute_Homotopy( phi, m, n );

elif IsChainComplexCategory( cat ) then 

   T := ChainToCochainComplexFunctor( ChainComplexCategory( underlying_cat ), CochainComplexCategory( underlying_cat )  );

   psi := ApplyFunctor( T, phi );

   sol := ShallowCopy( compute_left_homotopy_in_left_presentations( psi, -n, -m ) );

   new_var := sol[ 5 ];

   new_var := List( new_var, i-> [ i[1],-i[2], i[3] ] );

   sol[ 5 ] := new_var;

   return sol;

fi;

end;

is_left_homotopic_to_null :=
   function( mor )
   local S, R, m, n;

   S := Source( mor );

   R := Range( mor );

   if not IsBoundedChainOrCochainComplex( S ) or not IsBoundedChainOrCochainComplex( R ) then 

      Error( "Both source and range must be bounded complexes" );

   fi;

   m := Minimum( ActiveLowerBound( S ), ActiveLowerBound( R ) );

   n := Maximum( ActiveUpperBound( S ), ActiveUpperBound( R ) );

   return compute_left_homotopy_in_left_presentations( mor, m, n )[ 1 ];

end;

##
compute_lifts_in_chains := 
	function( alpha, beta )
	  local cat, U, P, N, M, alpha_, beta_, internal_hom_P_M, internal_hom_P_N, internal_hom_id_P_beta, k_internal_hom_id_P_beta_0, alpha_1, lift;
	  cat := CapCategory( alpha );
	  U := TensorUnit( cat );
	  P := Source( alpha );
	  N := Range( alpha );
	  M := Source( beta );

	  alpha_ := TensorProductToInternalHomAdjunctionMap( U, Source( alpha ), alpha );
	  beta_  := TensorProductToInternalHomAdjunctionMap( U, Source( beta ), beta );

	  internal_hom_id_P_beta := InternalHomOnMorphisms( IdentityMorphism( P ), beta );
	  internal_hom_P_M := Source( internal_hom_id_P_beta );
	  internal_hom_P_N := Range( internal_hom_id_P_beta );

	  k_internal_hom_id_P_beta_0 := KernelLift( internal_hom_P_N^0,
	  	PreCompose( CyclesAt( internal_hom_P_M, 0 ), internal_hom_id_P_beta[ 0 ]  ) );
	  
	  alpha_1 := KernelLift( internal_hom_P_N^0, alpha_[0] );

	  lift := Lift( alpha_1, k_internal_hom_id_P_beta_0 );
	  
	  if lift = fail then
	    	return fail;
	  else

	  	lift := ChainMorphism( U, internal_hom_P_M, [ PreCompose( lift, CyclesAt( internal_hom_P_M, 0 ) ) ], 0 );

	  	return InternalHomToTensorProductAdjunctionMap( P, M, lift );
	  fi;
end;

compute_lifts_in_cochains := 
        function( alpha, beta )
        local cochains_cat, chains_cat, cat, cochains_to_chains, chains_to_cochains, l;
        cochains_cat := CapCategory( alpha );
        cat := UnderlyingCategory( cochains_cat );
        chains_cat := ChainComplexCategory( cat );
        cochains_to_chains := CochainToChainComplexFunctor( cochains_cat, chains_cat );
        chains_to_cochains := ChainToCochainComplexFunctor( chains_cat, cochains_cat );
        l := compute_lifts_in_chains( ApplyFunctor( cochains_to_chains, alpha ), ApplyFunctor( cochains_to_chains, beta ) );
        return ApplyFunctor( chains_to_cochains, l );
end;

compute_colifts_in_chains := 
	function( alpha, beta )
	  local cat, U, P, N, M, alpha_, beta_, internal_hom_P_M, internal_hom_N_M, internal_hom_alpha_id_M, k_internal_hom_alpha_id_M_0, beta_1, lift;
	  cat := CapCategory( alpha );
	  U := TensorUnit( cat );
	  P := Range( alpha );
	  N := Source( alpha );
	  M := Range( beta );

	  alpha_ := TensorProductToInternalHomAdjunctionMap( U, Source( alpha ), alpha );
	  beta_  := TensorProductToInternalHomAdjunctionMap( U, Source( beta ), beta );

	  internal_hom_alpha_id_M := InternalHomOnMorphisms( alpha, IdentityMorphism( M ) );
	  internal_hom_P_M := Source( internal_hom_alpha_id_M );
	  internal_hom_N_M := Range( internal_hom_alpha_id_M );

	  k_internal_hom_alpha_id_M_0 := KernelLift( internal_hom_N_M^0,
	  	PreCompose( CyclesAt( internal_hom_P_M, 0 ), internal_hom_alpha_id_M[ 0 ]  ) );
	  
	  beta_1 := KernelLift( internal_hom_N_M^0, beta_[0] );

	  lift := Lift( beta_1, k_internal_hom_alpha_id_M_0 );

	  if lift = fail then
	  	return fail;
	  else  
                lift := ChainMorphism( U, internal_hom_P_M, [ PreCompose( lift, CyclesAt( internal_hom_P_M, 0 ) ) ], 0 );

	  	return InternalHomToTensorProductAdjunctionMap( P, M, lift );
	  fi;

end;

compute_colifts_in_cochains := 
        function( alpha, beta )
        local cochains_cat, chains_cat, cat, cochains_to_chains, chains_to_cochains, l;
        cochains_cat := CapCategory( alpha );
        cat := UnderlyingCategory( cochains_cat );
        chains_cat := ChainComplexCategory( cat );
        cochains_to_chains := CochainToChainComplexFunctor( cochains_cat, chains_cat );
        chains_to_cochains := ChainToCochainComplexFunctor( chains_cat, cochains_cat );
        l := compute_colifts_in_chains( ApplyFunctor( cochains_to_chains, alpha ), ApplyFunctor( cochains_to_chains, beta ) );
        return ApplyFunctor( chains_to_cochains, l );
end;

generators_of_hom_for_chains := 
    function( C, D )
    local chains, H, kernel_mor_of_H, kernel_obj_of_H, morphisms_C_to_D, morphisms_from_R_to_kernel, morphisms_from_T_to_H, T;
    chains := CapCategory( C );
    H := InternalHomOnObjects( C, D );
    kernel_mor_of_H := CyclesAt( H, 0 );
    kernel_obj_of_H := Source( kernel_mor_of_H );
    morphisms_from_R_to_kernel := List( [ 1 .. NrColumns( UnderlyingMatrix( kernel_obj_of_H ) ) ], i-> StandardGeneratorMorphism( kernel_obj_of_H, i ) );;
    T := TensorUnit( chains );
    morphisms_from_T_to_H := List( morphisms_from_R_to_kernel, m -> ChainMorphism( T, H, [ PreCompose( m, kernel_mor_of_H) ], 0 ) );
    return List( morphisms_from_T_to_H, m-> InternalHomToTensorProductAdjunctionMap( C, D, m ) );
end;

generators_of_hom_for_cochains := 
        function( C, D )
        local cochains_cat, chains_cat, cat, cochains_to_chains, chains_to_cochains, l, m;
        cochains_cat := CapCategory( C );
        cat := UnderlyingCategory( cochains_cat );
        chains_cat := ChainComplexCategory( cat );
        cochains_to_chains := CochainToChainComplexFunctor( cochains_cat, chains_cat );
        chains_to_cochains := ChainToCochainComplexFunctor( chains_cat, cochains_cat );
        l := generators_of_hom_for_chains( ApplyFunctor( cochains_to_chains, C ), ApplyFunctor( cochains_to_chains, D ) );
        return List( l, m -> ApplyFunctor( chains_to_cochains, m ) );
end;

compute_homotopy_chain_morphisms_for_null_homotopic_morphism := 
    function( f )
    local B, C, colift;
    if not IsNullHomotopic( f ) then
        return fail;
    fi;
    B := Source( f );
    C := Range( f );
    colift := Colift( NaturalInjectionInMappingCone( IdentityMorphism( Source( f ) ) ), f );
    if colift = fail then 
      return fail;
    else
      return MapLazy( IntegersList, 
      		n -> PreCompose( 
		MorphismBetweenDirectSums( [ [ IdentityMorphism( B[ n ] ), ZeroMorphism( B[ n ], B[ n + 1 ] ) ] ] ),
		colift[ n + 1 ] ), 1 );
    fi;
    # Here: l[n]: B[n] --> C[n+1], n in Z.
end;

compute_homotopy_cochain_morphisms_for_null_homotopic_morphism := 
        function( f )
        local cochains_cat, chains_cat, cat, cochains_to_chains, list;
        cochains_cat := CapCategory( f );
        cat := UnderlyingCategory( cochains_cat );
        chains_cat := ChainComplexCategory( cat );
        cochains_to_chains := CochainToChainComplexFunctor( cochains_cat, chains_cat );
        list := compute_homotopy_chain_morphisms_for_null_homotopic_morphism( ApplyFunctor( cochains_to_chains, f ) );
        if list = fail then
            return fail;
        else
            return MapLazy( IntegersList, n -> list[ -n ], 1 );
        fi;
end;
