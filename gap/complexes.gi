

BindGlobal( "ModelStructureOnChainComplexes",
 function( cat )
 
 SetIsModelCategory( cat, true );
 
 AddIsWeakEquivalence( cat, 
    function( phi )
      return IsQuasiIsomorphism( phi );
    end );
 
 ### Fix this
 AddIsCofibration( cat, 
    function( phi )
    local i, A, B;
    
    A := Source( phi );
      
    B := Range( phi );
      
    if not IsBoundedChainComplex( A ) and IsBoundedChainComplex( B ) then 

        Error( "Both source and range must be bounded" );
        
    fi;
        
      
    for i in [ Minimum( ActiveLowerBound( A ), ActiveLowerBound( B ) ) .. Maximum( ActiveUpperBound( A ), ActiveUpperBound( B ) ) ] do 
          
        if not IsMonomorphism( phi[ i ] ) then 
          
            return false;
             
        fi;
          
        if not IsProjective( CokernelObject( phi[ i ] ) ) then
             
             
            return false;
             
        fi;
          
      od;
      
      return true;
      
      end );
    
  AddIsFibration( cat, 
    function( phi )
    local i, A, B;
    
    A := Source( phi );
      
    B := Range( phi );
      
    if not IsBoundedChainComplex( A ) and IsBoundedChainComplex( B ) then 

        Error( "Both source and range must be bounded" );
        
    fi;
    
    for i in [ Minimum( ActiveLowerBound( A ), ActiveLowerBound( B ) ) .. Maximum( ActiveUpperBound( A ), ActiveUpperBound( B ) ) ] do 
        
        if not IsEpimorphism( phi[ i ] ) then 
            
            return false;
               
        fi;
            
    od;
        
        return true;
        
        end );

# This can be derived, but it will be faster to state it here.
AddIsFibrant( cat, 
    function( obj )
        return true;
    end );

# This can be derived, but it will be faster to state it here.
AddAcyclicCofibrationIntoFibrantModel( cat, 
    function( obj )
        return IdentityMorphism( obj );
    end );

# This can be derived, but it will be faster to state it here.
AddFibrantModel( cat, 
    function( obj )
        return obj;
    end );
    
# This can be derived, but it will be faster to state it here.
AddMorphismBetweenFibrantModels( cat, 
    function( mor )
        return mor;
    end );
    


# See Homotopy theories and model categories of Dwyer and Spakinski.      
AddLifting( cat,
    function( f, g, u, v )
    local l, A, B, P, splitting_morphism, direct_sum_to_B, direct_sum_to_X, B_to_direct_sum, X;
     
    if HasIsCofibration( f ) and HasIsAcyclicFibration( g ) and IsCofibration( f ) and IsAcyclicFibration( g ) then
    l := MapLazy( IntegersList, 
     
        function( i )
        local A, B, P, splitting_morphism, direct_sum_to_B, direct_sum_to_X, B_to_direct_sum, t, K, epsilon, X;
        
	if i < Minimum( ActiveLowerBound( Range( f ) ), ActiveLowerBound( Source( g ) ) ) then 
	   return ZeroMorphism( Range( f )[ i ], Source( g )[ i ] );
        fi;
        
        A := Source( f )[ i ];
               
        B := Range( f )[ i ];
        
        X := Source( g );
        
        K := KernelObject( g );
               
        P := CokernelObject( f[ i ] );
               
        splitting_morphism := ProjectiveLift( IdentityMorphism( P ), CokernelProjection( f[ i ] ) );
               
        direct_sum_to_B := UniversalMorphismFromDirectSum( [ A, P ], [ f[ i ], splitting_morphism ] );
               
        B_to_direct_sum := Inverse( direct_sum_to_B );
               
        direct_sum_to_X := MorphismBetweenDirectSums( [ [ u[ i ] ], [ ProjectiveLift( PreCompose( splitting_morphism, v[ i ] ), g[ i ] ) ] ] );
  
        t := PreCompose( B_to_direct_sum, direct_sum_to_X );
        
        if i = 0 then return t; fi;
        
        epsilon := PreCompose( t, X^i ) - PreCompose( Range( f )^i, l[ i - 1 ] );
        
        epsilon := KernelLift( K^( i - 1 ), KernelLift( g[ i - 1 ], CokernelColift( f[ i ], epsilon ) ) );
        
        epsilon := ProjectiveLift( epsilon, KernelLift( K^(i-1), K^i ) );
        
        return t - PreCompose( [ CokernelProjection( f[ i ] ), epsilon, KernelEmbedding( g )[ i ] ] );
        
        end, 1 );
        
        return ChainMorphism( Range( f ), Source( g ), l );
       
    fi;
    
    if HasIsAcyclicCofibration( f ) and HasIsFibration( g ) and IsAcyclicCofibration( f ) and IsFibration( g ) then
    
        A := Source( f );
               
        B := Range( f );
        
        P := CokernelObject( f );
        
        splitting_morphism := ProjectiveLift( IdentityMorphism( P ), CokernelProjection( f ) );
        
        direct_sum_to_B := UniversalMorphismFromDirectSum( [ A, P ], [ f, splitting_morphism ] );
        
        B_to_direct_sum := Inverse( direct_sum_to_B );
        
        direct_sum_to_X := MorphismBetweenDirectSums( [ [ u ], [ ProjectiveLift( PreCompose( splitting_morphism, v ), g ) ] ] );
        
        return PreCompose( B_to_direct_sum, direct_sum_to_X );
    fi;
    
    Error( "The first argument should be an acyclic cofibration the second a fibration or the first is cofibration and the second is acyclic fibration" );
    
    end );
    
    AddFactorThroughAcyclicFibration( cat, 
      function( f )
      local A, B, cyl_f_to_B, cyl_f_to_cone_f, P_to_cone_f, P, A_to_cyl_f, i, Q_to_cyl_f, j;
      
      A := Source( f );
      
      B := Range( f );
      
      cyl_f_to_B := NaturalMorphismFromMappingCylinderInRange( f );
      
      cyl_f_to_cone_f := NaturalMorphismFromMappingCylinderInMappingCone( f );
      
      ## Here we need the upper bound of the projective resolution, hence we try the first 5000 indeces
      P := ProjectiveResolutionWithBounds( MappingCone( f ), 5000 );
      
      P_to_cone_f := QuasiIsomorphismFromProjectiveResolution( MappingCone( f ) );
      
      A_to_cyl_f := NaturalInjectionOfSourceInMappingCylinder( f );
      
      ##
      i := UniversalMorphismIntoFiberProduct( [ cyl_f_to_cone_f, P_to_cone_f ], [ A_to_cyl_f, ZeroMorphism( A, P ) ] );
      Assert( 5, IsCofibration( i ) );
      SetIsCofibration( i, true );
      
      Q_to_cyl_f := ProjectionInFactorOfFiberProduct( [ cyl_f_to_cone_f, P_to_cone_f ], 1 );
      
      ##
      j := PreCompose( Q_to_cyl_f, cyl_f_to_B );
      Assert( 5, IsFibration( j ) );
      Assert( 5, IsWeakEquivalence( j ) );
      SetIsFibration( j, true );
      SetIsWeakEquivalence( j, true );
      
      
      return [ i, j ];
      
      end );
      
    AddFactorThroughAcyclicCofibration( cat,
      function( f )
      local A, B, cocyl_f_to_B, A_to_cocyl_f, cocyl_f_to_M, P_to_M, P, i, R_to_cocyl_f, j, M;
      
      A := Source( f );
      
      B := Range( f );
      
      cocyl_f_to_B := NaturalMorphismFromMappingCocylinderToRange( f );
      
      A_to_cocyl_f := NaturalMorphismFromSourceInMappingCocylinder( f );
      
      cocyl_f_to_M := CokernelProjection( A_to_cocyl_f );
      
      M := CokernelObject( A_to_cocyl_f );
      
      P := ProjectiveResolutionWithBounds( M, 5000 );
      
      P_to_M := QuasiIsomorphismFromProjectiveResolution( M );
      
      ##
      i := UniversalMorphismIntoFiberProduct( [ cocyl_f_to_M, P_to_M ], [ A_to_cocyl_f, ZeroMorphism( A, P ) ] );
      Assert( 5, IsCofibration( i ) );
      Assert( 5, AddIsWeakEquivalence( i ) );
      SetIsWeakEquivalence( i, true );
      SetIsCofibration( i, true );

      R_to_cocyl_f := ProjectionInFactorOfFiberProduct( [ cocyl_f_to_M, P_to_M ], 1 );
      
      ##
      j := PreCompose( R_to_cocyl_f, cocyl_f_to_B );
      Assert( 5, IsFibration( j ) );
      #SetIsFibration( j, true );
      
      return [ i, j ];
      
      end );
      
 end );
