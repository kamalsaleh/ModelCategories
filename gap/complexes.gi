

BindGlobal( "ModelStructureOnChainComplexes",
 function( cat )
 
 AddIsWeakEquivalence( cat, 
    function( phi )
      return IsQuasiIsomorphism( phi );
    end );
 
 AddIsCofibration( cat, 
    function( phi )
    local i;
    
      if not HasActiveUpperBound( phi ) then 
         Error( "the morphism must have an upper bound" );
      fi;
      
      for i in [ 0 .. ActiveUpperBound( phi ) ] do 
      
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
     local i;
     
        if not HasActiveUpperBound( phi ) then
           Error( "The morphism must have an upper bound" );
        fi;
        
        for i in [ 1 .. ActiveUpperBound( phi ) ] do 
        
            if not IsEpimorphism( phi[ i ] ) then 
            
               return false;
               
            fi;
            
        od;
        
        return true;
        
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
        
        X := Source( g );
        
        P := CokernelObject( f );
        
        splitting_morphism := ProjectiveLift( IdentityMorphism( P ), CokernelProjection( f ) );
        
        direct_sum_to_B := UniversalMorphismFromDirectSum( [ A, P ], [ f, splitting_morphism ] );
        
        B_to_direct_sum := Inverse( direct_sum_to_B );
        
        direct_sum_to_X := MorphismBetweenDirectSums( [ [ u ], [ ProjectiveLift( PreCompose( splitting_morphism, v ), g ) ] ] );
        
        return PreCompose( B_to_direct_sum, direct_sum_to_X );
    fi;
    
    Error( "The first argument should be an acyclic cofibration the second a fibration or the first is cofibration and the second is acyclic fibration" );
    
    end );
  
 end );
