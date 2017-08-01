

##
AddDerivationToCAP( ProjectiveLift, 
            [ [ Lift, 1 ] ], 
            
      function( alpha, beta )
      
      return Lift( alpha, beta );
      
end : Description := "projective lift from lift" );


##
AddDerivationToCAP( IsAcyclicFibration, 
            [ [ IsFibration, 1 ], [ IsWeakEquivalence, 1 ] ], 
            
      function( phi )
      
      if HasIsWeakEquivalence( phi ) then 
      
         return IsWeakEquivalence( phi ) and IsFibration( phi );
      
      fi;
      
      return IsFibration( phi ) and IsWeakEquivalence( phi );
      
end : Description := "checks if a morphism is acyclic fibration" );

##
AddDerivationToCAP( IsAcyclicCofibration, 
            [ [ IsCofibration, 1 ], [ IsWeakEquivalence, 1 ] ], 
            
      function( phi )
      
      if HasIsWeakEquivalence( phi ) then 
      
         return IsWeakEquivalence( phi ) and IsCofibration( phi );
      
      fi;
      
      return IsCofibration( phi ) and IsWeakEquivalence( phi );
      
end : Description := "checks if a morphism is acyclic cofibration" );

##
AddDerivationToCAP( IsFibrant, 
            [ [ IsFibration, 1 ] ], 
            
      function( obj )
      
      return IsFibration( UniversalMorphismIntoTerminalObject( obj ) );
      
end : Description := "checks if an object is fibrant" );

##
AddDerivationToCAP( IsCofibrant, 
            [ [ IsCofibration, 1 ] ], 
            
      function( obj )
      
      return IsCofibration( UniversalMorphismFromInitialObject( obj ) );
      
end : Description := "checks if an object is cofibrant" );

##
AddDerivationToCAP( IsFibrantAndCofibrant, 
            [ [ IsFibrant, 1 ], [ IsCofibrant, 1 ] ], 
            
      function( obj )
      
      if HasIsFibrant( obj ) then
      
         return IsFibrant( obj ) and IsCofibrant( obj );
      fi;
      
      return IsCofibrant( obj ) and IsFibrant( obj );
      
end : Description := "checks if an object is both fibrant and cofibrant" );

