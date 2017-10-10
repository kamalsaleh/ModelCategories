

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

##
AddDerivationToCAP( FibrantModel, 
            [ [ IsFibrant, 1 ], [ FactorThroughAcyclicCofibration, 1 ] ], 
            
    function( obj )
    local u;
    
    if IsFibrant( obj ) then
         
        return obj;
        
        SetAcyclicCofibrationIntoFibrantModel( IdentityMorphism( obj ) );
    
    else
      
        u := UniversalMorphismIntoTerminalObject( obj );
         
        u := FactorThroughAcyclicCofibration( u )[ 1 ];
         
        SetAcyclicCofibrationIntoFibrantModel( obj, u );
         
        Assert( 5, IsFibrant( Range( u ) ) );
        SetIsFibrant( Range( u ), true );
        
        return Range( u );
         
    fi;

end : Description := "constructs a fibrant model for the given obj" );

##
AddDerivationToCAP( AcyclicCofibrationIntoFibrantModel, 
            [ [ IsFibrant, 1 ], [ FactorThroughAcyclicCofibration, 1 ] ], 
            
    function( obj )
    local u;
    
    if IsFibrant( obj ) then
         
        SetFibrantModel( obj, obj );
         
        return IdentityMorphism( obj );
    
    else
      
        u := UniversalMorphismIntoTerminalObject( obj );
         
        u := FactorThroughAcyclicCofibration( u )[ 1 ];
        
        Assert( 5, IsFibrant( Range( u ) ) );
        SetFibrantModel( obj, Range( u ) );
        
        return u;
         
    fi;

end : Description := "constructs an acyclic cofibration into a fibrant model for the given obj" );

##
AddDerivationToCAP( CofibrantModel, 
            [ [ IsCofibrant, 1 ], [ FactorThroughAcyclicFibration, 1 ] ], 
            
    function( obj )
    local u;
    
    if IsCofibrant( obj ) then
         
        return obj;
        
        SetAcyclicFibrationFromCofibrantModel( IdentityMorphism( obj ) );
    
    else
      
        u := UniversalMorphismFromInitialObject( obj );
         
        u := FactorThroughAcyclicFibration( u )[ 2 ];
         
        SetAcyclicFibrationFromCofibrantModel( obj, u );
        
        Assert( 5, IsCofibrant( Source( u ) ) );
        SetIsCofibrant( Source( u ), true );
        
        return Source( u );
         
    fi;

end : Description := "constructs a cofibrant model for the given obj" );

##
AddDerivationToCAP( AcyclicFibrationFromCofibrantModel, 
            [ [ IsCofibrant, 1 ], [ FactorThroughAcyclicFibration, 1 ] ], 
            
    function( obj )
    local u;
    
    if IsCofibrant( obj ) then
         
        SetCofibrantModel( obj, obj );
         
        return IdentityMorphism( obj );
    
    else
      
        u := UniversalMorphismFromInitialObject( obj );
         
        u := FactorThroughAcyclicFibration( u )[ 2 ];
        
        Assert( 5, IsCofibrant( Source( u ) ) );
        SetCofibrantModel( obj, Source( u ) );
         
        return u;
         
    fi;

end : Description := "constructs an acyclic fibration from a cofibrant model for the given obj" );
