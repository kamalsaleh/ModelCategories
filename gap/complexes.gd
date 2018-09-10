
# DeclareOperation( "AssociatedExactTriangleOfShortExactSequence", [ IsChainMorphism, IsChainMorphism ] );
# InstallMethod( AssociatedExactTriangleOfShortExactSequence,
# 	[ IsChainMorphism, IsChainMorphism ],
# 	function( phi, psi )
# 	local
# 	if not IsMonomorphism( phi ) or not IsEpimorphism( psi ) then
# 		Error( "" );
# 	fi;
	
# 	h_phi := AsMorphismInHomotopyCategory( phi );
# 	h_psi := AsMorphismInHomotopyCategory( psi );
# 	rep_phi := UnderlyingReplacement( h_phi );
# 	rep_psi := UnderlyingReplacement( h_psi );
	
# 	tr_h_phi := CompleteMorphismToStandardExactTriangle( h_phi );

# 	cone := tr_h_phi[ 2 ];
# 	rep_cone := UnderlyingReplacement( cone );

# 	A := Source( rep_phi );
# 	B := Range( rep_phi );
# 	C := Range( rep_psi );
	
# 	morphisms := MapLazy( IntegersList, n -> MorphismBetweenDirectSums( [ [ ZeroMorphism( A[ n-1 ], B[ n ] ) ], 
# 									      [ IdentityMorphism( B[ n ] )       ]  ] 
# 									  ), 1
# 			    );

# 	mor := ChainMorphism( rep_cone, B, morphisms );
# 	mor := AsMorphismInHomotopyCategory( PreCompose( mor, rep_psi ) );
	
	
# 	return CreateExactTriangle( h_phi, h_psi, PreCompose( Inverse( mor ), tr_h_phi^2 ) ); 
	
# end );
