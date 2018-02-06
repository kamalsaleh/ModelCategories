
Read( "/home/saleh/Documents/gap_packages/local/pkg/ModelCategories/examples/left_homotopy_in_complexes_of_l_p_over_comm_homalg_ring.g" );

LoadPackage( "ModulePresentations" );
LoadPackage( "ModelCategories" );

R := HomalgFieldOfRationalsInSingular()*"x,y,z";;
cat := LeftPresentations( R: FinalizeCategory := false );
AddEpimorphismFromSomeProjectiveObject( cat, CoverByFreeModule );
SetIsAbelianCategoryWithEnoughProjectives( cat, true );
AddIsProjective( cat, function( P ) 
                      return not Lift( IdentityMorphism( P ), CoverByFreeModule( P ) ) = fail;
                      end );
Finalize( cat );
chains := ChainComplexCategory( cat : FinalizeCategory := false );
ModelStructureOnChainComplexes( chains );
AddAreLeftHomotopic( chains, 
    function( phi, psi )
        return is_left_homotopic_to_null( phi - psi );
    end );
CapCategorySwitchLogicOff( chains );
Finalize( chains );


m := HomalgMatrix( "[ x,y,0,z,-x,y ]", 2, 3, R );
# <A 2 x 3 matrix over an external ring>
n := HomalgMatrix( "[ x+y,x-y,z,y,0,-x,0,z ]", 4, 2, R );
# <A 4 x 2 matrix over an external ring>
a := HomalgMatrix( "[ x+y,0,x+y,-x,-x-y-z,2x ]", 3, 2, R );
# <A 3 x 2 matrix over an external ring>
M := AsLeftPresentation( m );
# <An object in Category of left presentations of Q[x,y,z]>
N := AsLeftPresentation( n );
# <An object in Category of left presentations of Q[x,y,z]>
phi := PresentationMorphism( M, a, N );
# <A morphism in Category of left presentations of Q[x,y,z]>
M := StalkChainComplex( M, 1 );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
N := StalkChainComplex( N, 1 );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
phi := ChainMorphism( M, N, [ phi ], 1 );
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 2>
M_cofib := CofibrantModel( M );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
N_cofib := CofibrantModel( N );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 5>
phi_cofib := MorphismBetweenCofibrantModels( phi );
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
IsWellDefined( phi );
# true
phi_cofib := MorphismBetweenCofibrantModels( phi );
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
IsWellDefined( phi_cofib, 0, 10 );
# true
Display( phi_cofib, 0, 10 );
# In index 0
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 1
# 
# Morphism is
# x+y,   0, 
# x+y,   -x,
# -x-y-z,2*x
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 2
# 
# Morphism is
# -y,z,   x+y-z,-y, 
# -y,-x+z,x+y-z,-x-y
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 3
# 
# Morphism is
# (an empty 0 x 3 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 4
# 
# Morphism is
# (an empty 0 x 1 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 5
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 6
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 7
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 8
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 9
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 10
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
M_cofib := CofibrantModel( M );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
N_cofib := CofibrantModel( N );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 5>
phi_cofib;
# <A bounded morphism in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound 0 and active upper bound 3>
H := InternalHomOnObjects( M_cofib, N_cofib );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound -2 and active upper bound 4>
kernel_mor_of_H := CyclesAt( H, 0 );
# <A monomorphism in Category of left presentations of Q[x,y,z]>
kernel_obj_of_H := Source( kernel_mor_of_H );
# <An object in Category of left presentations of Q[x,y,z]>
homology_of_H := HomologyAt( H, 0 );
# <An object in Category of left presentations of Q[x,y,z]>
ker_to_homology := CokernelProjection( KernelLift( H^0, BoundariesAt( H, 0 ) ) );
# <An epimorphism in Category of left presentations of Q[x,y,z]>
IsEqualForObjects( homology_of_H, Range( ker_to_homology ) );
# true
NrColumns( UnderlyingMatrix( homology_of_H ) );
# 14
morphisms_from_R_to_homology := List( [ 1 .. 14 ], i-> StandardGeneratorMorphism( homology_of_H, i ) );;
List( morphisms_from_R_to_homology, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
morphisms_from_R_to_kernel := List( morphisms_from_R_to_homology, m -> ProjectiveLift( m, ker_to_homology ) );;
List( morphisms_from_R_to_kernel, IsZero );
# [ false, false, false, false, false, false, false, false, false, false, false, false, false, false ]
T := TensorUnit( chains );
# <A bounded object in chain complexes category over category of left presentations of Q[x,y,z] with active lower bound -1 and active upper bound 1>
morphisms_from_T_to_H := List( morphisms_from_R_to_kernel, m -> ChainMorphism( T, H, [ PreCompose( m, kernel_mor_of_H) ], 0 ) );;
List( morphisms_from_T_to_H, IsWellDefined );
# [ true, true, true, true, true, true, true, true, true, true, true, true, true, true ]
morphisms_between_M_cofib_N_cofib := List( morphisms_from_T_to_H, m-> InternalHomToTensorProductAdjunctionMap( M_cofib, N_cofib, m ) );;
morphisms_between_M_cofib_N_cofib_homotopy_cat := List( morphisms_between_M_cofib_N_cofib, AsMorphismInHomotopyCategory );;
List( morphisms_between_M_cofib_N_cofib, IsZero );
# [ false, false, false, false, false, false, false, false, false, false, false, false, false, false ]
List( morphisms_between_M_cofib_N_cofib_homotopy_cat, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
List( morphisms_from_R_to_homology, IsZero );
# [ false, false, true, false, false, false, true, false, true, false, true, true, true, false ]
Display( morphisms_between_M_cofib_N_cofib[ 10 ], 0, 5 );
# In index 0
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, split epimorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 1
# 
# Morphism is
# z,0, 
# z,-z,
# z,0  
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 2
# 
# Morphism is
# 0,-z, z, 0,    
# 0,2*x,-z,-2*y-z
# 
# A morphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 3
# 
# Morphism is
# (an empty 0 x 3 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 4
# 
# Morphism is
# (an empty 0 x 1 matrix)
# 
# A zero, split monomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
# In index 5
# 
# Morphism is
# (an empty 0 x 0 matrix)
# 
# A zero, isomorphism in Category of left presentations of Q[x,y,z]
# 
# -----------------------------------------------------------------
#