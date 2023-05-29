{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module ProSys where

import Data.Profunctor
import Data.Profunctor.Adjunction
import Data.Profunctor.Cayley
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Composition
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Ran
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Types
import Data.Profunctor.Yoneda

-- | not profunctor Codensity
data ProSys p a b where
  ProSysFree :: p a b -> ProSys p a b
  SysCopastro :: Copastro (ProSys p) a b -> ProSys p a b
  SysCotambara :: Cotambara (ProSys p) a b -> ProSys p a b
  SysPastro :: Pastro (ProSys p) a b -> ProSys p a b
  SysTambara :: Tambara (ProSys p) a b -> ProSys p a b
  SysEnvironment :: Environment (ProSys p) a b -> ProSys p a b
  SysClosure :: Closure (ProSys p) a b -> ProSys p a b
  SysCopastroSum :: CopastroSum (ProSys p) a b -> ProSys p a b
  SysCotambaraSum :: CotambaraSum (ProSys p) a b -> ProSys p a b
  SysPastroSum :: PastroSum (ProSys p) a b -> ProSys p a b
  SysTambaraSum :: TambaraSum (ProSys p) a b -> ProSys p a b
  SysFreeTraversing :: FreeTraversing (ProSys p) a b -> ProSys p a b
  SysCofreeTraversing :: CofreeTraversing (ProSys p) a b -> ProSys p a b
  SysFreeMapping :: FreeMapping (ProSys p) a b -> ProSys p a b
  SysCofreeMapping :: CofreeMapping (ProSys p) a b -> ProSys p a b
  SysCoyoneda :: Coyoneda (ProSys p) a b -> ProSys p a b
  SysYoneda :: Yoneda (ProSys p) a b -> ProSys p a b
  SysCodensity :: Codensity (ProSys p) a b -> ProSys p a b
  SysRift :: Rift (ProSys p) (ProSys p) a b -> ProSys p a b
  SysProcompose :: Procompose (ProSys p) (ProSys p) a b -> ProSys p a b
  SysRan :: Ran (ProSys p) (ProSys p) a b -> ProSys p a b -- 21

instance Profunctor p => Profunctor (ProSys p) where
  dimap fl fr (ProSysFree p) = ProSysFree $ dimap fl fr p
  dimap fl fr (SysCopastro p) = SysCopastro $ dimap fl fr p
  dimap fl fr (SysCotambara p) = SysCotambara $ dimap fl fr p
  dimap fl fr (SysPastro p) = SysPastro $ dimap fl fr p
  dimap fl fr (SysTambara p) = SysTambara $ dimap fl fr p
  dimap fl fr (SysEnvironment p) = SysEnvironment $ dimap fl fr p
  dimap fl fr (SysClosure p) = SysClosure $ dimap fl fr p
  dimap fl fr (SysCopastroSum p) = SysCopastroSum $ dimap fl fr p
  dimap fl fr (SysCotambaraSum p) = SysCotambaraSum $ dimap fl fr p
  dimap fl fr (SysPastroSum p) = SysPastroSum $ dimap fl fr p
  dimap fl fr (SysTambaraSum p) = SysTambaraSum $ dimap fl fr p
  dimap fl fr (SysFreeTraversing p) = SysFreeTraversing $ dimap fl fr p
  dimap fl fr (SysCofreeTraversing p) = SysCofreeTraversing $ dimap fl fr p
  dimap fl fr (SysFreeMapping p) = SysFreeMapping $ dimap fl fr p
  dimap fl fr (SysCofreeMapping p) = SysCofreeMapping $ dimap fl fr p
  dimap fl fr (SysCoyoneda p) = SysCoyoneda $ dimap fl fr p
  dimap fl fr (SysYoneda p) = SysYoneda $ dimap fl fr p
  dimap fl fr (SysCodensity p) = SysCodensity $ dimap fl fr p
  dimap fl fr (SysRift p) = SysRift $ dimap fl fr p
  dimap fl fr (SysProcompose p) = SysProcompose $ dimap fl fr p
  dimap fl fr (SysRan p) = SysRan $ dimap fl fr p

data RunProSys q p = RunProSys
  { srunProSysFree :: q :-> p,
    srunCopastro :: Copastro p :-> p,
    srunCotambara :: Cotambara p :-> p,
    srunPastro :: Pastro p :-> p,
    srunTambara :: Tambara p :-> p,
    srunEnvironment :: Environment p :-> p,
    srunClosure :: Closure p :-> p,
    srunCopastroSum :: CopastroSum p :-> p,
    srunCotambaraSum :: CotambaraSum p :-> p,
    srunPastroSum :: PastroSum p :-> p,
    srunTambaraSum :: TambaraSum p :-> p,
    srunFreeTraversing :: FreeTraversing p :-> p,
    srunCofreeTraversing :: CofreeTraversing p :-> p,
    srunFreeMapping :: FreeMapping p :-> p,
    srunCofreeMapping :: CofreeMapping p :-> p,
    srunCoyoneda :: Coyoneda p :-> p,
    srunYoneda :: Yoneda p :-> p,
    srunCodensity :: Codensity (ProSys q) :-> p,
    srunRift :: Rift (ProSys q) p :-> p,
    srunProcompose :: Procompose p p :-> p,
    srunRan :: Ran (ProSys q) p :-> p
  }

runProSys :: Profunctor q => RunProSys q p -> ProSys q a b -> p a b
runProSys rps (ProSysFree p) = (srunProSysFree rps) p
runProSys rps (SysCopastro p) = (srunCopastro rps) $ promap (runProSys rps) p
runProSys rps (SysCotambara p) = (srunCotambara rps) $ promap (runProSys rps) p
runProSys rps (SysPastro p) = (srunPastro rps) $ promap (runProSys rps) p
runProSys rps (SysTambara p) = (srunTambara rps) $ promap (runProSys rps) p
runProSys rps (SysEnvironment p) = (srunEnvironment rps) $ promap (runProSys rps) p
runProSys rps (SysClosure p) = (srunClosure rps) $ promap (runProSys rps) p
runProSys rps (SysCopastroSum p) = (srunCopastroSum rps) $ promap (runProSys rps) p
runProSys rps (SysCotambaraSum p) = (srunCotambaraSum rps) $ promap (runProSys rps) p
runProSys rps (SysPastroSum p) = (srunPastroSum rps) $ promap (runProSys rps) p
runProSys rps (SysTambaraSum p) = (srunTambaraSum rps) $ promap (runProSys rps) p
runProSys rps (SysFreeTraversing p) = (srunFreeTraversing rps) $ promap (runProSys rps) p
runProSys rps (SysCofreeTraversing p) = (srunCofreeTraversing rps) $ promap (runProSys rps) p
runProSys rps (SysFreeMapping p) = (srunFreeMapping rps) $ promap (runProSys rps) p
runProSys rps (SysCofreeMapping p) = (srunCofreeMapping rps) $ promap (runProSys rps) p
runProSys rps (SysCoyoneda p) = (srunCoyoneda rps) $ promap (runProSys rps) p
runProSys rps (SysYoneda p) = (srunYoneda rps) $ promap (runProSys rps) p
runProSys rps (SysCodensity p) = (srunCodensity rps) p
runProSys rps (SysRift p) = (srunRift rps) $ promap (runProSys rps) p
runProSys rps (SysProcompose (Procompose p2 p1)) = (srunProcompose rps) $ Procompose (runProSys rps p2) (runProSys rps p1)
runProSys rps (SysRan p) = (srunRan rps) $ promap (runProSys rps) p
