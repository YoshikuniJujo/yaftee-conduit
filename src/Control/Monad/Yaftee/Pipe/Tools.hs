{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE BlockArguments, LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wall -fno-warn-tabs #-}

module Control.Monad.Yaftee.Pipe.Tools (

	-- * CONVERT

	convert, convert', convert'',

	-- * FILTER

	filter, filter',

	-- * EITHER

	checkRight, skipLeft1,

	-- * LENGTH

	lengthRun, length, Length,

	-- * SCAN

	scanl,

	-- * Devide

	devideRun, devide, devideNs, Devide

	) where

import Prelude hiding (length, filter, scanl)
import Prelude qualified as P
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Yaftee.Eff qualified as Eff
import Control.Monad.Yaftee.Pipe qualified as Pipe
import Control.Monad.Yaftee.State qualified as State
import Control.Monad.Yaftee.Except qualified as Except
import Control.HigherOpenUnion qualified as U
import Data.HigherFunctor qualified as HFunctor
import Data.Bits
import Data.Bool

convert :: U.Member Pipe.P effs => (a -> b) -> Eff.E effs a b r
convert f = fix \go -> Pipe.await >>= ((>> go) . Pipe.yield . f)

convert' :: U.Member Pipe.P effs => (a -> b) -> Eff.E effs a b ()
convert' f = fix \go -> Pipe.isMore
	>>= bool (pure ()) (Pipe.await >>= ((>> go) . Pipe.yield . f))

convert'' :: U.Member Pipe.P es => (Bool -> a -> b) -> a -> Eff.E es a b ()
convert'' f = fix \go p -> Pipe.isMore >>= bool
	(Pipe.yield (f True p))
	(Pipe.await >>= \x -> ((>> go x) . Pipe.yield $ f False p))

filter :: U.Member Pipe.P es => (a -> Maybe b) -> Eff.E es a b r
filter f = fix \go -> Pipe.await >>= \x -> case f x of
	Nothing -> go
	Just y -> Pipe.yield y >> go

filter' :: U.Member Pipe.P es => (a -> Maybe b) -> Eff.E es a b ()
filter' f = fix \go -> Pipe.isMore
	>>= bool (pure ()) (Pipe.await >>= \x -> case f x of
		Nothing -> go
		Just y -> Pipe.yield y >> go)

checkRight :: (U.Member Pipe.P es, U.Member (Except.E String) es) =>
	Eff.E es (Either a b) b r
checkRight = fix \go -> Pipe.await >>= (>> go)
	. either (const $ Except.throw "(Left _) exist") (Pipe.yield)

skipLeft1 :: (U.Member Pipe.P es, U.Member (Except.E String) es) =>
	Eff.E es (Either a b) o b
skipLeft1 = Pipe.await >>= \case
	Left _ -> Pipe.await >>= \case
		Left _ -> Except.throw @String "Not Right"
		Right x -> pure x
	Right x -> pure x

lengthRun :: forall nm es i o a . HFunctor.Loose (U.U es) =>
	Eff.E (State.Named nm Length ': es) i o a -> Eff.E es i o (a, Length)
lengthRun = (`State.runN` (0 :: Length))

length :: forall nm -> (
	Foldable t,
	U.Member Pipe.P es, U.Member (State.Named nm Length) es ) =>
	Eff.E es (t a) (t a) r
length nm = forever $ Pipe.await >>= \s ->
	State.modifyN nm (+ Length (P.length s)) >> Pipe.yield s

newtype Length = Length { unLength :: Int }
	deriving (Show, Eq, Bits, FiniteBits, Ord, Enum, Num, Real, Integral)

scanl :: U.Member Pipe.P es => (b -> a -> b) -> b -> Eff.E es a b r
scanl op =
	fix \go v -> (v `op`) <$>  Pipe.await >>= \v' -> Pipe.yield v' >> go v'

devideRun :: forall nm m es i o r . (P.Monoid m, HFunctor.Loose (U.U es)) =>
	Eff.E (State.Named nm (Devide m) ': es) i o r ->
	Eff.E es i o (r, Devide m)
devideRun = flip (State.runN @nm) (Devide mempty)

devideNs :: forall nm -> (
	Semigroup m,
	U.Member Pipe.P es, U.Member (State.Named nm (Devide m)) es ) =>
	(Int -> m -> Maybe (m, m)) -> m -> [Int] -> Eff.E es m m ()
devideNs nm sp bs0 ns0 = do
	State.putN nm $ Devide bs0
	($ ns0) $ fix \go -> \case
		[] -> pure ()
		n : ns -> do
			Pipe.yield =<< getInput nm sp n
			go ns

devide :: forall nm -> (
	Eq m, P.Monoid m,
	U.Member Pipe.P es, U.Member (State.Named nm (Devide m)) es ) =>
	(Int -> m -> Maybe (m, m)) -> m -> Int -> Eff.E es m m ()
devide nm sp bs0 n = do
	State.putN nm $ Devide bs0
	fix \go -> do
		bs <- getInput' nm sp n
		if bs == mempty then pure () else Pipe.yield bs >> go

getInput' :: forall m es o . forall nm -> (
	P.Monoid m,
	U.Member Pipe.P es, U.Member (State.Named nm (Devide m)) es ) =>
	(Int -> m -> Maybe (m, m)) -> Int -> Eff.E es m o m
getInput' nm sp n = State.getN nm >>= \(Devide bs) -> case sp n bs of
	Nothing -> readMore' nm >>= bool
		(unDevide <$> (State.getN nm <* State.putN @(Devide m) nm (Devide mempty)))
		(getInput' nm sp n)
	Just (t, d) -> t <$ State.putN nm (Devide d)

readMore' :: forall nm -> (
	Semigroup mono, U.Member Pipe.P es,
	U.Member (State.Named nm (Devide mono)) es ) =>
	Eff.E es mono o Bool
readMore' nm = Pipe.awaitMaybe >>= \case
	Nothing -> pure False
	Just xs -> True <$ State.modifyN nm (Devide . (<> xs) . unDevide)

getInput :: forall nm -> (
	Semigroup m,
	U.Member Pipe.P es, U.Member (State.Named nm (Devide m)) es ) =>
	(Int -> m -> Maybe (m, m)) -> Int -> Eff.E es m o m
getInput nm sp n = State.getN nm >>= \(Devide bs) -> case sp n bs of
	Nothing -> readMore nm >> getInput nm sp n
	Just (t, d) -> t <$ State.putN nm (Devide d)

readMore :: forall nm -> (
	Semigroup mono, U.Member Pipe.P es,
	U.Member (State.Named nm (Devide mono)) es ) =>
	Eff.E es mono o ()
readMore nm =
	Pipe.await >>= \xs -> State.modifyN nm (Devide . (<> xs) . unDevide)

newtype Devide m = Devide { unDevide :: m } deriving Show
