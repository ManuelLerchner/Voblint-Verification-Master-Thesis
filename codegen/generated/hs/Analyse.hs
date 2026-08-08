{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Analyse(Analysis_kind(..), analyse) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Str_Literal;
import qualified Interval;
import qualified Sign;
import qualified Core;

data Analysis_kind = Sign_Analysis | Interval_Analysis;

analyse ::
  Analysis_kind ->
    Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
analyse Sign_Analysis p = Sign.analyse_sign_report p;
analyse Interval_Analysis p = Interval.analyse_interval_td_report p;

}
