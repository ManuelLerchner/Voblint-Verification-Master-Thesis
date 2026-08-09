{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Analyse(Analysis_kind(..), Abstract_value(..), analyse, analyse_with_state)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Str_Literal;
import qualified Core;
import qualified Interval;
import qualified Sign;

data Analysis_kind = Sign_Analysis | Interval_Analysis;

data Abstract_value = SignValue Sign.Sign | IntervalValue Interval.Ivl;

analyse ::
  Analysis_kind ->
    Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
analyse Sign_Analysis p = Sign.analyse_sign_report p;
analyse Interval_Analysis p = Interval.analyse_interval_td_report p;

analyse_with_state ::
  Analysis_kind ->
    Core.Imp_prog_ext () ->
      [(Core.Cfg_node,
         (Core.Bexp, (Core.Check_result, String -> Abstract_value)))];
analyse_with_state Sign_Analysis p =
  map (\ (u, (c, (r, s))) -> (u, (c, (r, SignValue . s))))
    (Sign.analyse_sign_report_with_state p);
analyse_with_state Interval_Analysis p =
  map (\ (u, (c, (r, s))) -> (u, (c, (r, IntervalValue . s))))
    (Interval.analyse_interval_td_report_with_state p);

}
