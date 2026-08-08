module Str_Literal(literalOfAsciis, asciisOfLiteral) where

check_ascii :: Int -> Int
check_ascii k
  | (0 <= k && k < 128) = k
  | otherwise = error "Non-ASCII character in literal"

charOfAscii :: Integer -> Char
charOfAscii = toEnum . Prelude.fromInteger . (\k -> k `mod ` 128)

asciiOfChar :: Char -> Integer
asciiOfChar = toInteger . check_ascii . fromEnum

literalOfAsciis :: [Integer] -> [Char]
literalOfAsciis = map charOfAscii

asciisOfLiteral :: [Char] -> [Integer]
asciisOfLiteral = map asciiOfChar

