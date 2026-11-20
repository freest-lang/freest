-- Convert a bio-impedance scale report into a single comma-separated line.
--
--   P. consulta: 10/9 - 16.30h
--
--   PESO (KG) - 73.9  kg
--   M.GORDA (KG) - (21%) = 15.5  kg
--   MM - 55.7  kg
--   M. HÍDRICA (KG)-  (55.7%) = 41.2  kg
--   M. ÓSSEA (KG) - 3.0  kg
--   IDADE METAB. (ANOS)- 61
--   GORD. VISCERAL (GRAU)- 11.5
--   MET. BASAL (KCAL)-  1639  kcal
--
-- becomes
--
--   2026/9/10,16:30,73.9,15.5,55.7,41.2,3.0,61,11.5,1639
--
-- Code of the convert function by Clause

-- The consultation's year isn't in the report; assumed to be the current one.
year : String
year = "2026"

eqChar : Char -> Char -> Bool
eqChar c1 c2 = ord c1 == ord c2

containsChar : Char -> String -> Bool
containsChar _ []        = False
containsChar c (x :: xs) = eqChar c x || containsChar c xs

isDigitChar : Char -> Bool
isDigitChar c = ord c >= ord '0' && ord c <= ord '9'

isNumChar : Char -> Bool
isNumChar '.' = True
isNumChar c   = isDigitChar c

isNumber : String -> Bool
isNumber []        = False
isNumber (c :: cs) = isNumChar c && allNumChars cs
  where
    allNumChars : String -> Bool
    allNumChars []        = True
    allNumChars (x :: xs) = isNumChar x && allNumChars xs

-- The first element satisfying a predicate.
firstMatching : forall (a : *T) -> (a -> Bool) -> [a] -> a
firstMatching _ []        = error "firstMatching: no match"
firstMatching p (x :: xs)
  | p x       = x
  | otherwise = firstMatching p xs

-- Split a string at the first occurrence of a separator character, dropping
-- the separator itself.
splitOnChar : Char -> String -> (String, String)
splitOnChar c s = (before, dropSep after)
  where
    (before, after)   = span (\x -> not (eqChar c x)) s
    dropSep : String -> String
    dropSep (_ :: xs) = xs
    dropSep []        = []

-- Keep only the numeric-looking words.
numericWords : [String] -> [String]
numericWords []        = []
numericWords (w :: ws)
  | isNumber w = w :: numericWords ws
  | otherwise  =      numericWords ws

-- The value at the end of a measurement line, e.g.
--   "PESO (KG) - 73.9  kg"                  -> "73.9"
--   "M. HÍDRICA (KG)-  (55.7%) = 41.2  kg"  -> "41.2"
extractValue : String -> String
extractValue line = last (numericWords (words line))

-- A line worth including in the CSV: not blank.
isDataLine : String -> Bool
isDataLine line = not (null (words line))

filterDataLines : [String] -> [String]
filterDataLines []        = []
filterDataLines (l :: ls)
  | isDataLine l = l :: filterDataLines ls
  | otherwise    =      filterDataLines ls

notNewline : Char -> Bool
notNewline '\n' = False
notNewline _    = True

-- Split a string into its lines (on '\n').
splitLines : String -> [String]
splitLines s =
  case span notNewline s of
    (line, [])        -> [line]
    (line, _ :: rest) -> line :: splitLines rest

-- Parse "P. consulta: <day>/<month> - <hour>.<minute>h" into
-- ["<year>/<month>/<day>", "<hour>:<minute>"].
parseHeader : String -> [String]
parseHeader line =
  [year ++ "/" ++ month ++ "/" ++ day, hour ++ ":" ++ minute]
  where
    ws           = words line
    dateW        = firstMatching (containsChar '/') ws
    timeW        = firstMatching (containsChar 'h')  ws
    (day, month) = splitOnChar '/' dateW
    (hour, rest) = splitOnChar '.' timeW
    minute       = takeWhile isDigitChar rest

-- Convert a bio-impedance scale report into a single comma-separated line.
convert : String -> String
convert text =
  case splitLines text of
    (header :: rest) ->
      intercalate "," (parseHeader header ++ map extractValue (filterDataLines rest))

-- main and testing

-- Convert a bio-impedance report file into a CSV line.
convertFile : FilePath -> String
convertFile = convert . readFile

appendBioImpedance : () -> ()
appendBioImpedance () =
  let [csvFile, dataFile] = getArgs ()
      line = convertFile dataFile in
    appendFile csvFile (line ++ "\n")

test =
    let csv  = readFile "test/prog/Valid/IO/Bioimpedance/bioImpedance.csv"
        line = convertFile "test/prog/Valid/IO/Bioimpedance/2026-09-10.txt"
    in putStrLn $ csv ++ line

report : String
report =
  "P. consulta: 10/9 - 16.30h\n" ++
  "\n" ++
  "PESO (KG) - 73.9  kg\n" ++
  "M.GORDA (KG) - (21%) = 15.5  kg\n" ++
  "MM - 55.7  kg\n" ++
  "M. HÍDRICA (KG)-  (55.7%) = 41.2  kg\n" ++
  "M. ÓSSEA (KG) - 3.0  kg\n" ++
  "IDADE METAB. (ANOS)- 61\n" ++
  "GORD. VISCERAL (GRAU)- 11.5\n" ++
  "MET. BASAL (KCAL)-  1639  kcal"

-- _ = putStrLn $ convert report
-- expected: 2026/9/10,16:30,73.9,15.5,55.7,41.2,3.0,61,11.5,1639
