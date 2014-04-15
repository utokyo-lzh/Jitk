
type Port = Int

data Loc = Loc Int | Reject
    deriving (Eq, Ord, Show)

data Instruction
    = Nop
    | Jmp Loc 
    | Sge Port Loc
    | Sle Port Loc
    | Dge Port Loc
    | Dle Port Loc
    | Scond HostCond Loc
    | Dcond HostCond Loc
    deriving (Eq, Ord, Show)

type Program = [Instruction]

-- TODO fix the types for addr,prefixlen,family,userlocks
data HostCond = HostCond
    { hcFamily :: Int
    , hcPrefixLen :: Int
    , hcPort :: Port
    , hcAddr :: Int
    } deriving (Eq, Ord, Show)

data Entry = Entry
    { saddr :: Int
    , daddr :: Int
    , sport :: Port
    , dport :: Port
    , family :: Int
    , userlocks :: Int
    } deriving (Eq, Ord, Show)


eval :: Program -> Entry -> Bool
eval [] _ = True
eval (Nop : pgm) e = eval pgm e
eval (Jmp loc : pgm) e = jmp loc pgm e
eval (Sge port loc : pgm) e
    | sport e >= port = eval pgm e
    | otherwise = jmp loc pgm e
eval (Sle port loc : pgm) e
    | sport e <= port = eval pgm e
    | otherwise = jmp loc pgm e
eval (Dge port loc : pgm) e
    | dport e >= port = eval pgm e
    | otherwise = jmp loc pgm e
eval (Dle port loc : pgm) e
    | dport e <= port = eval pgm e
    | otherwise = jmp loc pgm e
eval (Scond hc loc : pgm) e
    | checkhc hc sport saddr e = eval pgm e
    | otherwise = jmp loc pgm e
eval (Dcond hc loc : pgm) e
    | checkhc hc dport daddr e = eval pgm e
    | otherwise = jmp loc pgm e

jmp :: Loc -> Program -> Entry -> Bool
jmp Reject _ _ = False
jmp (Loc x) p e = eval (drop x p) e

checkhc = error "checkhc: TODO"

-- ss 'sport >= :21 and sport < :1024'
-- from apsys paper
exampleProgram =
    [ Sge 21 Reject
    , Sge 1024 (Loc 1)
    , Jmp Reject
    , Nop
    ]

emptyEntry = Entry 0 0 0 0 0 0
test port = eval exampleProgram (emptyEntry { sport = port })

tests = map (\x -> (x, test x)) [20,21,22,80,1023,1024,1025]
