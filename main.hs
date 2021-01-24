import Automata

deltax :: Char -> Status -> [Status]
deltax 'a' (Q 0) = [Q 1]
deltax 'a' (Q 1) = [Q 1]
deltax 'b' (Q 1) = [Q 1]
deltax 'a' (Q 2) = [Q 2]
deltax 'b' (Q 2) = [Q 2, Q 3]
deltax _ _ = []


epsilon :: Status -> [Status]
epsilon (Q 100) = [Q 0, Q 2]
epsilon _ = []

a = AFNe "ab" [Q 100, Q 0, Q 1, Q 2, Q 3] (Q 100) deltax [Q 1, Q 3] epsilon
b = afnToafd (afneToafn a)
c = reduce b
d = normalizeNodes c
(AFD vocab nodes initial delta terminals) = b
(AFD vocab' nodes' initial' delta' terminals') = c
(AFD vocab'' nodes'' initial'' delta'' terminals'') = d

vocab1 = "ab"
nodes1 = [Q 0, Q 1, Trash]
initial1 = Q 0
terminals1 = [Q 1]

delta1 :: Char -> Status -> Status
delta1 'a' (Q 0) = Q 1
delta1 'a' (Q 1) = Q 1
delta1 _ _ = Trash

delta2 :: Char -> Status -> Status
delta2 'b' (Q 0) = Q 1
delta2 'b' (Q 1) = Q 1
delta2 _ _ = Trash

soloa = AFD vocab1 nodes1 initial1 delta1 terminals1
solob = AFD vocab1 nodes1 initial1 delta2 terminals1

orab = orAFD soloa solob

andab = andAFD soloa solob


-- Suma OR
cualquiera = 'a' |+| 'b'

-- Cierre *
todapalabra = (|^|) cualquiera

-- Concatenación *
terminaEnA :: Regex
terminaEnA = todapalabra |++| (RexChar 'a')

-- AFNe correspondiente
afne = regToAFNe terminaEnA
afn = afneToafn afne

afd = afnToafd afn

afd2 = normalizeNodes $ reduce afd