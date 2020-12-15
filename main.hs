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
c = normalizeNodes (b)
d = reduce c
(AFD vocab nodes initial delta terminals) = b
(AFD vocab' nodes' initial' delta' terminals') = c
(AFD vocab'' nodes'' initial'' delta'' terminals'') = d
